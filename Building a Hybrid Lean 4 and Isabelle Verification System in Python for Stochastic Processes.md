# Building a hybrid Lean 4 + Isabelle verification system in Python

**A Python-orchestrated system using both Lean 4 and Isabelle/HOL for stochastic processes verification is feasible today, and the two proof assistants are strikingly complementary.** Lean 4 has formalized discrete-time martingales, optional stopping, and Brownian motion construction, while Isabelle has the Central Limit Theorem, Markov chains, and ergodic theory — but neither system has stochastic calculus (Itô integral, SDEs, Girsanov). Practical Python tooling now exists for both backends: `lean-interact` and `isabelle-client` are pip-installable and actively maintained. No existing thesis or system combines Lean and Isabelle for the same mathematical domain, making this a genuinely novel contribution.

---

## Python ↔ Lean 4: five tools that actually work

The Lean 4 ecosystem has matured rapidly. Six Python integration tools exist; one is deprecated (lean-client-python, Lean 3 only). Here are the five that work, ranked by ease of setup for a beginner:

**LeanInteract** is the recommended starting point. Created at EPFL in 2025, it wraps the official Lean REPL with zero project setup required. Install with `pip install lean-interact`, then:

```python
from lean_interact import LeanREPLConfig, LeanServer, Command

config = LeanREPLConfig(verbose=True)  # auto-downloads Lean REPL
server = LeanServer(config)
response = server.run(Command(
    cmd='theorem ex (n : Nat) : n + n = 2 * n := by omega'
))
```

For Mathlib access (needed for measure theory), LeanInteract creates temporary projects automatically with `TemporaryProject`. It supports **v4.8.0-rc1 through v4.28.0-rc1**, has crash recovery via `AutoLeanServer`, and handles parallel processing. Current version is **0.11.0** on PyPI.

**LeanDojo** (749 GitHub stars, PyPI version 4.20.0, last updated December 2025) provides a gym-like "Dojo" environment for step-by-step tactic execution. It requires tracing a Git repository before interaction, making it heavier than LeanInteract but more powerful for proof search:

```python
from lean_dojo import LeanGitRepo, Theorem, Dojo

repo = LeanGitRepo("https://github.com/yangky11/lean4-example", "7b6ecb9...")
theorem = Theorem(repo, "Lean4Example.lean", "hello_world")
with Dojo(theorem) as (dojo, init_state):
    result = dojo.run_tac(init_state, "rw [add_assoc, add_comm b, ←add_assoc]")
```

**Pantograph/PyPantograph** (published at TACAS 2025, now mirrored under the official `leanprover` GitHub org) provides machine-to-machine interaction via JSON over stdin/stdout. Its killer feature is **subgoal independence** — you can solve subgoals in any order, enabling Monte Carlo Tree Search-style proof exploration. Install via `pip install git+https://github.com/stanford-centaur/PyPantograph`.

**leanclient** (PyPI version 0.9.2, January 2026) is a thin LSP wrapper for existing Lean projects, useful when you need hover information, diagnostics, and symbol resolution. **LeanCopilot** (1,200 stars) runs LLM inference natively inside Lean via CTranslate2; it cannot be called directly from Python but can be used through Lean code submitted via LeanInteract or LeanDojo.

For LLM-assisted proving, **ReProver** provides HuggingFace models (`kaiyuy/leandojo-lean4-tacgen-byt5-small`) that generate tactics from proof states. **llmstep** runs a Python HTTP server that Lean queries for suggestions. **DeepSeek-Prover-V2** (April 2025) represents the current state of the art.

The simplest possible approach requires no library at all — write Lean code to a `.lean` file and run `lake build` as a subprocess, parsing stdout/stderr for success or error messages.

## Python ↔ Isabelle: the tooling is less mature but functional

Isabelle's Python ecosystem is smaller but has one excellent entry point. The current Isabelle version is **Isabelle2025** (released March 2025), with Isabelle2025-1 released in December 2025.

**isabelle-client** is the recommended starting tool. It is pip-installable (`pip install isabelle-client`), actively maintained (version **1.0.0**, November 2025, 62 releases), and documented at isabelle-client.readthedocs.io. It communicates with Isabelle's built-in TCP server:

```python
from isabelle_client import get_isabelle_client, start_isabelle_server

server_info, _ = start_isabelle_server()
isabelle = get_isabelle_client(server_info)
isabelle.session_build(session="HOL")
session_id = isabelle.session_start()

# Submit a theory for verification
response = isabelle.use_theories(
    session_id=session_id,
    theories=["MyTheory"],
    master_dir="/path/to/theories",
    watchdog_timeout=0
)
```

The higher-level `IsabelleConnector` API allows inline verification without separate theory files:

```python
from isabelle_client.isabelle_connector import IsabelleConnector, IsabelleTheoryError

connector = IsabelleConnector()
try:
    connector.build_theory(r'lemma "\<forall> x. \<exists> y. x = y"' "\nby auto")
    print("Verified!")
except IsabelleTheoryError as error:
    print(error.args[0])
```

The critical limitation: isabelle-client operates at the **theory-file level**, not step-by-step tactic level. You submit complete theory files and get pass/fail results, but cannot inspect intermediate proof states.

For step-by-step interaction, **QIsabelle** is the best option. It runs a Scala server (via scala-isabelle) inside Docker, exposing an HTTP API. No local Isabelle installation needed — everything lives in containers, though pre-built AFP heap images consume **~40GB**:

```python
from session import QIsabelleSession

with QIsabelleSession(session_name="HOL", session_roots=[]) as session:
    session.new_theory(theory_name="Test", new_state_name="s0",
                       imports=["Complex_Main"])
    done, goals = session.execute("s0", 'lemma "prime p ⟹ p > (1::nat)"', "s1")
    done, goals = session.execute("s1", "by simp", "s2")  # done=True
```

**Isa-REPL** (`pip install IsaREPL`) is a newer alternative offering socket-based step-by-step interaction with state rollback. **PISA** (Portal to ISAbelle) is the original research tool used in many LLM-proving papers (Thor, LEGO-Prover) but is tied to Isabelle2022 and has complex setup requirements. **Isabellm** (January 2026) is the newest LLM-powered prover for Isabelle, supporting local models via Ollama.

Sledgehammer — Isabelle's crown jewel for automation — can be invoked programmatically by including `sledgehammer` as a proof method in submitted theory files. It calls external ATPs (E, SPASS, Vampire, Z3) in parallel with a default **30-second timeout** and returns suggested proof methods.

## The complementary library coverage is the strongest argument for a hybrid system

The gap analysis reveals that **Lean 4 and Isabelle have almost perfectly complementary coverage** for stochastic processes, making a hybrid system not just interesting but genuinely useful.

| Topic | Lean 4 (Mathlib) | Isabelle (HOL-Prob + AFP) |
|-------|:-:|:-:|
| Probability spaces, σ-algebras | ✅ Full | ✅ Full |
| Conditional expectation | ✅ Full | ✅ Full |
| Discrete-time Markov chains | ⚠️ Kernels only | ✅ Full (classification, stationary dists) |
| Continuous-time Markov chains | ❌ | ✅ Full |
| Discrete-time martingales | ✅ Full (convergence, Doob decomp) | ❌ |
| Optional stopping theorem | ✅ Full | ❌ |
| Brownian motion | ⚠️ Active project (construction done) | ❌ |
| Central Limit Theorem | ❌ | ✅ Full |
| Ergodic theorems (Birkhoff) | ❌ | ✅ Full |
| Laws of large numbers | ✅ Strong (Etemadi) | ✅ Both (ergodic approach) |
| Itô integral / Itô's formula | ❌ (planned) | ❌ |
| SDEs, Girsanov, Feynman-Kac | ❌ | ❌ |
| BSDEs, Black-Scholes | ❌ | ❌ |

**Lean's Mathlib probability modules** live under `Mathlib.Probability.*` and `Mathlib.MeasureTheory.*`. Key imports include `Mathlib.Probability.Martingale.Basic` (martingale definitions and convergence), `Mathlib.Probability.Martingale.OptionalStopping`, `Mathlib.Probability.StrongLaw` (Etemadi's proof), `Mathlib.Probability.Process.Stopping` (stopping times, filtrations), and seven named distributions (Gaussian, Exponential, Gamma, Geometric, Poisson, Uniform, Pareto). The Brownian motion formalization by Degenne, Ledvinka, Marion, and Pfaffelhuber (arXiv:2511.20118, November 2025) has completed the construction via the Kolmogorov extension theorem and Kolmogorov-Chentsov continuity theorem, with migration to Mathlib ongoing. The Itô integral is explicitly declared as the next project phase.

**Isabelle's coverage** centers on the `HOL-Probability` session (in the distribution) plus AFP entries. The `Markov_Models` AFP entry (Hölzl, J. Autom. Reasoning 2017) includes discrete-time and continuous-time Markov chains, MDPs, pCTL model checking, and applications. The `Ergodic_Theory` entry (Gouëzel, 2015) formalizes the Birkhoff ergodic theorem, Kingman's subadditive theorem, and Poincaré recurrence. The `Laws_of_Large_Numbers` entry (Eberl, 2021) derives both laws via ergodic theory. The CLT was formalized by Avigad, Hölzl, and Serafin. The `Levy_Prokhorov_Metric` entry (Hirata, ITP 2024) adds weak convergence and the Portmanteau theorem.

**The entire second half of a graduate stochastic processes course — stochastic calculus — cannot be formalized in either system** as of February 2026. This is itself a significant finding for a thesis.

## Hybrid architectures: what exists and what you must build

The **Flyspeck project** (Thomas Hales, 2003–2014) is the only major example of a multi-prover formal verification effort. It proved the Kepler conjecture using HOL Light for analysis and Isabelle for tame planar graph classification. The team acknowledged that their "single greatest vulnerability to error lies in the hand translation of this one statement from Isabelle to HOL Light." No automated translation was used.

**No direct Lean 4 ↔ Isabelle translator exists.** The closest paths are:

- **Dedukti** (λΠ-calculus modulo rewriting) serves as a translation hub. The `isabelle_dedukti` tool can export Isabelle/HOL theories to Dedukti/Lambdapi, and STTfaXport can export from Dedukti to Lean. However, translations are "notoriously sluggy, resource-demanding, and do not scale to large developments."
- **LLM-based autoformalization** is currently more practical for statement-level translation. Wu et al. (NeurIPS 2022) demonstrated autoformalization to Isabelle using LLMs. This is imperfect but workable for translating theorem statements (not proofs) between systems.
- **Blanqui's dk2isa project** (active as of February 2026) specifically targets Lean/Coq → Isabelle translation via Dedukti, but remains research-stage.

The practical architecture for your system should follow a **parallel proof search** model rather than attempting proof translation:

```
Python Orchestrator
├── Theorem Parser (natural language or structured JSON)
├── Domain Classifier / Router
│   ├── Library coverage lookup (Mathlib vs AFP)
│   ├── Type analysis (dependent types → Lean)
│   └── Automation needs (first-order → Isabelle/Sledgehammer)
├── Lean 4 Backend (LeanInteract or LeanDojo)
│   └── Submit theorem, attempt proof, return result
├── Isabelle Backend (isabelle-client or QIsabelle)
│   └── Submit theorem, attempt proof, return result
├── SymPy Fallback (symbolic computation checks)
└── Result Aggregator (confidence levels, cross-validation)
```

**Routing heuristics** should use these criteria: route to Isabelle when the theorem involves Markov chains, ergodic theory, CLT, or benefits from heavy first-order automation (Sledgehammer). Route to Lean when the theorem involves martingales, stopping times, dependent type structures, or abstract algebra with type parameters. Try both for foundational measure theory results where both libraries have coverage.

## SymPy as a third verification tier

SymPy serves as "soft verification" — not proving theorems but providing evidence. The MATH-VF framework (arXiv:2505.20869) demonstrates this "tool-integrated critic" approach. SymPy can verify algebraic identities, check symbolic differentiation and integration, evaluate expressions at test points, compute moments and MGFs of distributions, and solve equations. It cannot handle quantifier reasoning, topological properties, abstract measure-theoretic statements, or convergence of function sequences.

The safest integration follows the **"skeptical approach"** (Harrison & Théry, 1998): treat SymPy results as conjectures requiring independent verification. A practical confidence framework:

| Level | Method | Confidence |
|-------|--------|------------|
| L5 | Full formal proof (Lean or Isabelle) | ~100% (modulo kernel soundness) |
| L4 | Partial proof with explicit `sorry` gaps | 90–99% |
| L3 | Proved in both systems independently | 95%+ (cross-validated) |
| L2 | SymPy symbolic verification | 70–90% (evidence, not proof) |
| L1 | Numerical/Monte Carlo checks | 50–70% |
| L0 | Informal proof only | Baseline |

No existing framework classifies mathematical verification confidence in this tiered way — this taxonomy itself constitutes a novel contribution.

## A realistic thesis timeline and what counts as novel

**Learning curve reality**: a math graduate student should expect **2–3 months** to reach basic proficiency in each system (Natural Number Game → Mathematics in Lean for Lean 4; Concrete Semantics for Isabelle). Working with measure theory libraries requires **6–12 months per system**. Kevin Buzzard's teaching experience at Imperial shows that even with weekly workshops, the steep learning curve causes significant attrition. The Lean community emphasizes: "It is much much longer to formalize a proof than to be sure the proof is right."

**Recommended 15–18 month plan**:

- Months 1–4: Learn both systems in parallel. Start with Lean 4 (larger community, more active probability development). Use Natural Number Game, then Mathematics in Lean. Begin Isabelle via Concrete Semantics in month 2–3.
- Months 4–10: Formalize specific theorems. Pick a bounded target — e.g., properties of discrete Markov chains in Isabelle and martingale convergence in Lean. Build the Python orchestration layer incrementally.
- Months 10–14: Integration work. Connect LeanInteract and isabelle-client through your Python orchestrator. Add SymPy fallback. Run comparative benchmarks.
- Months 14–18: Write the thesis. The comparison and gap analysis should emerge naturally from the formalization experience.

**What constitutes a novel contribution** — several elements are individually publishable:

- **The hybrid architecture itself**: No existing system orchestrates Lean + Isabelle + SymPy. The Dagstuhl Seminar 23401 ("Automated Mathematics") identified interoperability as a major open challenge.
- **The systematic gap analysis**: A detailed empirical comparison of formalizing stochastic processes theorems in both systems, with quantitative data on effort, automation effectiveness, and library coverage.
- **New formalizations**: Any probability result not currently in Mathlib or AFP. Even formalizing a single new theorem (e.g., a Markov chain property in Lean, or martingale convergence in Isabelle) is publishable.
- **The verification confidence framework**: The tiered L0–L5 classification applied to stochastic processes has no precedent.

No thesis combining Lean and Isabelle for the same mathematical domain was found in the literature search, confirming the novelty.

## Concrete setup: getting from zero to a working system

**Project structure**:

```
thesis-hybrid-verification/
├── lean/                      # Lake-managed Lean 4 project
│   ├── lakefile.lean          # Requires Mathlib
│   ├── lean-toolchain         # Pin Lean version
│   └── HybridVerify/          # Your formalizations
├── isabelle/                  # Isabelle theories
│   ├── ROOT                   # Session definition
│   └── theories/              # .thy files
├── python/
│   ├── orchestrator.py        # Main routing logic
│   ├── lean_backend.py        # LeanInteract wrapper
│   ├── isabelle_backend.py    # isabelle-client wrapper
│   ├── sympy_verifier.py      # Symbolic computation checks
│   └── confidence.py          # Tiered confidence scoring
├── docker/
│   ├── docker-compose.yml
│   ├── Dockerfile.lean
│   └── Dockerfile.isabelle
└── benchmarks/                # Test theorems and results
```

**Installation checklist**:

```bash
# 1. Lean 4 (via elan)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | bash
lake +v4.24.0 new lean math  # creates project with Mathlib

# 2. Python tools for Lean
pip install lean-interact lean-dojo

# 3. Isabelle
wget https://isabelle.in.tum.de/dist/Isabelle2025_linux.tar.gz
tar -xzf Isabelle2025_linux.tar.gz
export PATH="$PATH:$HOME/Isabelle2025/bin/"
isabelle build -b HOL  # ~30 min

# 4. Python tools for Isabelle
pip install isabelle-client

# 5. SymPy
pip install sympy
```

**Key learning resources** (in priority order): For Lean 4, start with the Natural Number Game (adam.math.hhu.de), then Mathematics in Lean by Avigad and Massot, then the Lean Zulip chat. For Isabelle, start with Concrete Semantics by Nipkow and Klein (free at concrete-semantics.org), then the AFP examples. For measure theory specifically, read Degenne's "Basic probability in Mathlib" blog post (October 2024) and Hölzl's Markov chain formalization paper.

## Conclusion: the architecture works because the gaps align

The strongest argument for building this system is not theoretical — it is the empirical fact that Lean and Isabelle cover almost perfectly disjoint portions of stochastic processes. A student who needs to formalize both Markov chain properties and martingale convergence has no single-system option. The Python orchestration layer (using LeanInteract and isabelle-client, both pip-installable and actively maintained) makes the engineering tractable. The thesis novelty comes not from any single formalization but from the systematic integration: the architecture, the gap analysis, and the confidence framework together constitute a contribution that no prior work addresses. Start with Lean 4 (bigger community, more momentum in probability formalization), add Isabelle for its unique strengths (CLT, Markov chains, Sledgehammer automation), and use SymPy as a pragmatic fallback for the large territory — especially stochastic calculus — that neither prover can yet reach.
