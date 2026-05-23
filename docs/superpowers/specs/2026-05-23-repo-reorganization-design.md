# Repo reorganization — design spec

**Date:** 2026-05-23
**Status:** Draft, awaiting user approval
**Scope:** Single-PR structural reorganization. Zero proof changes.

## Vision

This repo is THE place where machine-verified quant-finance theorems live in
Lean 4. It is a **Lean library**, not a Python verification framework. Every
structural decision — directory layout, naming, doc placement, dependency
graph — must reinforce that fact.

The Python orchestrator, Isabelle stubs, and SymPy backend were vestiges of an
abandoned "hybrid 3-backend verification" framing. The actual asset is 138
`.lean` files of formally verified quant-finance content built on Mathlib +
Degenne's BrownianMotion. The reorganization aligns the repo's *shape* with
its *substance*.

## Diagnosis

Eight concrete problems, ranked by visitor impact:

1. **The lean library is buried under `lean/`.** A visitor sees `lean/` and
   `python/` as siblings, suggesting equal status. In fact the lean directory
   *is* the artifact; everything else exists to serve it.

2. **10 markdown files at root.** `README.md`, `FORMALIZATION_STATUS.md`,
   `BRIDGE_AUDIT.md`, `LEARNINGS.md`, `MATH_DEPTH_ROADMAP.md`,
   `QUANTFIN_ROADMAP.md`, `AGENTS.md`, `CLAUDE.md`, `degenne-pr-description.md`,
   `pr-description.md`. No signal-vs-noise hierarchy. A newcomer cannot tell
   what is authoritative versus internal notes versus transient PR drafts.

3. **Naming is vestigial.** The Python package is `hybrid_verify`, the Lean
   library is `HybridVerify`, the Docker image is `quantfin-verify`. Three
   names for one thing, all rooted in the abandoned "hybrid 3-backend"
   framing. Current reality is Lean-first across all routes (per
   `CLAUDE.md` routing table and user direction).

4. **Two upstream-PR staging areas.** `proposals/` (committed:
   `bm-martingales`, `mathlib-gaussian-tail`) and `staging/` (untracked:
   `degenne-pr`, `mathlib-pr`, `zulip`) do the same job.

5. **Dead Python in `python/`.** `add_phase12_benchmarks.py`,
   `add_phase13_benchmarks.py`, `restructure_rename.py` are one-shot
   migration scripts that ran once and were never deleted.

6. **Dead Isabelle.** `isabelle/theories/StochasticBasic.thy` is a single
   file. User direction (recorded in memory): "nevermind isabelle. full
   stream ahead with lean."

7. **Dead SymPy.** `python/sympy_verifier.py` is referenced by the
   orchestrator but no active route uses it (per `CLAUDE.md` routing table
   and memory).

8. **Reference material is split.** `papers/` directory plus
   `stochastic_notes.pdf` (2 MB, at root) should live together.

## Target tree

```
automated_proofs_quantfin/
├── README.md                       # already framed correctly; trim + relink
├── CONTRIBUTING.md                 # NEW — 1-page "how to add a theorem"
├── CLAUDE.md, AGENTS.md            # kept at root (AI-tool convention)
├── LICENSE                         # hoisted from lean/ or new Apache 2.0
├── lakefile.lean                   # ★ hoisted from lean/
├── lean-toolchain                  # ★ hoisted
├── lake-manifest.json              # ★ hoisted
├── HybridVerify.lean               # ★ hoisted (umbrella)
├── HybridVerify/                   # ★ hoisted (138 files, 10 subdirs unchanged)
│   ├── Foundations/                # 32 files: math primitives & bridges
│   ├── BlackScholes/               # 43 files: BS family & exotics
│   ├── Binomial/                   # CRR, American, Snell, reflection
│   ├── Futures/                    # Black-76, swaption
│   ├── FixedIncome/                # Vasicek, hazard, KMV, duration
│   ├── Portfolio/                  # Markowitz, CAPM, BL, risk parity
│   ├── RiskMeasures/               # coherent axioms, VaR/CVaR, spectral
│   ├── Performance/                # Sharpe, Sortino, Kelly
│   ├── Actuarial/                  # mortality, compound Poisson
│   ├── DeFi/                       # constant-product AMM
│   └── Examples.lean
├── docs/
│   ├── coverage.md                 # was FORMALIZATION_STATUS.md
│   ├── bridges.md                  # was BRIDGE_AUDIT.md
│   ├── patterns.md                 # was LEARNINGS.md
│   ├── roadmap.md                  # merged MATH_DEPTH + QUANTFIN roadmaps
│   └── superpowers/                # skill workspace (this file lives here)
├── upstream/                       # consolidates proposals/ + staging/
│   ├── README.md                   # strategy + links to open PRs
│   ├── brownian-motion/            # = bm-martingales + degenne-pr/Gaussian
│   ├── mathlib/                    # = mathlib-gaussian-tail + mathlib-pr/Probability
│   └── zulip/                      # = zulip drafts
├── references/                     # = papers/ + stochastic_notes.pdf
│   ├── stochastic_notes.pdf
│   ├── ssrn-6336503.pdf            # Nagy "From Itô to Black-Scholes"
│   └── OASIcs.FMBC.2024.5.pdf      # Pusceddu-Bartoletti AMMs
├── benchmarks/                     # kept; demoted from headline
├── tools/
│   └── verify/                     # was python/, minus dead scripts
│       ├── cli.py
│       ├── orchestrator.py
│       ├── router.py
│       ├── lean_backend.py
│       ├── lean_repl.py
│       ├── confidence.py
│       ├── config.py
│       ├── coverage_report.py
│       ├── models.py
│       ├── sympy_verifier.py       # dead-but-harmless, kept
│       └── __init__.py
├── docker/                         # kept; mount paths patched
├── scripts/                        # kept; paths patched
├── tests/                          # kept at root (pytest discovers it)
├── hybrid_verify.toml              # kept; local_project="." not "lean"
├── pyproject.toml                  # kept; package path patched
└── requirements.txt                # kept
```

Net change: a visitor running `ls` immediately sees a Lean project
(lakefile at root, library directory at root). Docs cluster in `docs/`.
Ops cluster in `tools/` + `docker/` + `scripts/`. Upstream work clusters
in `upstream/`. PR-staging redundancy is gone. Zero ambiguity about what
the artifact is.

## What I am NOT touching

Explicit scope discipline to keep this a single-PR change:

- **Lean library name (`HybridVerify`)** — renaming would be 138-file
  namespace churn for cosmetics. The Lake name is the install handle; the
  external storefront is the repo name + README. Mathlib lives in a repo
  called `mathlib4`. Fine.
- **Lean library internal subdirectory organization** — already good.
- **Python package name (`python`)** — same reason. Path is changing
  (`python/` → `tools/verify/`), but the importable name doesn't need to.
  Defer rename to a separate cycle if user wants.
- **Mathlib / BrownianMotion pins** — frozen.
- **Benchmark JSON format** — frozen.
- **Proof content** — zero `.lean` file edits.
- **`tests/` location** — pytest discovers from root; leave alone.

## Kill list

Delete with prejudice (already-dead files, no consumers):

- `python/add_phase12_benchmarks.py` — one-shot migration
- `python/add_phase13_benchmarks.py` — one-shot migration
- `python/restructure_rename.py` — one-shot migration
- `python/isabelle_backend.py` — Isabelle dropped per user direction
- `python/lean-check.sh` — duplicate of `scripts/lean-check.sh`
- `isabelle/theories/StochasticBasic.thy` — single dead file
- `isabelle/` — emptied
- `degenne-pr-description.md` — leftover PR draft (gitignored)
- `pr-description.md` — leftover PR draft (gitignored)

Quarantine but keep:

- `python/sympy_verifier.py` → `tools/verify/sympy_verifier.py` — orchestrator
  imports it; deleting requires touching `orchestrator.py`. Keep
  dead-but-harmless under `tools/verify/`. Mark as legacy in
  `tools/verify/README.md`.

## Files needing path updates (patch list)

After moves, these files reference `lean/...` or `python/...` paths and
must be patched:

1. `hybrid_verify.toml` — `local_project = "lean"` → `local_project = "."`
2. `docker/docker-compose.yml` — bind-mount paths (`./lean`, `./python`,
   `./tests`, `./benchmarks`, `./hybrid_verify.toml`) and command paths
3. `docker/Dockerfile.verify` — comment references and `WORKDIR`/`COPY`
   paths
4. `scripts/lean-check.sh` — usage examples and the file-path argument
   it forwards
5. `pyproject.toml` — `packages = ["python"]` → `packages = ["tools.verify"]`
   (or rename the Python package; see scope discipline note)
6. `tests/test_router.py` — imports of `python.router`, `python.models`,
   etc. → `tools.verify.router`, `tools.verify.models`
7. `README.md` — file path references throughout
8. `CLAUDE.md` — file path references throughout
9. `AGENTS.md` — file path references throughout
10. `docs/bridges.md` (was `BRIDGE_AUDIT.md`) — internal cross-references
11. `docs/coverage.md` (was `FORMALIZATION_STATUS.md`) — internal cross-references

## Migration plan

Single PR. Five mechanical steps. Verified at each step.

**Step 1: hoist the Lake project.**
```
git mv lean/HybridVerify HybridVerify
git mv lean/HybridVerify.lean .
git mv lean/lakefile.lean .
git mv lean/lean-toolchain .
git mv lean/lake-manifest.json .
# move LICENSE if present under lean/
rm -rf lean/.lake          # build artifact, regenerates
rmdir lean                 # should be empty
```

**Step 2: create new directory homes.** `mkdir docs upstream references
tools/verify`. Move files in with `git mv` (preserves history):
- doc moves listed in §4
- `proposals/{bm-martingales,mathlib-gaussian-tail}` + `staging/{degenne-pr,mathlib-pr,zulip}` → `upstream/`
- `papers/*` + `stochastic_notes.pdf` → `references/`
- `python/*` → `tools/verify/` (minus dead-list scripts)

**Step 3: kill the dead list.** `git rm` each file in §6.

**Step 4: patch the 11 path-reference files.** Mechanical sed-able edits.

**Step 5: verify.**
```
# Lean side: no-op recompile, confirms structural move works
cd /home/rapha/code/automated_proofs_quantfin
docker compose -f docker/docker-compose.yml build verify    # bakes new oleans
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/cross_validated.json -v

# Python side: confirm test_router still passes under new import paths
docker compose -f docker/docker-compose.yml run --rm \
    --entrypoint python3 verify -m pytest tests/test_router.py -q
docker compose -f docker/docker-compose.yml run --rm \
    --entrypoint python3 verify -m tools.verify.coverage_report
```

## Risks and mitigations

| Risk | Mitigation |
|---|---|
| Docker rebuild fails after path changes | Step 5 catches this before commit. Rollback = `git reset --hard HEAD`. |
| Lean lake-build regression from hoist | Step 5 runs full lake build. Mathlib pin and proof content unchanged; only file locations move. |
| External consumer hardcoded `lean/HybridVerify` import path | None known. The Lake package is consumed locally; not published. |
| AI-tool config (CLAUDE.md / AGENTS.md) path references go stale | Patched in step 4. Tools re-read on next session. |
| Git history continuity for moved files | `git mv` preserves rename detection; `git log --follow` works. |

## Decisions deferred (single follow-up cycle if user wants)

1. **Rename `HybridVerify` → `QuantFin`.** 138-file namespace churn. Real
   value if the lib is ever published; minor if it stays a private repo.
2. **Rename `hybrid_verify` Python package → `quantfin_verify`.** Smaller
   churn, same value question.
3. **Delete `benchmarks/` and `tools/verify/` outright.** The lean library
   stands alone via `lake build`. Orchestrator + JSON were the original
   verification protocol but are now overhead. Keeping them as a
   regression-test harness has some value; deleting them sharpens the
   "this is a Lean library" claim further.
4. **Publish to a Lake registry / reservoir.** Out of scope of this PR but
   becomes natural once the repo is shaped like a Lean library.
