# Mathematical finance, formally verified

[![build](https://github.com/raphaelrrcoelho/formal-mathfin/actions/workflows/build.yml/badge.svg)](https://github.com/raphaelrrcoelho/formal-mathfin/actions/workflows/build.yml)
[![axioms](https://img.shields.io/badge/axioms-propext%2C%20Classical.choice%2C%20Quot.sound-blue)](MathFin/AxiomAudit.lean)
[![blueprint](https://img.shields.io/badge/blueprint-deductive_spine-blue)](docs/blueprint.md)
[![Lean](https://img.shields.io/badge/Lean-4.31.0-blue)](lean-toolchain)
[![license](https://img.shields.io/badge/license-Apache_2.0-blue)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20477782.svg)](https://doi.org/10.5281/zenodo.20477782)
[![arXiv](https://img.shields.io/badge/arXiv-2606.01356-b31b1b)](https://arxiv.org/abs/2606.01356)
[![dataset](https://img.shields.io/badge/HF-dataset-ffcc4d)](https://huggingface.co/datasets/raphaelrrcoelho/formal-mathfin-theorems)
[![PRs welcome](https://img.shields.io/badge/PRs-welcome-brightgreen)](CONTRIBUTING.md)
[![Contributor Covenant](https://img.shields.io/badge/Contributor%20Covenant-2.1-4baaaa)](CODE_OF_CONDUCT.md)

> A Lean 4 library building toward a **formal theory of mathematical finance** — every result
> machine-checked against [Mathlib](https://github.com/leanprover-community/mathlib4) and
> [Degenne's BrownianMotion](https://github.com/RemyDegenne/brownian-motion), with an exact statement of
> what is proved and what is assumed, and the deep connections between the field's pillars made
> *load-bearing* rather than decorative.

**`309` theorems · `292` delivery-ready · `0` sorries · axioms-clean · `lake build` is the proof.**

---

## What we're building

Formalized finance is usually a scattering of isolated results. The ambition here is a **theory**: prove
the Black–Scholes world, the Itô tower, the Fundamental Theorem of Asset Pricing, and the risk-measure
layer — then wire them together around the field's actual organizing principles, so that the
**architecture** is the artifact, not just the catalogue. "Top-notch" here is not *more theorems* — it is
the theorems organized around the field's spine, with the deep cross-connections proved.

Two commitments make that trustworthy:

- **The build is the proof.** A clean `lake build` re-elaborates every theorem against pinned Lean +
  Mathlib. There is no `sorry` and no project-local axiom anywhere; every `full` result depends only on
  the three standard axioms `propext, Classical.choice, Quot.sound`, `#print axioms`-pinned as a CI
  invariant in [`MathFin/AxiomAudit.lean`](MathFin/AxiomAudit.lean).
- **Honest scope, enforced — never overclaimed.** Every entry declares a faithfulness status
  (`full` / `library_wrapper` / `reduced_core`); an input-hash [verification
  ledger](verification_ledger.json) records exactly what each was checked under; and a multi-agent
  [values review](docs/values-review.md) runs on a CI cadence. The README does not claim a result the
  kernel has not accepted.

## The architecture — the field's spine

Mathematical finance is a few deep principles whose consequences are the models. The library has the
**four pillars**; the active program is to make the **connective tissue** between them load-bearing.

| Pillar | The principle | In the library |
|---|---|---|
| **I — No-arbitrage as convex duality** | the separating hyperplane *is* the equivalent martingale measure | the FTAP tower · [`ConvexDuality`](MathFin/Foundations/ConvexDuality.lean) · state prices |
| **II — Stochastic calculus** | every model is `dX = b dt + σ dB`; Itô makes functionals computable | the Itô tower: from-scratch L² integral, Itô's formula, quadratic variation |
| **III — Probabilistic ⟷ analytic duality** | the price is both a risk-neutral expectation and a PDE solution | the BS-PDE keystone (Feynman–Kac and Itô routes) |
| **IV — Intensity & exponential families** | closed forms and the "exp of an integrated intensity" | Gaussian closed forms · the exponential-discount root · credit/mortality unification |

**The bridges are where the depth lives** — each makes two pillars one theorem:

| Bridge | Connects | Status |
|---|---|---|
| **Convex duality** | I ↔ IV (pricing ↔ risk) | ✅ **WIRED** — the FTAP and the coherent-risk representation are proved to be the *same* Hahn–Banach theorem |
| **Feynman–Kac** | II ↔ III | ✅ **WIRED** — the Black–Scholes PDE from the risk-neutral expectation |
| **Donsker / CLT** | discrete ↔ continuous | ✅ **WIRED** — CRR binomial → Black–Scholes |
| **Girsanov** | I ↔ II | ◐ **partially wired** — the EMM is now an *explicit* change of measure (constant θ); the distributional Girsanov + adapted θ stay open ([#40](https://github.com/raphaelrrcoelho/formal-mathfin/issues/40)) |
| **Numéraire** | IV ↔ I | ◻️ open |

→ The full spine, seam by seam: **[`docs/mathematical-architecture.md`](docs/mathematical-architecture.md)**.

## Landmark results

| Result | Statement | Lean |
|---|---|---|
| **Pricing = risk, one theorem** | the FTAP separating functional and the coherent-risk representation are the same finite-dimensional Hahn–Banach separation | [`exists_pos_separating_of_cone_disjoint_simplex`](MathFin/Foundations/ConvexDuality.lean) · [`coherentRisk_isLUB`](MathFin/RiskMeasures/AcceptanceSet.lean) |
| **BS PDE from Feynman–Kac** | the Black–Scholes PDE derived from the risk-neutral expectation by heat-kernel differentiation — independent of the closed form and of Itô | [`bsV_satisfies_bs_pde_via_feynmanKac`](MathFin/BlackScholes/PDEFromFeynmanKac.lean) |
| **CRR → Black–Scholes** | the n-step binomial call price converges to `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)` (characteristic functions + Lévy continuity + put-call parity) | [`binomialPrice_call_tendsto_bs_closed`](MathFin/Binomial/CRRClosedForm.lean) |
| **Continuous-time Itô formula** | `f(B_T) − f(B_0) = ∫₀ᵀ f′(B_s) dB_s + ½∫₀ᵀ f″(B_s) ds`, on a from-scratch L² Itô integral, for a general `C³` `f` with no growth bound | [`ito_formula_unrestricted`](MathFin/Foundations/ItoFormulaUnrestricted.lean) |
| **The EMM via Girsanov** | the risk-neutral measure is *constructed* as an explicit density change of the physical measure, `Q = withDensity(exp(−θX_T − ½θ²T))`; the discounted stock is a proven `Q`-martingale — retiring the Wald shortcut | [`bs_discounted_isQMartingale`](MathFin/Foundations/Girsanov.lean) |
| **Jump risk is never free** | the Merton (1976) jump-diffusion price dominates Black–Scholes | [`bsV_le_mertonCallPrice`](MathFin/BlackScholes/MertonDominance.lean) |

## A theorem, up close

```lean
-- Coherent risk = sup of expected loss over the representing measures (the ADEH representation).
-- Closedness of the acceptance set is *derived* from the four axioms, not assumed.
theorem coherentRisk_isLUB {ι : Type*} [Fintype ι] [Nonempty ι] {ρ : (ι → ℝ) → ℝ}
    (hρ : IsCoherentRisk ρ) (X : ι → ℝ) :
    IsLUB ((fun q => ∑ i, q i * (- X i)) '' representingSet ρ) (ρ X)

-- Black–Scholes delta, in one line of the "magic identity" collapse: ∂V/∂S = Φ(d₁).
lemma hasDerivAt_bsV_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s => bsV K r σ s τ) (Phi (bsd1 S K r σ τ)) S
```

See [`MathFin/Examples.lean`](MathFin/Examples.lean) for a curated tour.

## Status at a glance

| | |
|---|---:|
| theorems (machine-checked) | **309** |
| delivery-ready (`full` + `library_wrapper`) | **292** |
| full derivations | 274 |
| reduced cores (honest special cases) | 17 |
| placeholders / sorries | **0** |
| axioms used | `propext, Classical.choice, Quot.sound` only |
| Lean / Mathlib | `v4.31.0`, pinned ([`lean-toolchain`](lean-toolchain)) |

## Quick start

```bash
# Pull the pinned image (~3 min) instead of building locally (~15 min)
docker compose -f docker/docker-compose.yml pull verify

# Build the whole library — a clean exit means every theorem typechecks
docker compose -f docker/docker-compose.yml run --rm --entrypoint bash verify -lc 'lake build'

# Fast authoring loop (5–30s feedback via the persistent REPL daemon)
docker compose -f docker/docker-compose.yml up -d lean-repl
./scripts/lean-check.sh MathFin/<Section>/<Module>.lean
```

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for the full workflow.

## How verification works

- **The build is the proof.** `lake build` re-elaborates every theorem against the pinned toolchain; a
  clean exit is the canonical verification.
- **Axiom audit.** [`AxiomAudit.lean`](MathFin/AxiomAudit.lean) (headliners) and
  [`AxiomAuditGen.lean`](MathFin/AxiomAuditGen.lean) (generated over the whole corpus) pin `#print axioms`
  as `#guard_msgs` build invariants — no `sorry`, no project-local axioms.
- **Verification ledger.** [`verification_ledger.json`](verification_ledger.json) records the input-hash
  (snippet + transitive imports + toolchain pins) each entry last verified under; only entries whose
  inputs changed re-run.
- **CI gates.** Every push runs the Python gates (status taxonomy, forbidden tactics, ledger freshness)
  and the environment linter *before* the Lean build.
- **Values review.** Sessions that change proof content close with a multi-agent review over eight
  judgment lenses, logged in [`docs/values-review.md`](docs/values-review.md) (cadence CI-enforced).

## What's covered

A breadth-and-depth library across eleven areas. Headlines per area (full per-theorem audit + status in
[`docs/coverage.md`](docs/coverage.md)):

- **Black–Scholes & exotics** — the full Greek matrix (δ, γ, vega, θ, ρ, vanna, volga, charm), digitals,
  BS-Merton dividends, Garman–Kohlhagen FX, implied-vol uniqueness, the PDE, Breeden–Litzenberger;
  Margrabe exchange, chooser, capped/bull/butterfly, lookback, Asian bounds.
- **Bachelier & Black-76** — arithmetic-BM pricing + Greeks; the futures-options formula + swaption.
- **Binomial / lattice** — replication + uniqueness, American/Bermudan via the Snell envelope, **CRR →
  Black–Scholes** convergence, Merton 1973 dominance, André's reflection principle.
- **Fixed income & credit** — bonds, duration/convexity, Redington immunization, yield-curve bootstrap,
  reduced-form hazard credit, Vasicek (ODE + SDE law), KMV–Merton default.
- **Portfolio & performance** — Markowitz (2- and N-asset), CAPM + equilibrium, two-fund separation,
  risk parity, Black–Litterman, tangency; Sharpe/Sortino/Treynor/Information ratios, Kelly.
- **Risk measures** — Gaussian VaR/CVaR closed forms, the coherent (ADEH) axioms + **the representation
  as a sup over measures**, spectral measures, Rockafellar–Uryasev, Herfindahl–Hirschman.
- **Stochastic foundations** — the **Itô tower** (from-scratch L² integral, isometry, quadratic
  variation, Itô's formula), the **FTAP tower** (finite-Ω multi-period, general-Ω one-period, d-asset),
  static Girsanov, Feynman–Kac, and **the convex-duality unification**.
- **Actuarial & DeFi** — Gompertz mortality, annuities, net premium; constant-product (Uniswap-v2) AMMs.

## Scope: what's not done

Honesty is the point, so the gaps are explicit:

- **17 `reduced_core` entries** — special cases or algebraic/structural cores whose fully general form is
  not yet formalized (the 2-D Itô formula, Lévy's characterisation, SDE existence/uniqueness, continuous
  Girsanov, some Markov/Poisson cores). Tracked per-entry in [`docs/coverage.md`](docs/coverage.md).
- **Girsanov (I↔II) is partially wired** — the EMM/change-of-measure martingale side is proved (constant θ); the *distributional* Girsanov and general θ remain open, as does the **numéraire (IV↔I)** bridge.
- **Known upstream/limit gaps** — e.g. the superhedging strong-duality *equality* needs a
  finite-dimensional Farkas / polyhedral-cone closedness absent from Mathlib at this pin
  ([#39](https://github.com/raphaelrrcoelho/formal-mathfin/issues/39)).

The frontier is in the [open issues](https://github.com/raphaelrrcoelho/formal-mathfin/issues) and
[`docs/roadmap.md`](docs/roadmap.md).

## Documentation

| File | Contents |
|---|---|
| [`docs/mathematical-architecture.md`](docs/mathematical-architecture.md) | **The field's spine** — the four pillars, the connective bridges, and which seams are wired vs open. |
| [`docs/architecture.md`](docs/architecture.md) | The engineering design: structural-principle modules, the three honesty tiers, the bridge methodology. |
| [`docs/blueprint.md`](docs/blueprint.md) | The deductive spine — a dependency graph from Brownian motion to Black–Scholes, each node linked to its proof. |
| [`docs/coverage.md`](docs/coverage.md) | Per-theorem audit: faithfulness status, verification evidence, claim wording. |
| [`docs/roadmap.md`](docs/roadmap.md) | Strategic depth-vs-breadth framing and the tactical phase log. |
| [`docs/values-review.md`](docs/values-review.md) | The judgment layer: the eight review lenses and the upgrade log. |
| [`docs/bridges.md`](docs/bridges.md) · [`docs/leaps.md`](docs/leaps.md) · [`docs/patterns.md`](docs/patterns.md) | The Foundations→pricing bridges, the deductive leaps, and distilled Lean proof patterns. |

## Contributing · citation · license

Contributions welcome — see [`CONTRIBUTING.md`](CONTRIBUTING.md) and the
[good first issues](https://github.com/raphaelrrcoelho/formal-mathfin/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22).
Please cite via the [Zenodo DOI](https://doi.org/10.5281/zenodo.20477782) or the
[paper](https://arxiv.org/abs/2606.01356) ([`CITATION.cff`](CITATION.cff)). Licensed under
[Apache 2.0](LICENSE).
