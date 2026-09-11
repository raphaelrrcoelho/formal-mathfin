# Mathematical finance, formally verified

[![build](https://github.com/formal-applied-math/formal-mathfin/actions/workflows/build.yml/badge.svg)](https://github.com/formal-applied-math/formal-mathfin/actions/workflows/build.yml)
[![axioms](https://img.shields.io/badge/axioms-propext%2C%20Classical.choice%2C%20Quot.sound-blue)](MathFin/AxiomAudit.lean)
[![blueprint](https://img.shields.io/badge/blueprint-deductive_spine-blue)](docs/blueprint.md)
[![Lean](https://img.shields.io/badge/Lean-4.32.0-blue)](lean-toolchain)
[![license](https://img.shields.io/badge/license-Apache_2.0-blue)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20477781.svg)](https://doi.org/10.5281/zenodo.20477781)
[![arXiv](https://img.shields.io/badge/arXiv-2606.01356-b31b1b)](https://arxiv.org/abs/2606.01356)
[![dataset](https://img.shields.io/badge/HF-dataset-ffcc4d)](https://huggingface.co/datasets/formal-applied-math/formal-mathfin-theorems)
[![PRs welcome](https://img.shields.io/badge/PRs-welcome-brightgreen)](CONTRIBUTING.md)
[![Contributor Covenant](https://img.shields.io/badge/Contributor%20Covenant-2.1-4baaaa)](CODE_OF_CONDUCT.md)

> A Lean 4 library building toward a **formal theory of mathematical finance** — every result
> machine-checked against [Mathlib](https://github.com/leanprover-community/mathlib4) and
> [Degenne's BrownianMotion](https://github.com/RemyDegenne/brownian-motion), with an exact statement of
> what is proved and what is assumed, and the deep connections between the field's pillars made
> *load-bearing* rather than decorative.

**`372` theorems · `359` delivery-ready · `0` sorries · axioms-clean · `lake build` is the proof.**

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
  ledger](verification_ledger.json) records exactly what each was checked under; a machine-generated
  [`formalization.yaml`](formalization.yaml) self-report discloses how each result was produced; and a
  multi-agent [values review](docs/values-review.md) runs on a CI-enforced cadence. The README does not
  claim a result the kernel has not accepted.

## The architecture — the field's spine

Mathematical finance is a few deep principles whose consequences are the models. The library has the
**four pillars**; the active program is to make the **connective tissue** between them load-bearing.

| Pillar | The principle | In the library |
|---|---|---|
| **I — No-arbitrage as convex duality** | the separating hyperplane *is* the equivalent martingale measure | the FTAP tower · [`ConvexDuality`](MathFin/Foundations/ConvexDuality.lean) · state prices |
| **II — Stochastic calculus** | every model is `dX = b dt + σ dB`; Itô makes functionals computable | the Itô tower: from-scratch L² integral, Itô's formula, quadratic variation, and its jump analogue — and it *names* the `σ`, down to `dŜ = σŜ dB` for the discounted price |
| **III — Probabilistic ⟷ analytic duality** | the price is both a risk-neutral expectation and a PDE solution | the BS-PDE keystone (Feynman–Kac and Itô routes) |
| **IV — Intensity & exponential families** | closed forms and the "exp of an integrated intensity" | Gaussian closed forms · the exponential-discount root · credit/mortality unification |

**The bridges are where the depth lives** — each makes two pillars one theorem:

| Bridge | Connects | Status |
|---|---|---|
| **Convex duality** | I ↔ IV (pricing ↔ risk) | ✅ **WIRED** — the FTAP and the coherent-risk representation are proved to be the *same* Hahn–Banach theorem |
| **Feynman–Kac** | II ↔ III | ✅ **WIRED** — the Black–Scholes PDE from the risk-neutral expectation |
| **Lattice limit (CLT)** | discrete ↔ continuous | ✅ **WIRED** — CRR binomial → Black–Scholes, by characteristic functions and Lévy continuity through put-call parity. Donsker's invariance principle itself is *not* formalized; this seam is the pricing limit, not the functional CLT |
| **Numéraire** | IV ↔ I | ✅ **WIRED** — the price-invariance seam `N₀·𝔼^{Qᴺ}[X/N_T] = B₀·𝔼^Q[X/B_T]` (`changeOfNumeraire`), with BS-stock / Margrabe-`S²` / Kelly-EMM instances |
| **Girsanov** | I ↔ II | ✅ **WIRED** — the EMM is an *explicit* change of measure, and the distributional Girsanov is closed for **bounded** predictable θ: `B^θ` is a `Q`-Brownian motion in full — zero start, Gaussian **and** independent increments. That is strictly inside the integrand class: `itoIntegralCLM_T` is defined on all of `L²`-predictable, and boundedness is a real extra hypothesis, so unbounded `L²`/progressive θ is open, as is Novikov's condition itself ([scope](#scope-whats-not-done)) |
| **Martingale representation** | I ↔ II | ✅ **WIRED** — the same seam from the other side: the Itô integral is proved *onto* the centered `𝓕ᴮ_T`-measurable claims, so every square-integrable claim has a unique hedge, and (since 2026-08-16, via the Itô chain rule) that hedge is a holding in the **price** and the pricing measure is pinned without assuming gains-neutrality — from a square-integrable density plus the price being a `Q`-martingale |

→ The full spine, seam by seam: **[`docs/mathematical-architecture.md`](docs/mathematical-architecture.md)**.

## Landmark results

| Result | Statement | Lean |
|---|---|---|
| **Pricing = risk, one theorem** | the FTAP separating functional and the coherent-risk representation are the same finite-dimensional Hahn–Banach separation | [`exists_pos_separating_of_cone_disjoint_simplex`](MathFin/Foundations/ConvexDuality.lean) · [`coherentRisk_isLUB`](MathFin/RiskMeasures/AcceptanceSet.lean) |
| **BS PDE from Feynman–Kac** | the Black–Scholes PDE derived from the risk-neutral expectation by heat-kernel differentiation — independent of the closed form and of Itô | [`bsV_satisfies_bs_pde_via_feynmanKac`](MathFin/BlackScholes/PDEFromFeynmanKac.lean) |
| **CRR → Black–Scholes** | the n-step binomial call price converges to `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)` (characteristic functions + Lévy continuity + put-call parity), under no-arbitrage at every step with `n ≥ 1` — a hypothesis [`binomialNoArb_crr`](MathFin/Binomial/CRRConvergence.lean) discharges whenever `\|r\|·√T < σ` | [`binomialPrice_call_tendsto_bs_closed`](MathFin/Binomial/CRRClosedForm.lean) |
| **Continuous-time Itô formula** | `f(T,B_T) − f(0,B_0) − ∫₀ᵀ(f_t + ½f_xx) ds` is a continuous **local martingale** — Itô's lemma as a semimartingale decomposition — for a general `C³` `f` with no growth bound, on a from-scratch L² Itô integral. Where the partials are bounded, that residual is *identified*: `= ∫₀ᵀ f_x(s,B_s) dB_s` | [`ito_formula_unrestricted`](MathFin/Foundations/ItoFormulaUnrestrictedLocMart.lean) · [`ito_formula_td_L2_bddDeriv`](MathFin/Foundations/ItoFormulaTD.lean) |
| **GBM decomposed, coefficients named** | `dŜ = σŜ dB + mŜ dt` for `Ŝ(t) = S₀e^{(m−σ²/2)t+σB_t}`, the stochastic term the genuine Itô integral of a *named* integrand — so the diffusion coefficient of the discounted price is sayable, not merely known to exist | [`ito_formula_gbm`](MathFin/Foundations/ItoFormulaGBM.lean) · [`discountedGBM_eq_itoIntegral`](MathFin/Foundations/ItoFormulaGBM.lean) |
| **The EMM via Girsanov** | the risk-neutral measure is *constructed* as an explicit density change of the physical measure; the discounted stock is a proven `Q`-martingale — retiring the Wald shortcut | [`bs_discounted_isQMartingale`](MathFin/Foundations/Girsanov.lean) |
| **Itô–Lévy L² isometry** | the compensated-Poisson stochastic integral built to an L²-isometric continuous linear operator, on a from-scratch density argument | [`assembly_isometry`](MathFin/Foundations/PoissonCompensatedIntegralOperator.lean) |
| **SDE existence + uniqueness** | the Picard contraction in the predictable `L²` space, and pathwise uniqueness by an `L²`-energy Grönwall argument | [`picardMap_contraction`](MathFin/Foundations/SDEExistence.lean) · [`IsL2SolutionPair.uniqueness`](MathFin/Foundations/SDEUniqueness.lean) |
| **Martingale representation** | the Itô integral `φ ↦ ∫₀ᵀ φ dB` is onto the centered `𝓕ᴮ_T`-measurable part of `L²(μ)` — by orthogonal decomposition against its closed range plus totality of the step Doléans exponentials, with no Malliavin calculus; the finance reading is that every square-integrable claim has a unique hedge | [`itoIntegralCLM_T_surjective_onto_centered`](MathFin/Foundations/MartingaleRepresentation.lean) · [`exists_replicating_strategy`](MathFin/Foundations/MarketCompleteness.lean) |
| **Jump risk is never free** | the Merton (1976) jump-diffusion price dominates Black–Scholes | [`bsV_le_mertonCallPrice`](MathFin/BlackScholes/MertonDominance.lean) |
| **A reified capped call, priced by composition** | a reified capped call — built by composing two reified European-call contracts, long at `K₁` and short at `K₂`, rather than written as one more inline payoff — whose Black–Scholes value is the difference of two European call values, by linearity of `Contract.value` alone; no third integral is touched. Contract-reification framing after Bilokon 2026 ([`docs/sources.md`](docs/sources.md)) | [`value_cappedCall`](MathFin/Contracts/CappedCall.lean) · [`cappedCall_payoff_eq`](MathFin/Contracts/CappedCall.lean) |

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
| theorems (machine-checked) | **372** |
| delivery-ready (`full` + `library_wrapper`) | **359** |
| full derivations | 341 |
| library wrappers | 18 |
| reduced cores (honest special cases) | 13 |
| placeholders / sorries | **0** |
| Lean modules · lines of Lean | 459 · ~83,100 |
| verification ledger | 372 fresh, 0 stale |
| axioms used | `propext, Classical.choice, Quot.sound` only |
| Lean / Mathlib / BrownianMotion | `v4.33.0-rc1` / `0434c033` / `314f04a`, pinned ([`lean-toolchain`](lean-toolchain), [`lake-manifest.json`](lake-manifest.json)) — a Lean **release candidate**, tracking BrownianMotion, which has not moved to a stable `v4.33.x` |

The library is organized by theme under [`MathFin/`](MathFin): `Foundations/` (138 modules — the
stochastic core), `BlackScholes/` (224), `FixedIncome/` (24), `Binomial/` (18), `Portfolio/` (14),
`RiskMeasures/` (10), `Actuarial/` (6), `Contracts/` (5), `Performance/` (5), `Futures/` (3),
`Bridges/` (2), `DeFi/` (1), `Execution/` (2).

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

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for the full workflow and
[`docs/onboarding.md`](docs/onboarding.md) for a guided path into the codebase.

## How verification works

- **The build is the proof.** `lake build` re-elaborates every theorem against the pinned toolchain; a
  clean exit is the canonical verification.
- **Axiom audit.** [`AxiomAudit.lean`](MathFin/AxiomAudit.lean) (headliners) and
  [`AxiomAuditGen.lean`](MathFin/AxiomAuditGen.lean) (generated over the whole corpus) pin `#print axioms`
  as `#guard_msgs` build invariants — no `sorry`, no project-local axioms.
- **Verification ledger.** [`verification_ledger.json`](verification_ledger.json) records the input-hash
  (snippet + transitive imports + toolchain pins) each entry last verified under; only entries whose
  inputs changed re-run.
- **Kernel replay.** A `leanchecker` job re-checks proof terms *below* the elaborator. It is
  best-effort and `workflow_dispatch`-only: the full-Mathlib environment does not fit in a 16 GB
  hosted runner, and the README says so rather than implying a green replay it cannot run.
- **CI gates.** Every push runs the Python gates (status taxonomy, forbidden tactics, ledger freshness,
  generated-artifact freshness) and the environment linter *before* the Lean build.
- **Values review.** Sessions that change proof content close with a multi-agent review over eight
  judgment lenses, logged in [`docs/values-review.md`](docs/values-review.md). It is an upgrade engine
  producing a ranked backlog, not a pass/fail stamp; only its cadence is machine-enforced.

## Provenance — who proved what

Some entries are drafted by an automated pipeline rather than by hand, and the library says which.
[`formalization.yaml`](formalization.yaml) is generated from the corpus (never hand-edited, freshness
CI-enforced) and records the methods in use: interactive human authoring, and a two-stage machine
autoformalization loop that drafts a statement, gates it adversarially, and proves it. Machine-drafted
entries carry a `provenance` marker in their benchmark entry, so the disclosure is counted from the
corpus rather than asserted.

Automation is held to the same bar as hand-authored work: a proof that a machine found is refactored to
the conceptually right argument before it merges, and a statement that is *faithful but empty* — an
instantiation of an already-∀-quantified lemma, or a Mathlib result restated in finance names — is
rejected rather than counted.

## What's covered

A breadth-and-depth library across eleven areas. Headlines per area (full per-theorem audit + status in
[`docs/coverage.md`](docs/coverage.md)):

- **Black–Scholes & exotics** — the full Greek matrix (δ, γ, vega, θ, ρ, vanna, volga, charm), digitals,
  BS-Merton dividends, Garman–Kohlhagen FX, implied-vol uniqueness, the PDE, Breeden–Litzenberger;
  Margrabe exchange, chooser, capped/bull/butterfly, lookback, geometric-Asian, barrier parity, quanto.
- **Bachelier & Black-76** — arithmetic-BM pricing + Greeks; the futures-options formula + swaption.
- **Binomial / lattice** — replication + uniqueness, American/Bermudan via the Snell envelope, **CRR →
  Black–Scholes** convergence, Merton 1973 dominance, André's reflection principle, barrier/lookback.
- **Fixed income & credit** — bonds, duration/convexity, Redington immunization, yield-curve bootstrap,
  zero-coupon and forward rates, FRAs, vanilla interest-rate swaps, the T-forward measure, reduced-form
  hazard credit, first-to-default, Vasicek (ODE + SDE law), KMV–Merton default.
- **Portfolio & performance** — Markowitz (2- and N-asset), CAPM + equilibrium, two-fund separation,
  risk parity, Black–Litterman, tangency; Sharpe/Sortino/Treynor/Information ratios, Kelly.
- **Risk measures** — Gaussian VaR/CVaR closed forms, the coherent (ADEH) axioms + **the representation
  as a sup over measures**, spectral measures, Rockafellar–Uryasev, Herfindahl–Hirschman.
- **Stochastic foundations** — the **Itô tower** (from-scratch L² integral, isometry, quadratic
  variation, Itô's formula — stating *which* integrand, down to `dŜ = σŜ dB` for geometric Brownian
  motion) and its jump analogue, the **compensated-Poisson (Itô–Lévy) integral** built
  to an L²-isometric continuous linear operator, the **SDE tower** (Picard existence, `L²`-Grönwall
  uniqueness, pathwise decomposition), the **FTAP tower** (finite-Ω multi-period, general-Ω one-period,
  d-asset), Girsanov, **martingale representation** and the market completeness it delivers,
  Feynman–Kac, and **the convex-duality unification**.
- **Market microstructure** — the Avellaneda–Stoikov market-making problem: the Riccati value function,
  its approximate-HJB solution, and the constant half-spread / linear-skew closed forms, single-asset
  and multi-asset (matrix Riccati by spectral reduction); and the **Glosten–Milgrom**
  adverse-selection spread, derived from the trader mix, with the quotes posited as Bayesian
  conditional expectations of the value given the order's direction rather than derived from a
  competitive market maker's zero expected profit.
- **Contract reification** — a payoff language (`Payoff`/`Contract` over a typed underlying index)
  separating *what an instrument pays* from *the model that prices it*, with evaluation proved
  measurable, and the reified European call, put, cash-or-nothing digital and capped call reduced to
  the closed forms the library already proves — the capped call by **composing** two European call
  values, no third integral. Framing after Bilokon 2026 ([`docs/sources.md`](docs/sources.md)).
- **Actuarial & DeFi** — Gompertz mortality, survival models, annuities, net premium, compound-Poisson
  MGF; constant-product (Uniswap-v2) AMMs.

## Scope: what's not done

Honesty is the point, so the gaps are explicit:

- **13 `reduced_core` entries** — special cases or algebraic/structural cores whose fully general form is
  not yet formalized (the 2-D Itô formula, Lévy's characterisation, Novikov's condition, the
  fully-general `L²`/progressive Girsanov, some Markov/Poisson cores). Tracked per-entry in
  [`docs/coverage.md`](docs/coverage.md).
- **18 `library_wrapper` entries** — thin restatements consuming a Mathlib/BrownianMotion lemma. They are
  delivery-ready but are not original derivations, and are counted separately for that reason.
- **Girsanov's general case, and Novikov separately.** The ladder is closed through bounded
  predictable θ (constant → simple-adapted → adapted-continuous → predictable). That is *narrower*
  than the integrand class the ladder is built on: `itoIntegralCLM_T` maps all of `Lp ℝ 2 (trimMeasure_T T)`,
  and on a finite measure `L² ⊋ L^∞`, so a square-integrable predictable θ need not be bounded.
  Unbounded, merely progressively-measurable θ remains open. **Novikov's condition is not derived either** — its entry is a structure spec carrying a
  uniform `L¹` bound in place of `𝔼[exp(½∫₀ᵀθ²ds)] < ∞` (the genuine condition needs `∫θ dB`, and no θ
  or `B` appears in the structure), so the martingale conclusion is read off by projection. The open
  case is therefore *two* gaps, not one hypothesis away from a proved theorem.
- **The second FTAP is not proved unconditionally.** Since 2026-08-16 gains-neutrality is no longer
  an assumption: for the discounted price `S = S₀ + (σ●B)` with `σ ≠ 0` a.e., a probability measure
  `Q = D·μ` with a **square-integrable density** `D ∈ L²(μ)`, under which `S` is a martingale,
  prices the traded gains at zero and hence agrees with `μ` on `𝓕ᴮ_T`. What remains conditional is
  that density hypothesis — it is what makes the pricing functional continuous and this argument
  does not remove it — together with `σ ≠ 0` and a **driftless** price. Only `complete ⟹ unique` is
  delivered; the converse needs the Jacod–Yor extreme-point characterisation. The earlier statement,
  which took `PricesGainsAtZero` outright, is still in the library and still true.
- **The replicating hedge is unique but unnamed.** For a general square-integrable claim, market
  completeness gives a unique `φ` with `H = 𝔼[H] + ∫₀ᵀ φ dB` and says nothing about what `φ` is.
  Naming it is Clark–Ocone ([#182](https://github.com/formal-applied-math/formal-mathfin/issues/182)) and
  is open. The Itô *formula's* integrand is named throughout — that is how `dŜ = σŜ dB` is stated —
  but that is the weaker of the two facts.
- **The contract layer is a payoff kernel, not a legal instrument.** `MathFin/Contracts/` reifies
  what an instrument *pays* over a finite observation grid, single-asset. Calendars, business-day
  conventions, market disruption, corporate actions and issuer credit are absent from the language and
  are not claimed; nor is a lifecycle layer (branching contracts, outstanding notional, termination),
  which waits on the first callable instrument to force it. One theorem in that tower —
  `Payoff.measurable_eval_of_obsTimes_le`, the filtration-indexed *adapted* variant — still has no
  consumer, because nothing yet integrates a contract against a filtration; its a.e.-measurable
  sibling is consumed.
- **Known upstream/limit gaps** — e.g. the superhedging strong-duality *equality* needs a
  finite-dimensional Farkas / polyhedral-cone closedness absent from Mathlib at this pin
  ([#39](https://github.com/formal-applied-math/formal-mathfin/issues/39)).

The frontier is in the [open issues](https://github.com/formal-applied-math/formal-mathfin/issues) and
[`docs/roadmap.md`](docs/roadmap.md). For genuinely *unsolved* problems — as opposed to unformalized
known mathematics — [`docs/open-problems.md`](docs/open-problems.md) is a survey built over three
adversarial rounds, where each entry carries an evidence class and the date of the most recent source
asserting it is still open.

## Documentation

| File | Contents |
|---|---|
| [`docs/mathematical-architecture.md`](docs/mathematical-architecture.md) | **The field's spine** — the four pillars, the connective bridges, and which seams are wired vs open. |
| [`docs/architecture.md`](docs/architecture.md) | The engineering design: structural-principle modules, the three honesty tiers, the bridge methodology. |
| [`docs/blueprint.md`](docs/blueprint.md) | The deductive spine — a dependency graph from Brownian motion to Black–Scholes, each node linked to its proof. |
| [`docs/coverage.md`](docs/coverage.md) | Per-theorem audit: faithfulness status, verification evidence, claim wording. |
| [`docs/open-problems.md`](docs/open-problems.md) | Unsolved problems in the field, by evidence class, with where this library has leverage. |
| [`docs/roadmap.md`](docs/roadmap.md) | Strategic depth-vs-breadth framing and the tactical phase log. |
| [`docs/hjm-program.md`](docs/hjm-program.md) | The HJM formalization program: stochastic Fubini as a shared primitive, the drift condition as its consumer. |
| [`docs/values-review.md`](docs/values-review.md) | The judgment layer: the eight review lenses and the upgrade log. |
| [`docs/onboarding.md`](docs/onboarding.md) · [`docs/troubleshooting.md`](docs/troubleshooting.md) | Getting in, and getting unstuck. |
| [`docs/sources.md`](docs/sources.md) | External formalisations and papers this library has learned from: what was taken from each, what was not, and where the credit lives in the code. |
| [`docs/bridges.md`](docs/bridges.md) · [`docs/leaps.md`](docs/leaps.md) · [`docs/patterns.md`](docs/patterns.md) | The Foundations→pricing bridges, the deductive leaps, and distilled Lean proof patterns. |

## Contributing · citation · license

Contributions welcome — see [`CONTRIBUTING.md`](CONTRIBUTING.md) and the
[good first issues](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22).
Please cite via the [Zenodo DOI](https://doi.org/10.5281/zenodo.20477781) or the
[paper](https://arxiv.org/abs/2606.01356) ([`CITATION.cff`](CITATION.cff)). Licensed under
[Apache 2.0](LICENSE).
