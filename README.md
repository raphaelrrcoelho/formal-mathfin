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

A Lean 4 library of machine-checked mathematical-finance theorems, built on Mathlib
and Degenne's BrownianMotion. 295 theorems across 11 areas — Black-Scholes
with the full Greek matrix, the exotics, and Merton jump-diffusion, binomial
trees with American / Bermudan / Snell envelope, fixed income with hazard
credit, first-to-default baskets, and Vasicek SDE, portfolio theory from
Markowitz to Black-Litterman, coherent risk measures, Kelly, mortality, and
constant-product AMMs.

The aim is a comprehensive, honest reference for formally-verified
mathematical finance: broad coverage, and — for every result — an exact
statement of what is proved and what is assumed.

Public artifacts: [paper (arXiv:2606.01356)](https://arxiv.org/abs/2606.01356),
[Zenodo DOI](https://doi.org/10.5281/zenodo.20477782), and
[Hugging Face theorem dataset](https://huggingface.co/datasets/raphaelrrcoelho/formal-mathfin-theorems).

|  | count |
|---|---:|
| total theorems | 295 |
| **full derivations** | **259** |
| library wrappers | 18 |
| reduced cores | 17 |
| placeholders | **0** |

**278 of the 295 are delivery-ready** (`full` + `library_wrapper`); the 17
`reduced_core` entries are honest special cases or algebraic/structural cores
of results whose general form is not yet formalized here (see *What's not
done*).

Every `full` derivation depends only on the three Mathlib standard axioms
`[propext, Classical.choice, Quot.sound]` — there is no `sorry` and no
project-local axiom anywhere in the library. For the load-bearing derivations
(~115 declarations) this is `#print axioms`-pinned as a build invariant in
`MathFin/AxiomAudit.lean`.

## Landmark results

| | statement | where |
|---|---|---|
| **BS PDE from Feynman–Kac** | the Black–Scholes PDE derived from the risk-neutral expectation via heat-kernel differentiation — independent of the closed-form check and of Itô | [`bsV_satisfies_bs_pde_via_feynmanKac`](MathFin/BlackScholes/PDEFromFeynmanKac.lean) |
| **CRR → Black–Scholes** | the n-step binomial call price converges to `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)` (characteristic functions + Lévy continuity + put-call parity) | [`binomialPrice_call_tendsto_bs_closed`](MathFin/Binomial/CRRClosedForm.lean) |
| **Continuous-time L² Itô formula** | `f(B_T) − f(B_0) = ∫₀ᵀ f′(B_s) dB_s + ½ ∫₀ᵀ f″(B_s) ds` on a from-scratch L² Itô integral (time-dependent variant included) | [`ito_formula_L2_bddDeriv`](MathFin/Foundations/ItoFormulaCLM.lean) |
| **The EMM is a theorem** | static Girsanov via an Esscher tilt *constructs* the risk-neutral measure from the physical one; the discounted asset is a proven `Q`-martingale | [`BSCallHyp.exists_of_physical`](MathFin/Foundations/GaussianGirsanov.lean) · [`discountedGBM_isMartingale`](MathFin/Foundations/ContinuousFTAP.lean) |
| **Jump risk is never free** | the Merton (1976) jump-diffusion price dominates Black–Scholes, with the classic `Λ′ = Λ(1+k)` weights display | [`bsV_le_mertonCallPrice`](MathFin/BlackScholes/MertonDominance.lean) |
| **André's reflection principle** | the hitting-path bijection, with a discrete IVT discharging the reflected-side hitting condition — the counting backbone of barrier pricing | [`reflectionPrincipleEquiv_below`](MathFin/Binomial/PathReflection.lean) |

## At a glance

```lean
-- MathFin/BlackScholes/PDE.lean — BS delta via the magic identity
lemma hasDerivAt_bsV_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s => bsV K r σ s τ) (Phi (bsd1 S K r σ τ)) S := by
  have h_d1_S := hasDerivAt_bsd1_S (r := r) hK hσ hτ hS
  have h_d2_S := hasDerivAt_bsd2_S (r := r) hK hσ hτ hS
  have h_Phi_d1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp S h_d1_S
  have h_Phi_d2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp S h_d2_S
  have h_V := (hasDerivAt_id S).mul h_Phi_d1
              |>.sub (h_Phi_d2.const_mul (K * Real.exp (-(r * τ))))
  have h_bs := bs_identity (r := r) hS hK hσ hτ
  ...; field_simp; linear_combination -h_bs
```

The `bs_identity` magic-identity collapse drives delta, gamma, theta, vega,
rho, vanna, volga, and the BS PDE forward direction. See
[`MathFin/Examples.lean`](MathFin/Examples.lean) for a curated
five-proof tour.

## Quick start

```bash
# Pull the pinned image (~3 min) instead of building locally (~15 min)
docker compose -f docker/docker-compose.yml pull verify

# Build the entire library — clean exit means every theorem typechecks
docker compose -f docker/docker-compose.yml run --rm --entrypoint bash verify -lc 'lake build'

# Run a benchmark chapter
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/mathematical_finance.json
```

Fast authoring loop (5–30s feedback via persistent REPL daemon):

```bash
docker compose -f docker/docker-compose.yml up -d lean-repl
./scripts/lean-check.sh MathFin/<Section>/<Module>.lean
```

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for the full development workflow.

## How verification works

- **The build is the proof.** `lake build` from the repo root re-elaborates
  every theorem against the pinned toolchain; a clean exit is the canonical
  verification.
- **Axiom audit.** [`MathFin/AxiomAudit.lean`](MathFin/AxiomAudit.lean)
  (curated headliners) and [`MathFin/AxiomAuditGen.lean`](MathFin/AxiomAuditGen.lean)
  (generated over the whole corpus) pin `#print axioms` output as
  `#guard_msgs` build invariants — no `sorry`, no project-local axioms, only
  the three Mathlib standard axioms.
- **Verification ledger.** [`verification_ledger.json`](verification_ledger.json)
  records the input-hash (snippet code + transitive imports + toolchain pins)
  each of the 295 benchmark entries last verified under; only entries whose
  inputs changed ever re-run.
- **CI gates.** Every push runs the Python gates (status taxonomy, forbidden
  tactics, a definitional-`rfl` tripwire, blueprint ⊆ audit, ledger
  freshness) *before* the Lean build.
- **Values review.** Sessions that add or change proof content close with a
  multi-agent review panel over eight judgment lenses (inspired math,
  upstream coherence, zero slop, architecture, first principles, idiomatic
  register, concept clarity, elegance); verdicts are logged in
  [`docs/values-review.md`](docs/values-review.md), and a CI cadence test
  fails if the corpus outgrows the last verdict.

## What's covered

| Area | Headline results |
|---|---|
| **Black-Scholes** | Call, put, digital (cash + asset) + parity; full Greek matrix (δ, γ, vega, θ, ρ, vanna, volga, ψ); BS-Merton with dividends; Garman-Kohlhagen FX; implied vol uniqueness + bisection bracket; PDE forward direction; strike Greeks (∂_K, ∂²_K); static price bounds; box-spread arbitrage; lognormal moments + n-th moment + power forward; variance swap fair strike (closed-form + QV-limit); Breeden-Litzenberger implied risk-neutral PDF; PDE re-derived from Feynman–Kac (heat-kernel route). |
| **Exotics** | Chooser via PCP; capped call = bull spread; bull-spread + butterfly non-negativity; lookback ≥ vanilla; two-date geometric ≤ arithmetic Asian; **Margrabe exchange option** (multivariate — effective vol `√(σ₁²+σ₂²−2ρσ₁σ₂)`, parity, and the price as a `bs_call_formula` call on the ratio). |
| **Bachelier** | Arithmetic-BM option pricing with the truncated-mean primitive; full first-order Greeks. |
| **Black-76 (Futures)** | Black-76 formula via zero-drift specialisation + full Greek matrix; swaption. |
| **Binomial trees** | Single-period replication + uniqueness; multi-period backward induction; American options (Snell envelope characterisation); **CRR → Black-Scholes** convergence (binomial call price → the BS closed form `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)`, via characteristic functions + Lévy continuity + put-call parity); **Bermudan sandwich** (European ≤ Bermudan ≤ American); **Merton 1973** strict dominance bsV > S − K (American = European for non-dividend call); **André's reflection principle** with full bijection. |
| **Fixed income** | ZCB + duration + convexity; coupon bond pricing + YTM monotonicity; annuity geometric-series closed form; flat + non-flat forward/spot rate consistency; Macaulay vs modified duration; first- + second-order Redington immunization; yield-curve bootstrap; reduced-form credit (constant + time-varying hazard); Vasicek deterministic ODE + SDE terminal distribution; **KMV-Merton** structural default. |
| **Portfolio theory** | 2-asset Markowitz (completing-the-square); N-asset Markowitz (Finset double sum, diagonal, iid diversification, PSD bound); **N-asset Lagrangian** FOC characterisation; CAPM (β + portfolio linearity) + **equilibrium derivation**; two-fund separation (CML + Sharpe invariance); **risk parity** equal-contribution (log-barrier FOC); **Black-Litterman** 1-D + **N-dim normal-equation** posterior; tangent portfolio FOC. |
| **Performance ratios** | Sharpe (full affine invariance, √T scaling); Sortino; Treynor; Information ratio; tracking error; Kelly criterion (FOC, horizon myopia, fraction bounds, sign analysis). |
| **Risk measures** | Gaussian VaR / CVaR closed forms; coherent axioms (translation, homogeneity, monotonicity, subadditivity) **verified on the gaussian closed form** (acceptance-set convexity is separately derived from concave utility in `UtilityDerivation.lean`); joint-stdev triangle; VaR/CVaR additivity at ρ=1; **Rockafellar-Uryasev** algebraic form; spectral risk measures; **Herfindahl-Hirschman** with Cauchy-Schwarz lower bound. |
| **Actuarial** | Annuity-due closed form; net premium principle; **Gompertz** cumulative force of mortality. |
| **DeFi** | Constant-product AMM (Uniswap v2) invariants — adapted from Pusceddu-Bartoletti. |
| **Foundations** | **Static Girsanov** — the risk-neutral measure *derived* from the physical measure via an Esscher density, making `BSCallHyp` a theorem and the discounted asset a proven `Q`-martingale ([`docs/leaps.md`](docs/leaps.md)); Brownian motion martingales (square-sub-time, Wald exponential); Wiener integral + L² version; **the adapted Itô isometry** — the genuinely-stochastic `E[(Σ φₖ·ΔBₖ)²]=Σ E[φₖ²]·Δtₖ` for *random adapted* integrands, cross-terms killed by the weak Markov property (`∫B dB` capstone) ([`docs/leaps.md`](docs/leaps.md)); quadratic variation; Doob L^p continuous-time convergence; conditional Jensen; **discrete Itô lemma** (after Nagy); simple Itô integral; **FTAP tower** (two-state explicit EMM; multi-state single-period biconditional; **multi-period finite-Ω biconditional** NA ⟺ ∃ EMM via geometric Hahn–Banach separation, `ftap_discrete`; **general-Ω one-period scalar** NA ⟺ ∃ EMM via bounded-density reduction, `ftap_one_period`; **d-asset one-period** NA ⟺ ∃ EMM for any finite-dimensional market via Esscher/softplus minimisation on the gains kernel, `ftap_one_period_vector`; open rung: general-Ω multi-period DMW); pricing kernels; state prices; Itô structural drift (GBM log-drift, log return mean); BS PDE from Itô + no-arbitrage; **the Black–Scholes PDE re-derived from Feynman–Kac** — the heat kernel's joint Fréchet-differentiability makes the orphaned `feynmanU` heat-flow load-bearing for pricing (closing the two-tower gap). |

The library leans on seven **structural-principle modules** where one named
fact generates dozens of one-line corollaries (Garman normal form, price
bounds, K-convexity at three scales, convex pricing functional, standard
gaussian MGF, exponential discount, Snell envelope). See
[`docs/architecture.md`](docs/architecture.md) for the full catalogue.

## Documentation

| File | Contents |
|---|---|
| [`docs/blueprint.md`](docs/blueprint.md) | **The deductive spine** — a dependency graph from Brownian motion to Black–Scholes (the risk-neutral measure *derived*, the Itô gate marked), each node linked to its Lean proof. |
| [`docs/coverage.md`](docs/coverage.md) | Per-theorem audit: faithfulness status (`full` / `library_wrapper` / `reduced_core` / `placeholder`), verification evidence, claim-wording guidance. |
| [`docs/architecture.md`](docs/architecture.md) | Design principles: structural-principle modules, the three-tier honesty model, the Foundations → pricing bridge methodology. |
| [`docs/leaps.md`](docs/leaps.md) | Static Girsanov (EMM derived), the genesis cascade, and Margrabe's multivariate exchange option — the deductive arc that makes the risk-neutral measure a theorem. |
| [`docs/bridges.md`](docs/bridges.md) | Catalogue of bridges from `Foundations/` to pricing modules. |
| [`docs/patterns.md`](docs/patterns.md) | Distilled Lean / Mathlib proof patterns and anti-patterns from prior phases. |
| [`docs/roadmap.md`](docs/roadmap.md) | Strategic depth-vs-breadth framing and the tactical phase log. |
| [`docs/values-review.md`](docs/values-review.md) | The judgment layer: the eight review lenses and the per-round verdict log (cadence machine-enforced in CI). |
| [`upstream/`](upstream/) | Drafts of contributions to Mathlib, BrownianMotion, and Lean Zulip. |
| [`references/`](references/) | Source PDFs (Saporito notes, cited papers). |

## What's not done (yet)

17 of the 295 theorems are `reduced_core` — an honest special case or
algebraic/structural core of a result whose fully general form is not yet
formalized here. By area:

- **Itô calculus** (`stochastic_calculus`, 4): the two-dimensional Itô formula,
  Lévy's martingale characterisation, SDE existence + uniqueness, and Girsanov.
  (The one-dimensional path-wise Itô lemma, the quadratic variation of an Itô
  process, *and* the time-dependent Itô formula — constant σ, Lipschitz drift,
  explicit L² rates — are now `full`; see below.)
- **Girsanov** (`girsanov_finance`, 3).
- **Markov chains** (5): finite-state structural specifications, one of them a
  definitional identity pinned `reduced_core` by convention. No longer
  upstream-gated — Mathlib now ships the Ionescu–Tulcea trajectory-measure
  machinery (`Kernel.traj`).
- **Continuous-time Poisson processes** (1): the whole-sequence iid claim for
  interarrival times needs the strong Markov property. Its analytic core is
  derived (first interarrival proved exponential, memoryless factorisation
  proved from independent increments), and the marginal law, superposition,
  and thinning are now `full` — each from a new derived identity (Gamma-CDF
  difference, Poisson convolution, binomial-marking factorisation).
- **Fine Brownian path machinery** (3): path-wise reflection,
  nowhere-differentiability, law of iterated logarithm.
- **Actuarial algebra** (`mathematical_finance`, 1): the compound-Poisson MGF
  identity is pinned at its exponential-algebra core (demoted from `full` in
  values round 6); the genuine `E[e^{tS}] = exp(λ(M_X(t)−1))` needs the
  compound-sum conditioning step on top of `poisson_pgf`.

The continuous-time L²-adapted **Itô integral itself is built** — the bounded
linear map `itoIntegralCLM_T` on `[0,T]` (`Foundations/ItoIntegralCLM.lean`,
axioms-clean, with `∫₀ᵀ B dB = ½(B_T²−B₀²−T)` as its first consumer) — and on
top of it the **continuous-time L² Itô formula** `f(B_T)−f(B_0) =
itoIntegralCLM_T gf' + ½∫₀ᵀ f″(B_s) ds` is now `full`
(`Foundations/ItoFormulaCLM.lean`, `ito_formula_L2_bddDeriv`), derived from
primitives (weighted quadratic variation + vanishing Itô–Taylor remainder +
Riemann↔CLM bridge) and AxiomAudit-pinned. Its scope is `f ∈ C³` with bounded
`f′,f″,f‴`; the gap to the unrestricted-`C²` textbook statement is a
localization step (Summit C), not yet formalized. What remains gated beyond
that is the SDE / Lévy layer that builds on it. See
[`docs/roadmap.md`](docs/roadmap.md).

**Pathwise regularity of the general-integrand Itô integral** is now built on top
of the L² tower. The L²-valued process `t ↦ (φ●B)_t` admits a **continuous
modification on `[0,T]`**
(`Foundations/ItoIntegralProcessContinuousModification.lean`,
`exists_continuous_modification_itoProcess`): an honest sample-path process agreeing
a.e. with the L² value at each `t ≤ T` and a.s. continuous — the first sample-path
result for the *general* integrand, from Degenne's continuous-time Doob maximal
inequality + Borel–Cantelli on a fast subsequence. This is then upgraded to a genuine
**continuous local martingale**
(`Foundations/ItoIntegralProcessLocalMartingaleGeneral.lean`,
`exists_continuous_localMartingale_modification`): the everywhere-continuous
representative, adapted to the **null-augmented** Brownian filtration `𝓕ᴮ ⊔ 𝓝`,
satisfies Degenne's `IsLocalMartingale` interface. The measure-theoretic core is
`condExp_sup_nulls` — conditioning on the null augmentation agrees a.e. with
conditioning on `𝓕ᴮ` (the σ-algebra crux consuming Mathlib's
`eventuallyMeasurableSpace`). Both are axioms-clean and non-redundant with Degenne's
(sorry-backed) general càdlàg modification.

Finally the local martingale is extended to the **whole half-line `ℝ≥0`**
(`Foundations/ItoIntegralProcessLocalMartingaleInfinite.lean`,
`exists_continuous_localMartingale_modification_infinite`): the unbounded-horizon Itô
integral has an everywhere-continuous local-martingale representative modifying the
process at *every* `t`, not just on a fixed `[0,T]`. The per-horizon `[0,T=n]` continuous
local martingales are **glued** — horizon consistency (`itoProcessL2Inf_eq_itoProcessCLM`,
itself resting on a hand-built `[0,T]` clamp of Degenne's `SimpleProcess`) makes each a
modification of the *same* unbounded-horizon process, and
`indistinguishable_of_modification_on` agrees them on overlaps — into one path continuous
on all of `ℝ≥0`. Unlike the finite-horizon version there is no clamp: the martingale
property holds globally, supplied directly by the unbounded-horizon `L²` martingale through
`condExp_sup_nulls`. This is the continuous-time Itô integral as a continuous local
martingale on the entire time domain.

## Related upstream contributions

Drafted as part of this project (source under [`upstream/`](upstream/)):

- **Mathlib**: `gaussianReal_zero_one_Iic_neg`, `gaussianReal_zero_one_Ioi_toReal`, `exp_mul_gaussianPDFReal_zero_one`, `integral_exp_mul_gaussianPDFReal_zero_one_Ioi` (standard normal tail + completing-the-square primitives).
- **Remy Degenne's `brownian-motion`**: `IsFilteredPreBrownian.squareSubTime_isMartingale`, `IsFilteredPreBrownian.waldExponential_isMartingale` (the two textbook BM martingales).

## Reproducibility

The verify Docker image pins:

- Lean toolchain `4.31.0`
- Mathlib at commit `fabf563a7c95`
- Remy Degenne's `brownian-motion` library at commit `d6f23daf48f9`

These are frozen in [`lakefile.lean`](lakefile.lean) + [`lake-manifest.json`](lake-manifest.json) + [`lean-toolchain`](lean-toolchain) at the repo root.

## Acknowledgements

Three modules adapt published Lean 4 formalisations by other authors, with
explicit attribution headers on each file:

- `Foundations/DiscreteIto.lean` and `Foundations/FTAPTwoState.lean` adapt the discretization framework from Tamás Nagy, *"From Itô to Black-Scholes: A Machine-Verified Derivation in Lean 4"*, SSRN [6336503](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6336503), 2026.
- `DeFi/ConstantProductAMM.lean` adapts Pusceddu & Bartoletti, *"Formalizing Automated Market Makers in the Lean 4 Theorem Prover"*, [OASIcs FMBC 2024.5](https://doi.org/10.4230/OASIcs.FMBC.2024.5) (companion code: <https://github.com/dpusceddu/lean4-amm>); underlying economic theory from Bartoletti, Chiang, Lluch-Lafuente, *"A theory of Automated Market Makers in DeFi"*, LMCS 2022.

Adaptations re-implement these results in this library's framework
(real-valued, `gaussianReal`-based BS hypothesis rather than reconstructed
Itô integral, ℝ-positivity rather than `PReal` subtypes). Mathematical
content is unchanged; copyright on the specific adaptation is Raphael
Coelho (Apache 2.0); academic fair use covers the derivative-work
relationship.

## References

Saporito, *Stochastic Processes* (textbook chapter coverage, primary
source). Hull, *Options, Futures, and Other Derivatives*. Bodie / Kane /
Marcus, *Investments*. Fabozzi, *Fixed Income Mathematics*. McNeil / Frey /
Embrechts, *Quantitative Risk Management*. Demeterfi / Derman / Kamal,
*More Than You Ever Wanted to Know About Volatility Swaps* (1999).
Artzner / Delbaen / Eber / Heath, *Coherent Measures of Risk* (1999).
Kelly, *A New Interpretation of Information Rate* (1956). Tobin,
*Liquidity Preference as Behavior Towards Risk* (1958). Sharpe (1965),
Treynor (1965), Sortino-van der Meer (1991), Grinold-Kahn (1999),
Rockafellar-Uryasev (2000). Black-Scholes (1973), Merton (1973), Black
(1976), Bachelier (1900), Cox-Ross-Rubinstein (1979). Roncalli-Maillard
on risk parity, Black-Litterman (1992).

## Contributing

Contributions are welcome — from documentation fixes to new theorem
formalisations to upstream Mathlib PRs.

- [`CONTRIBUTING.md`](CONTRIBUTING.md) — full development workflow.
- [`docs/onboarding.md`](docs/onboarding.md) — step-by-step first-contribution
  walkthrough (environment setup, fast iteration loop, PR checklist).
- [`docs/troubleshooting.md`](docs/troubleshooting.md) — common setup failures
  and fixes.
- [Good first issues](https://github.com/raphaelrrcoelho/formal-mathfin/issues?q=is%3Aopen+label%3A%22good+first+issue%22)
  — labelled tasks with explicit scope, acceptance criteria, and file pointers.

Please read and follow our [Code of Conduct](CODE_OF_CONDUCT.md).

## License

Apache 2.0, per the header on each source file.
