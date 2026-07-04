# Mathematical-quality review — 2026-07-04 (whole corpus)

A whole-repo review under the **mathematical** values lenses — elegance, clarity,
reusability, use of Mathlib capabilities, genuine proof depth, and mathematical
ingenuity. This is the repo's own values-review instrument (`docs/values-review.md`,
the 8 lenses) applied comprehensively, and read as an **upgrade engine**: each
finding names the concrete current state and the concrete upgrade, and the
**exemplars** (the current ceiling per lens) are named and celebrated, not just the
gaps. It is distinct from, and complementary to, the code-craft pass
(`docs/idiomatic-review-2026-07-04.md`).

**Method.** Nine reviewers fanned out over disjoint *mathematical-theme* slices
(the Itô-integral construction, the Itô-formula tower, martingale/SDE/Feynman–Kac,
FTAP/convex/pricing, the probability leaves, BlackScholes, Binomial, FixedIncome,
Portfolio/Risk) — grouping by theme rather than directory so each reviewer could
spot *missed unifying abstractions*. Every top finding was re-verified by hand
against the source (and, where it names a Mathlib/Degenne lemma, against the vendored
`.lake` tree). Agent over-claims were checked, not trusted.

---

## Headline verdict

**The mathematics is genuinely excellent and the ceiling is high.** All nine
reviewers independently reported the same baseline: no `sorry`, no vacuity, no
grind-abuse, register uniformly high, and *many* proofs that are genuinely
beautiful — the Itô-vs-Wiener increment-independence core, the softplus/Esscher
FTAP, the Garman normal form unifying six pricing models, the Rockafellar–Uryasev
pointwise certificate, the covariance-PSD-from-self-dot-variance identity, and more
(full list below). Several proofs already *are* textbook instances of the repo's own
best patterns (`docs/patterns.md`).

So the upgrade axis is **not** fixing badness — it is **coherence and
consolidation**. Four honest sub-themes, in value order:

1. **Reusability / name-once** — the dominant theme. A dozen-plus proof skeletons are
   duplicated verbatim (or near-verbatim) across sibling files where one named lemma
   would serve all consumers.
2. **Mathlib-leverage** — a handful of places reinvent a Mathlib *abstraction*
   (`cdf`, `PosSemidef`, `ConcaveOn`, `convexOn_id.sup`, `Matrix.cramer`,
   `pow_le_of_le_one`) or a Degenne lemma (`uniformIntegrable_of_dominated_singleton`)
   that already exists.
3. **Missed unifying reductions** — a few concrete results that should be short
   corollaries of an abstraction the repo already owns (dynamic change-of-numéraire,
   the variance-swap L² concentration, put-strike convexity, the swaption).
4. **Honesty tightenings** — a small set of docstrings that promise more than the
   file proves (a good catch, all self-correctable).

The single most valuable cross-cutting recommendation (spanning three slices) is
**§Gaussian-facts home** below.

---

## §Gaussian-facts home — the top cross-cutting upgrade

Gaussian facts are scattered into model-specific files instead of living in
`Foundations/StandardNormal.lean` / `Foundations/GaussianCDFDeriv.lean`, forcing
reinvention and even cross-model imports. Consolidating them is one coherent PR that
touches the whole downstream:

| fact | currently in | should be in | consequence today |
|---|---|---|---|
| `Phi_le_one` | `BlackScholes/PriceBounds.lean:133` | `Foundations/StandardNormal` | `FixedIncome/KMVMerton` reinvents `Φ≤1` from scratch (M7) |
| `∫_s gaussianPDFReal = (gaussianReal s).toReal` | anon `have` ×6 (StandardNormal:150, Call:245, Put:52/167, Digital:108, Bachelier:266) | one `setIntegral_gaussianPDFReal_eq_toReal` in `StandardNormal` | proved 6× byte-identical (M5) — verified |
| `hasDerivAt_gaussianPDFReal_zero_one` (`ϕ'=-zϕ`) | `BlackScholes/Bachelier.lean:72` | `GaussianCDFDeriv` | `HigherGreeks`/`DigitalGreeks` `import …Bachelier` — a whole other pricing model — for one derivative (M5) |
| `gaussianPDFReal_zero_one_neg` (`ϕ(-z)=ϕ(z)`) | `BlackScholes/PutStrikeConvexity.lean:37` | `StandardNormal` (beside `Phi_neg`) | model-agnostic fact homed in a convexity file (M5) |
| `Phi := (gaussianReal 0 1 (Iic x)).toReal` | `StandardNormal.lean:49` | `Phi := ProbabilityTheory.cdf (gaussianReal 0 1)` | rolls a bespoke CDF; the exp leaves already use `cdf` — inherit `monotone_cdf`/`tendsto_cdf_at{Top,Bot}` for free (M4b) |

Doing this once removes the reinvention, deletes the spurious cross-model imports,
and makes `Φ` a Mathlib-`cdf`-shaped object (upstreamable).

---

## Reusability — name-once (dominant theme)

Ranked by value. All verified against source (occurrence counts hand-checked).

| # | sites | observation | upgrade | conf |
|---|---|---|---|---|
| R1 | `ItoIntegralCLM:725`, `WienerIntegralL2:418`, `ItoIntegralL2Dense:315` | the three `extendOfNorm` **isometry-norm** proofs are verbatim (`extendOfNorm_eq ⟨1,_⟩` + `induction_on` + `isClosed_eq (continuous_norm.comp I.continuous) …`) — **verified** | extract `LinearMap.norm_extendOfNorm_eq_of_isometry (h_dense)(h_isom)(y)`; pair with `denseRange_iff_orthogonal_range_eq_bot` (also ×3) as one isometric-extension package | 0.93 |
| R2 | `ZCB:58`, `Immunization:64`, `ConvexityImmunization:57` | the ZCB rate-derivative atom `d/dr[k·e^{−rΔ}] = −kΔ·e^{−rΔ}` hand-proved 3× (the portfolio files don't even `import ZCB`) | `import ZCB`; `(hasDerivAt_zcb_r t (Tᵢ) r).const_mul (wᵢ)` — *(overlaps idiomatic-review's deferred FIN2-ZCB item; the math agent supplies the cleaner path)* | 0.95 |
| R3 | `StrikeConvexity:154`, `SpotConvexity:111` | re-derive the sign facts already named in `GreekSigns` (`bsV_partial_KK_nonneg`, `bsV_gamma_pos`) — `GreekSigns` already applies this discipline to vega | `exact bsV_partial_KK_nonneg …` / `(bsV_gamma_pos …).le` | 0.93 |
| R4 | `CAPMEquilibrium:75` vs `MarkowitzNAsset:41` | `portfolioVariance` and `portfolioVarN` are the same double sum, **never identified** — so `CovariancePSD.covariance_kernel_psd` (a genuine first-principles PSD proof) is *unreachable* from every N-asset FOC file, which therefore can only *assume* PSD | one `portfolioVariance_eq_portfolioVarN` (`sum_congr;ring`) bridge transports PSD to the whole Lagrangian/risk-parity cluster | 0.82 |
| R5 | `QuadraticVariationL2`, `BrownianQuadraticVariation`, `BrownianMartingale` | the Brownian-increment Gaussian-law preamble (`HasLaw (Bₜ₁−Bₜ₀) (gaussianReal 0 (t₁−t₀))`) copied ~9× (26 `HasLaw`/`gaussianReal` occurrences — **verified**) | one `hasLaw_increment (ht : t₀≤t₁)` + a moment helper via `HasLaw.integral_comp` | 0.82 |
| R6 | `ItoFormulaGBM:44` | `ito_formula_expBrownian` re-instantiates the exp-growth tower from scratch but is exactly `ito_formula_itoProcess` at `b=0, f=exp` | collapse to a `b=0` specialization, as `discountedGBM_eq_itoIntegral` is the `m=0` corollary | 0.83 |
| R7 | `ItoFormulaC2:43` | `ito_formula_L2` reproves ~120 lines that `ItoFormulaTD.ito_formula_td_L2` generalizes (C2 is the `f(t,x)=g(x)` case) | derive as the time-independent corollary of the TD theorem | 0.80 |
| R8 | `FTAPOnePeriod:233`, `FTAPOnePeriodVector:556` | the L⁰→L¹ `(1+‖Y‖)⁻¹` tempering reduction ~55 lines copy-pasted scalar/vector (only `|·|` vs `‖·‖`) | extract `exists_isEMM_of_noArbitrage_of_integrableSolver` into `EquivMeasure` | 0.72 |
| R9 | `ItoProcessPredictable:244,301` | `itoProcessAssembled_add`/`_sub` ~55 lines each, differ only add↔sub | share the `ae_prod_iff_ae_ae` block; derive `_sub` from `_add`+`_neg` | 0.83 |
| R10 | `GaussianMoments:43,63` | `x⁴`(=3v²)/`x⁶`(=15v³) byte-identical | one even-moment `∫x^(2n) = (2n−1)!!·vⁿ`; pow4/pow6 = `by simpa` | 0.82 |
| R11 | `DoobLpMaximalInequality:61`, `L2MartingaleConvergence:58`, `LpContinuousMartingaleConvergence:213` | the running-max envelope (L^p-bounded → envelope → Doob-bound → MCT) rebuilt 3× | one envelope lemma consumed by all three | 0.60 |
| — | also: Taylor-remainder tower dup (`ItoFormulaRemainder`/`TDRemainder`, 0.72); Lipschitz→L² domination ×4 (`ItoFormulaCLM`/`TD`/`Localized`/`GBM`, 0.70); exp-tail `e^{−rt}` ×3 (`ExpMin`/`PoissonInterarrival`/`PoissonCounting`, 0.70); `E`-norm²=product-double-integral ×3 (`DriftProcessModification`/`Predictable`, 0.72); forward-FTAP telescoping ×2 (`FTAP`/`FTAPDiscrete`, 0.50); immunization order-match ×2 (`Immunization`/`ConvexityImmunization`, 0.75); TangentPortfolio 2-vs-N unbridged (0.80); CAPM `beta_linearity_two` vs `_finset` (0.75). |||

---

## Mathlib-leverage — consume the right abstraction

| # | site | reinvents | consume instead | conf |
|---|---|---|---|---|
| L1 | `L2MartingaleConvergence:189` | 66-line Chebyshev uniform-integrability | Degenne `uniformIntegrable_of_dominated_singleton` (**verified** at `.lake/…/UniformIntegrable.lean:183`; the sibling file already consumes it) | 0.72 |
| L2 | `StandardNormal:49` | bespoke Gaussian CDF | `ProbabilityTheory.cdf` (see §Gaussian-facts home) | 0.75 |
| L3 | `MertonAmericanCallTree:87` | Jensen for `max(·,0)` by hand (`by_cases`/`nlinarith`) — feeds the flagship Merton theorem | `((convexOn_id _).sup (convexOn_const 0 _)).2 …` (`ConvexOn.sup`) | 0.85 |
| L4 | `MarkowitzNAsset:95` | ad-hoc PSD `Prop` | `Matrix.PosSemidef` (for the `Fintype`/`s=univ` case) — also heals the `ι→ι→ℝ` vs `Matrix` split with `BlackLittermanND` | 0.60 |
| L5 | `UtilityDerivation:89` | hand-rolled concavity predicate | `ConcaveOn ℝ Set.univ u` (`AcceptanceSet` already uses `ConvexOn` for the mirror fact — inconsistency within `RiskMeasures/`) | 0.70 |
| L6 | `Concentration:61` | `w²≤w` via `nlinarith` | `pow_le_of_le_one` — *(note: `patterns.md` flagged this exact goal as needing `nlinarith`; the direct Mathlib lemma beats it)* | 0.85 |
| L7 | `ReplicatingUniqueness:69` | Cramer's rule narrated in the docstring, proved by bespoke scalar elimination | `Matrix.cramer` / `det_fin_two_of` — generalizes to n-asset completeness | 0.70 |
| L8 | `Mortality:88` | hand-built antiderivative for `∫B·e^{cu}` | `integral_exp` + `integral_comp_mul_left` | 0.65 |
| — | also: `ConvexDuality:48` `functional_eq_sum_single` → `Pi.basisFun.sum_repr` (0.45); `Credit:94` 7-line iff → `mul_left_inj'` (sibling `CDSTimeVarying` = one line, 0.90). |||

---

## Missed unifying reductions

- **`VarianceSwapEquivalence:79`** (0.60) — the ~370-line QV ladder (`FromQV`/`Equipartition`/`Limit`) delivers only the *expectation-level* limit, **strictly dominated** by the single L²-concentration `tendsto_realizedVariance_gbm_L2` (`VarianceSwapDriftImmunity`). The two towers are split only by a missing hypothesis bridge; prove `IsPreBrownianReal B μ → BrownianQuadraticVariation …` (its fields *are* the BM-marginal MGF facts already proved) and the ladder collapses to a one-line L²→L¹ corollary.
- **`Numeraire:118` + `ChangeOfMeasure:50`** (0.60) — `Numeraire` proves only the *static* price-invariance; the *dynamic* change-of-numéraire (`X/B` a `Q`-mtg ⟺ `X/N` a `Q^N`-mtg) is exactly `changeOfMeasure_setIntegral_eq` at `Z_t=(N_t B₀)/(N₀ B_t)`. Instantiate the Bayes engine → the theorem practitioners actually use, wiring the numéraire seam to Girsanov.
- **`Futures/Black76:91` (swaption)** (0.85) — `GarmanNormalForm`'s *own docstring* names `Swaption.lean` as a formula "redefined in new variable names"; add `swaption_eq_bsVGarman` and get `swaption_payer_receiver_parity` free from Garman-level parity. (Benchmarked `mf-swaption-parity` `full`.)
- **`PutStrikeConvexity:47`** (0.85) — proves `hasDerivAt_bsP_KK` but never states `ConvexOn`; since `bsP = bsV + affine(K)`, convexity is free via `(bsV_strike_convexOn).add`. The 2nd-derivative apparatus is unnecessary.
- **`AsianInequality:61`** (0.83) — proves the *general* n-ary weighted AM-GM but only assembles the *two-date* Asian payoff; the n-date fact is a one-line `max_le_max` on the already-proved hard step.

---

## Depth — honesty tightenings (docstring promises > delivered / ceremony)

- **`VarianceSwap.lean` docstring** (0.95) promises `varianceSwap_fairStrike` and `integral_excess_return_eq_zero` — **verified**: the names appear only in the module's Results header, never as declarations. Add the two-term theorem (`E_Q[(S_T−F)/F]=0` is one line from `Forward.expected_terminal_eq_forward`) or trim the header.
- **`BlackLittermanND:56`** (0.85) — docstring asserts "recovers the 1-D posterior"; no such lemma exists (the sibling `Markowitz` *proves* its analogous claim). Add `blPosteriorMean_one_dim_eq_posteriorMean1d`.
- **`RiskParityFOC:96`** (0.85) — takes the log-barrier FOC as a *bare hypothesis*; the Lagrangian `Real.log` derivative never appears (contrast `SharpeFOCDerivation`, which computes the actual `HasDerivAt`). Prove it so the FOC is a consequence, not a restatement.
- **`CRRDiscreteIto.lean`** (0.85) — claims to bridge to `Foundations/DiscreteIto` and imports it, but uses **zero** `DiscreteIto` identifiers; the theorems are `.congr'`-massaged restatements of `DriftLimit`/`CRRConvergence`. Either instantiate `discrete_ito_formula` at `X=log S` (make the bridge real) or drop the vestigial framing.
- **`Bermudan.lean`** (0.75) — benchmarked `mf-bermudan-sandwich` `full`, but the whole file is `Finset.sup'_mono` ×2 on an *uninterpreted* `v` (imports only `Mathlib`, no `bermudanPrice` def tying it to the tree). Define `bermudanPrice` over admissible exercise sets so the sandwich becomes a genuine instance.
- **`PDEFromIto.lean`** (0.87) — 5 of 6 results are abstract `unfold;ring` over free reals, never instantiated at `bsV`, and superseded by `PDEFromFeynmanKac`'s genuine forward derivation. Delete or fold + mark superseded.
- lower-value ceremony: `gbm_solves_sde` coefficient-level, dominated by `ito_formula_gbm` (keep its `HasDerivAt.unique` "can't-fake-the-partials" device); `discrete_cubing_identity'` + orphan quartic remainder; `DoobLp` untruncated chain mirrors the truncated one ~160 lines (take it to the `K→∞` sup already proved); `SDEUniqueness.IsL2SolutionPair` 9 fields (several derivable); `ExpMin.minimum_survival` stops at the survival function, one lemma short of the law; `Insurance.net_premium_principle` / `PoissonThinning` (marking law assumed, not constructed).

---

## Elegance — grind → conceptual

- **`WienerIntegralL2:165` + `ItoIntegralProcessMartingale:117`** (0.74) — interval-overlap identities brute-forced by 16-case `nlinarith`, while the repo *already contains* the elegant model `ItoIntegralProcessIsometry.band_overlap_real` (coincide the right endpoints, then a single `le_total` split, 2 cases). Restructure both to the repo's own pattern.
- **`ConvexPricingFunctional:103`** (0.72) — opaque `nlinarith [hconv]` hides the certificate `mul_le_mul_of_nonneg_left hconv hqi`; surface it (pointwise-certificate-minimality).
- **`Call.bsd2_eq:111`** (0.75) — `nlinarith` used for a pure *equality* driven by one substitution → `linear_combination (σ²) * h_sqT_sq` (matches the repo's own "nlinarith is for inequalities" doctrine).
- **`StandardNormal.Phi_neg:79`** (0.68) — reinvents complementation ~22 lines vs the file's own `gaussianReal_Ioi_toReal` 10-line idiom (`prob_compl_eq_one_sub`).
- **`BivariateGaussian:133`** (0.60) — the decorrelation *idea* is exemplary but the endgame carries a removable `Xhat` scaffold; the direct split `X = βY + (X−βY)` drops ~30 lines.

---

## Exemplars — the current ceiling (celebrate and keep)

These are the high-water marks the gradient upgrades should aspire to; each was read
in full and verified genuine.

- **`GarmanNormalForm`** — one formula `A·Φ(d₁) − K·DF·Φ(d₂)` shown to *literally be* BS, Black-76, BS-Merton dividends, Garman–Kohlhagen, KMV-Merton, and (via `ExchangeOption`) Margrabe, each by a one-line log bridge. Three-scale unification across an entire *model family*.
- **`ItoIsometryAdapted.rect_increment_pairing`** — the genuine stochastic core: cross-terms vanish by increment-*independence* (weak Markov), not deterministic covariance — the Itô-vs-Wiener distinction, formalized as a reusable inner-product identity.
- **`ItoIntegralProcessGeneral.itoProcessCLM_eq_condExpL2`** — one identification `(φ●B)_t = condExpL2 𝓕_t (∫φdB)` from which adaptedness, the martingale property, the L² contraction, and terminal isometry all fall out as cheap corollaries.
- **`FTAPOnePeriodVector`** (softplus/Esscher) — derives the general-Ω d-asset EMM by minimizing a smooth convex potential over the gains-kernel's orthogonal complement, sidestepping Hahn–Banach, L⁰-cone closedness, *and* measurable selection at once, absorbing redundant assets with no non-redundancy hypothesis.
- **`ConvexDuality` + `ConvexSeparation`** — one cone-separation root yields FTAP, coherent-risk (verified consumed by `AcceptanceSet`), and superhedging. The convex-duality unification is load-bearing, not prose.
- **`RiskMeasures/RockafellarUryasev`** — the full variational theorem via the honest pointwise certificate `(L−c)⁺ ≥ (L−c)·𝟙_{Z>z}`, tight exactly at `c=VaR` — certificate-not-calculus.
- **`Portfolio/CovariancePSD`** — PSD of the covariance matrix falls out for free because the Markowitz quadratic form *is* `Var[∑wᵢRᵢ]` (self-dot variance). (Findings R4/L4 are precisely about getting this asset to its natural consumers.)
- **`QuadraticVariationL2`** — the L² quadratic variation as a Pythagorean identity: centered squared increments are pairwise orthogonal by weak Markov, the diagonal being Gaussian kurtosis `E[X⁴]=3Var²` — why `(dB)²=dt`.
- **`MargrabeGrounding` + `ExchangeOption`**, **`MertonDominance`** (vega+gamma channels, Jensen-tangent made tight by the Poisson compensator), **`VasicekSDEGaussian`** (derives the Vasicek Gaussian law from the actual stochastic integral — closes the two-tower gap), **`KMVMertonStructural`** (this-IS-that ×3), **`CRRCharFun`** (triangular-array CLT via charFun + a put-call-parity uniform-integrability sidestep), **`PathReflection`** (algebraic-identity / counting-bijection decoupling + a discrete IVT), **`ito_formula_unrestricted_local`** (double space+time localization), **`ito_formula_td_localized`** (isometry transfers Cauchy-ness of the integrals to the integrands), **`condExp_sup_nulls`** (recognizing the null-augmented σ-algebra as Mathlib's `eventuallyMeasurableSpace`), **`OptionalSamplingInequality`** (inequality = equality + monotone part), **`KellyNumeraire`** (GOP-deflation ⟹ EMM, p-independence *derived* from the Kelly FOC), **`ExponentialDiscount`** (one calculus genuinely consumed by Mortality/HazardCurve/ForwardRate).

---

## Recommended upgrade priorities

Sequenced by value / low-risk-first. All are consolidations — none change what the
library proves; each improves coherence and deletes duplication.

1. **§Gaussian-facts home** — the biggest coherence win; also deletes cross-model imports. Low risk.
2. **R1 isometric-extension package** (×3 verbatim) and **R3 GreekSigns sign-fact reuse** — high-confidence, local, pure deletion.
3. **R4 `portfolioVariance_eq_portfolioVarN` bridge** — unlocks the genuine PSD proof for the whole portfolio cluster (one lemma, large reach).
4. **L1 consume Degenne's `uniformIntegrable_of_dominated_singleton`** — deletes 66 hand-rolled lines.
5. **The honesty tightenings** (VarianceSwap, BlackLittermanND, RiskParityFOC, CRRDiscreteIto, Bermudan) — cheap, and they raise the delivery-layer's integrity (three are benchmarked `full`).
6. **R2 ZCB-atom** and **L3 Jensen-via-`ConvexOn`** — feed benchmarked/flagship theorems.
7. **The missed reductions** (variance-swap L² bridge, dynamic numéraire, swaption=Garman, put-strike convexity) — higher mathematical value, moderate effort; the variance-swap one retires ~370 lines.
8. **Elegance + remaining name-once items** — fold opportunistically when the file is next touched.

---

## Upgrades executed this session (2026-07-04)

Applied and validated (per-file `lean-check` + a full green boot build; gates 19/19;
AxiomAuditGen byte-fresh):

1. **§Gaussian-facts home** (priority 1) — `setIntegral_gaussianPDFReal_eq_toReal`
   hoisted to `StandardNormal` (retires the pdf→Φ idiom ×6 across
   Call/Put/Digital/Bachelier); `Phi_le_one` and `gaussianPDFReal_zero_one_neg`
   moved to `StandardNormal` (KMVMerton/PutStrikeConvexity now cite them); the
   standard-normal PDF derivatives moved to `GaussianCDFDeriv`, and the two spurious
   cross-model `import …Bachelier` in `HigherGreeks`/`DigitalGreeks` dropped. (The
   `Phi := ProbabilityTheory.cdf` redefinition — the deepest-blast-radius sub-item —
   is deferred: high churn, low marginal value.)
2. **R3** — StrikeConvexity / SpotConvexity now cite the named `bsV_partial_KK_nonneg`
   / `bsV_gamma_pos` (`GreekSigns`) instead of re-deriving the sign facts.
3. **R2** — Immunization / ConvexityImmunization consume the ZCB duration atom
   `ZCB.hasDerivAt_zcb_r`.
4. **L6** — `Concentration` uses `pow_le_of_le_one` (was `nlinarith`).
5. **ConvexPricingFunctional** — the honest `mul_le_mul_of_nonneg_left` certificate
   (was opaque `nlinarith [hconv]`).
6. **Honesty tightenings** (docstring integrity, benchmarked-`full`): VarianceSwap
   (Results list now matches the proved `varianceSwap_log_contribution`, not the two
   absent headline lemmas), BlackLittermanND (the 1-D "Connection" is the honest
   correspondence, not a claimed lemma), CRRDiscreteIto (no longer claims to "bridge"
   the DiscreteIto framework it does not instantiate).

Also corrected `README.md`'s architecture table (the numéraire IV↔I seam was stale
`◻️ open`; it is `✅ WIRED` — `changeOfNumeraire`, already documented at README:168
and `mathematical-architecture.md:52`).

**Not executed** (higher effort / cascade risk / needs a design call), carried in the
backlog above: L1 (Degenne `uniformIntegrable_of_dominated_singleton` — a different
UI predicate with a downstream consumer), R4 (portfolioVariance PSD bridge), R1
(isometry-extension package ×3), the RiskParityFOC / Bermudan lemma-adds, and the
missed reductions. L3 and `bsd2_eq` deferred (fiddly, low value; current proofs clean
and correct).

## Relationship to the other reviews & non-findings

- **Overlap with the idiomatic review** (`docs/idiomatic-review-2026-07-04.md`): the
  `isCadlag_of_continuous` triplication (that review's I4, deferred) is independently
  confirmed here with the same conclusion — the proper fix is upstreaming
  `Continuous.isCadlag` to Degenne. The ZCB-atom (R2) is the idiomatic FIN2-ZCB item;
  the math agent supplies a cleaner path. `Insurance.net_premium_principle` is a
  wrapper both reviews flag. Everything else here is *new* (the deep-math findings).
- **Non-findings / genuinely optimal** (do not "upgrade"): `ItoFormulaSquaredL2`
  (the direct 3-line proof beats invoking the general machine); `FiniteMeasureCauchySchwarz`,
  `PoissonPgf`, `PoissonSuperposition`, `BrownianExpMoment`, `MartingaleTransform`,
  `ExitTime`, `PriceBounds`, `MertonClassicDisplay`, `NewtonConvergence` — read in full,
  each is minimal and right for its purpose. Bespoke objects with a documented reason
  (Degenne's `SimpleProcess` bounded-coefficient clamp; `AdaptedAt`'s explicit `g` for
  `indepFun`; the raw-filtration `ExitTime`) are correctly kept.

Corpus unchanged (312) — this is a Foundations-and-craft review, no benchmark added.
The upgrades executed this session are recorded above; the remaining backlog is
specified precisely enough to apply directly.
