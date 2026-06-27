# Mathlib / BrownianMotion-Package Bridge Audit

**Date:** 2026-05-22
**Scope:** All modules under `MathFin/Foundations/`
plus pricing-module consumption of Mathlib's probability surface.

## Executive summary

The earlier critique that "4664 LOC of Foundations is dead code from pricing
modules" was **half right and half wrong**:

- **Right** that the BM/Wiener/martingale machinery is structurally
  disconnected from pricing modules. `IsBrownianMotion`, `Martingale`
  (Mathlib class), `wienerIntegral`, `quadraticVariation`, `StoppingTime`,
  `condExp` are referenced **0 times** in any pricing module.
- **Wrong** that Foundations duplicates Mathlib. Of the 9 substantive
  Foundations files audited below, **8 fill genuine Mathlib gaps** that
  cannot be replaced by direct Mathlib imports.

The right action is **additive bridges** (constructors connecting Foundations
to pricing) rather than **destructive replacement** (deleting Foundations in
favor of Mathlib equivalents). Phase 30 (Bridge A,
`BSCallHypFromBrownian.lean`) is the first such bridge.

## Per-module audit findings

### Foundations/BrownianQuadraticVariation.lean (161 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **What it does:** L¹-expectation form of `[B, B]_t = t` for processes with
  Gaussian increments. Pure marginal-moment computation via
  `variance_id_gaussianReal`.
- **BrownianMotion package equivalent:**
  `StochasticIntegral/QuadraticVariation.lean` defines `quadraticVariation`
  via the Doob-Meyer decomposition (`predictablePart` of squared norm).
  Currently sorry-laden (WIP).
- **Bridge opportunity:** Once BM package's path-wise QV is complete, derive
  our L¹ version as its expectation. For now, **keep both**.

### Foundations/LpContinuousMartingaleConvergence.lean (725 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **What it does:** L^p convergence at naturals for continuous-time L^p-
  bounded martingales (`lp_continuous_martingale_converges_at_naturals`).
- **BrownianMotion package equivalent:**
  `StochasticIntegral/DoobLp.lean` proves Doob's maximal inequality
  (`maximal_ineq_countable`, `maximal_ineq_ennreal`). Related but not the
  same theorem. The maximal inequality is *used* in our convergence proof.
- **Bridge opportunity:** Replace our internal Doob's maximal inequality
  (if any) with imports from BM package's `DoobLp.lean`. Low-LOC change,
  defer until needed.

### Foundations/MartingaleTransform.lean (123 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **What it does:** Discrete martingale-transform construction `(A · M)_n :=
  ∑_{k<n} A_{k+1}(M_{k+1} − M_k)` and adapted-integrability-martingale
  property.
- **Mathlib equivalent:** None found by name search. Mathlib's
  `Mathlib.Probability.Martingale.*` covers discrete and continuous
  martingales but no `martingaleTransform` named declaration.
- **Bridge opportunity:** None needed. Likely upstream candidate.

### Foundations/CondExpJensen.lean (95 LOC)

- **Status: DELETED 2026-06-04 — Mathlib subsumes it.** (The assessment below
  is the historical 2026-05-22 audit record, which predates the deletion.)
- **Status (2026-05-22, superseded):** Fills Mathlib gap. NOT duplicate.
- **Self-documenting:** The file's own docstring says "Mathlib v4.30 has no
  general subgradient API for convex functions on ℝ" — the explicit
  subgradient parameterisation is necessary.
- **Bridge opportunity:** None. Upstream candidate when Mathlib gains a
  subgradient API.

### Foundations/BivariateGaussian.lean (165 LOC)

- **Status:** Builds finance-specific struct over Mathlib `HasGaussianLaw`.
- **What it does:** `BivariateGaussianHyp` packages the bivariate-Gaussian
  conditional-expectation formula `E[X | σ(Y)] = μ_X + (ρ σ_X / σ_Y)(Y - μ_Y)`.
- **Mathlib equivalent:** Mathlib has `IsGaussianProcess`, `HasGaussianLaw`,
  `gaussianProjectiveFamily` (in BrownianMotion package). The conditional-
  expectation closed form for bivariate is not directly stated.
- **Bridge opportunity:** Connect `joint_gaussian` to `HasGaussianLaw` more
  formally if not already. Low value.

### Foundations/StandardGaussianMGF.lean (81 LOC)

- **Status:** Specialised reformulation. Possible partial duplication.
- **What it does:** Specialises `∫ exp(c·Z) ∂N(0,1) = exp(c²/2)` for the BS
  use case. Currently derived from `integral_exp_mul_gaussianPDFReal_univ`.
- **Mathlib equivalent:** `gaussianReal_charFun` is the characteristic
  function `E[exp(i·t·X)]`. The MGF would be its analytic continuation to
  real `c`.
- **Bridge opportunity:** Could potentially derive our MGF identity from
  `gaussianReal_charFun` via analytic continuation. Significant rework for
  modest gain. **Defer.**

### Foundations/GaussianCDFDeriv.lean (81 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **Self-documenting:** "not present in Mathlib (no `Real.erf`, no
  `gaussianReal_Iic_hasDerivAt`)".
- **Bridge opportunity:** None. Upstream candidate.

### Foundations/WienerIntegral.lean + WienerIntegralL2.lean (580 LOC combined)

- **Status:** Foundation work. Possible partial overlap with BM package.
- **BM package equivalents:** `StochasticIntegral/SimpleProcess.lean`,
  `MonotoneProcess.lean`, `LocalMartingale.lean`, `Predictable.lean`,
  `Centering.lean`. The BM package is more general (cadlag, predictable
  processes) where ours is L²-specific Wiener integral.
- **Bridge opportunity:** Once BM package's stochastic-integral pipeline is
  complete (currently has sorries), our L² Wiener integral could be derived
  as a special case of theirs. **Defer until BM package stabilises.**

### Foundations/DoobLpMaximalInequality.lean (1019 LOC) — LARGEST

- **Status:** Original proof of Doob's **strong-type** `Lᵖ` maximal
  inequality (`MeasureTheory.maximal_ineq_Lp`) — a genuine gap-fill over
  Mathlib's weak-type form, via ~18 private helpers (layer cake + Fubini +
  Hölder + truncation/monotone convergence). Axioms-clean.
- **Bridge opportunity:** This file deserves a dedicated audit pass; out of
  scope for current bridging session. **TODO.**

### Foundations/BrownianMartingale.lean (473 LOC)

- **Status:** Continuous-time Brownian-motion-is-martingale derivations.
- **BM package equivalent:** `IsPreBrownian` + `Auxiliary/Martingale`. The
  package's `IsPreBrownian` characterises BM by finite-dim Gaussian laws
  and has a continuous modification (Kolmogorov-Chentsov). Our file builds
  martingale + stopping-time structure on top.
- **Bridge opportunity:** Re-derive our `BrownianMartingale` content as
  consequences of `IsPreBrownian`. Could shrink considerably. **TODO** —
  needs careful audit to preserve any unique content.

## Bridges executed (Phase 30+)

| # | Name | File | Status |
|---|------|------|--------|
| A | `BSCallHyp.of_isPreBrownian` | `Foundations/BSCallHypFromBrownian.lean` | NEW (phase 30) |
| A.2 | `BachelierHyp.of_isPreBrownian` | (same file) | NEW (phase 30) |
| — | Core scaling lemma `scaled_isPreBrownian_eval_law` | (same file) | NEW (phase 30) |
| — | `bsTerminal_via_brownian` (S_T = S_0 · exp((r−σ²/2)T + σ·W_T)) | (same file) | NEW (phase 30) |
| — | `bachelierTerminal_via_brownian` (S_T = S_0 + σ·W_T) | (same file) | NEW (phase 30) |
| 31 | Full pricing pipeline from `IsPreBrownian` (composite corollaries): BS call, put, put-call parity, Bachelier, cash digital, asset digital, power call, dividends call, stock numeraire, KMV PD, Merton equity | `Foundations/PricingFromBrownian.lean` | NEW (phase 31) |
| 32 | Variance-swap per-increment QV identity: `E[(X_t − X_s)²] = σ²(t−s) + (r−σ²/2)²(t−s)²` for BS log-price under `BrownianQuadraticVariation` hypothesis. First downstream use of the BQV module from outside `Foundations/BrownianQuadraticVariation.lean`. Exposed previously-private `integral_sq_increment`, `integrable_sq_increment`, `measurable_increment` and added new public `integral_increment` (E[B_t − B_s] = 0), `integrable_increment` to BQV's public surface | `Foundations/VarianceSwapFromQV.lean` + BQV public-surface additions | NEW (phase 32) |
| 33 | Variance-swap equipartition sum: `E[Σ_{k=0}^{n} (X-increments at k·T/(n+1))²] = σ²·T + (r−σ²/2)²·T²/(n+1)`. Builds on phase 32's per-increment via `integral_finset_sum` after establishing per-summand integrability | `Foundations/VarianceSwapEquipartition.lean` | NEW (phase 33) |
| 34 | Variance-swap QV limit: `Tendsto (E[Σ ...]) atTop (𝓝 (σ²·T))`. The drift contribution `drift²·T²/(n+1) → 0` via `tendsto_one_div_add_atTop_nhds_zero_nat`. Completes the QV chain — realised variance under fine partitions equals the variance-swap fair strike `σ²` (after `1/T` rescaling) | `Foundations/VarianceSwapLimit.lean` | NEW (phase 34) |
| 35 | Discrete Itô formula `f(X_N) − f(X_0) = Σ f'·ΔX + (1/2) Σ f''·(ΔX)² + Σ R_k`, telescoping + per-summand Taylor remainder by definition. **Adapted from Nagy 2026** (SSRN 6336503, Section 3). Attribution: original Lean source in paper §3; our adaptation renames `taylor_remainder → discreteTaylorRemainder`, factors `(1/2)` out, restructures proof to use `Finset.sum_congr` | `Foundations/DiscreteIto.lean` | NEW (phase 35, after Nagy) |
| 37 | FTAP both directions for one-period one-asset two-state market: forward (EMM ⟹ no arbitrage), backward (construct EMM from sign data via `q_up = −z_down/(z_up − z_down)`). **Adapted from Nagy 2026** (§7). Attribution: Nagy's Theorems 7.1-7.3. Complements our existing forward FTAP for general finite-state in `Foundations/NoArbitrageDerivations.lean` | `Foundations/FTAPTwoState.lean` | NEW (phase 37, after Nagy) |
| 38 | Constant-product AMM (Uniswap v2-style): swap output `Δy = y·Δx/(x + Δx)`, constant-product invariant preservation `(x + Δx)·(y − Δy) = x·y`, internal price `y/x` at zero input, arbitrage trigger. **Adapted from Pusceddu-Bartoletti FMBC 2024** (OASIcs FMBC.2024.5), with own ℝ-based framework (no `PReal` dependency). Attribution to the underlying Bartoletti-Chiang-Lluch-Lafuente 2022 theory. **First DeFi module** in MathFin — opens Foundations to DeFi market microstructure | `DeFi/ConstantProductAMM.lean` | NEW (phase 38, after Pusceddu-Bartoletti) |
| 39 | Itô structural drift formula `itoDrift f' f'' μ_X σ_X := μ_X · f' + (1/2) · σ_X² · f''` — the per-time-unit drift coefficient in Itô's lemma. Specialisations: identity sanity check + **GBM log-drift** `d(log S) drift = μ − σ²/2` (the celebrated `−σ²/2` Itô correction). **Adapted from Nagy 2026 §5**. The structural drift, not the full L²-integral form (which is gated). Used downstream by Phase 46 (BS PDE). | `Foundations/ItoLemma.lean` | NEW (phase 39, after Nagy) |
| 41 | Vasicek terminal-distribution form **(stated, not derived)**: the OU law `r_t ~ N(r_0 e^{−κt} + θ(1−e^{−κt}), σ²(1−e^{−2κt})/(2κ))` is *posited* as closed-form `def`s (BSCallHyp-style), with the parametrisation `vasicekSDETerminal r_0 θ κ σ t Z = mean + √var · Z`, the mean-reversion asymptotic `mean → θ`, and variance-positivity / `t=0` properties proved. ~~**The SDE → Gaussian-law derivation itself is open**~~ — **now CLOSED, see row WG↓**: the SDE→law derivation is formalized in `FixedIncome/VasicekSDEGaussian.lean` (`vasicekShortRate_hasLaw_gaussian`), so the posited `def`s here are now a *theorem*. | `FixedIncome/VasicekSDE.lean` | NEW (phase 41); derivation landed WG (2026-06-27) |
| 43 | Binomial up-probability `q = (e^r − d)/(u − d)` derived from two-state FTAP backward construction (Phase 37 + Nagy §7). Excess returns `(z_u, z_d) = (u − e^r, d − e^r)` satisfy the sign condition under `BinomialNoArb` ⟹ EMM exists. The binomial `q` equals Nagy's `−z_d/(z_u − z_d)`. Bridge between `Binomial/Model.lean` and `Foundations/FTAPTwoState.lean`. | `Binomial/BinomialFromFTAP.lean` | NEW (phase 43) |
| 45 | Variance-swap log-payoff and QV-limit form equivalence: both `(2/T) · E[log(F/S_T)]` (existing) and `lim_n (1/T) · E[Σ (Δlog S)²]` (Phase 34) yield `σ²`. Model-parameter equivalence: same model variance recovered by both empirical / replication characterisations. | `Foundations/VarianceSwapEquivalence.lean` | NEW (phase 45); WIRED (corpus `mf-variance-swap-equivalence`, 2026-06-09) |
| 46 | BS PDE derived from Itô drift + no-arbitrage: under risk-neutral GBM, the discounted price's drift = 0 ⟹ `∂_t V + r S ∂_S V + (1/2) σ² S² ∂_SS V − r V = 0`. Forward derivation from no-arb (vs the backward verification in existing `BlackScholes/PDE.lean`). Uses Phase 39's `itoDrift` as the algebraic core. | `BlackScholes/PDEFromIto.lean` | NEW (phase 46) |
| 53 | Pricing kernel from two-state FTAP: discounted EMM weights `q_state = e^{−rT} · q^{EMM}` form a valid pricing kernel — non-negative, sums to bond price, linear in payoff. Composes `Foundations/StatePrices.lean` (linear functional axioms) with `Foundations/FTAPTwoState.lean` (Phase 37 EMM construction). Bond price + monotonicity from FTAP, not assumed separately. *(Round 6: the composition made definitional — `statePrices_two_state := e^{−rT} · emmWeight{Up,Down}` consumes FTAPTwoState's named weights, and the kernel IS `statePricePricing`, its lemmas consumed from `StatePrices`.)* | `Foundations/PricingKernel.lean` | NEW (phase 53); WIRED (corpus `mf-pricing-kernel-butterfly`, 2026-06-09); recomposed (round 6, 2026-06-09) |
| 53a | **Payoff convexity through a non-negative linear pricing functional** (`ConvexPricingFunctional`): call-price convexity in strike, butterfly non-negativity, implied-PDF non-negativity — one principle, consumed by `PricingKernel`'s FTAP butterfly (corpus `mf-pricing-kernel-butterfly`). One of the five documented Foundations→pricing application bridges; this row records its layering exception. | `Foundations/ConvexPricingFunctional.lean` | catalogued (round 6, 2026-06-09) |
| 44a+b | CRR binomial scheme as discrete-Itô process: per-step drift `(2p − 1)·σ√Δt` (= `q · log u + (1−q) · log d`) and per-step QV `4p(1−p)·σ²·Δt` (= variance of log-return), identified algebraically (44a). Summed over `n` steps: drift → `(r − σ²/2)·T`, QV → `σ²·T` (44b, composing existing `crr_drift_limit_n` from `DriftLimit.lean` and `crr_variance_limit` from `CRRConvergence.lean`). Connects Phase 35 discrete-Itô framework to existing CRR machinery. | `Binomial/CRRDiscreteIto.lean` | NEW (phase 44a+b) |
| 44c | CRR → BS price convergence: the n-step binomial call price converges to the Black-Scholes call price (`binomialPrice_call_tendsto_bs`), via a characteristic-function + Lévy-continuity route to convergence in distribution and a put-call-parity argument (the bounded put converges weakly; parity lifts it to the call — no triangular-array CLT needed). The literal closed form `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)` is `binomialPrice_call_tendsto_bs_closed`, chaining that put-parity limit through `bs_put_formula` (on the standardised terminal law) + `Phi_neg`. | `Binomial/CRRCharFun.lean`, `Binomial/CRRClosedForm.lean` | DONE (phase 44c) |
| 42 | Multi-state FTAP: **forward direction proved in arbitrary finite state + finite assets** (`noArbitrage_of_emm_multi`: EMM ⟹ no arbitrage, by the `Finset.sum_comm` swap + `Finset.sum_pos'` positivity argument). **The open piece** (Phase 42c): constructing `q` from no-arbitrage via Hahn-Banach separation / Farkas (Mathlib has Hahn-Banach in normed spaces but not specialised to finite-dim with positivity cone). Forward direction generalises Phase 37. | `Foundations/FTAPMultiState.lean` | NEW (phase 42 forward); WIRED forward (corpus `mf-ftap-multi-state-forward`, 2026-06-09) |
| 40 (GBM specialisation) | **Itô's lemma L¹-expectation form specialised to GBM-log** (`f = log` on `dS = r S dt + σ S dB`). `bsLogReturn r σ T Z := (r − σ²/2)·T + σ·√T·Z` collapses `log(bsTerminal/S_0)` to a linear function of `Z`. Under `BSCallHyp`: `E_Q[bsLogReturn] = (r − σ²/2)·T` (the Itô-corrected drift integrated) and `Var_Q[bsLogReturn] = σ²·T` (the QV over `[0, T]`). **First L¹-form Itô identity** in the library — the path-wise version remains gated on full L²-density convergence (which Nagy 2026 also leaves "structurally verified"). | `BlackScholes/GBMLogMoments.lean` | NEW (phase 40 GBM specialisation) |
| 28 | **Forward-rate / hazard / force-of-mortality via Mathlib `intervalIntegral` + the `ExponentialDiscount` principle** (was deferred below). `forwardRate_eq_neg_log_discount`, `force_eq_neg_log_deriv_survival`, `hazard_eq_neg_log_deriv_survival` express `rate = −d/dt log Q` against the actual discount `exp(−H)`, via `rate_eq_neg_log_deriv` + the FTC (`integral_hasDerivAt_right`). Mortality/HazardCurve previously stated this only in prose. Makes `Foundations/ExponentialDiscount` load-bearing (0 → 3 consumers). | `FixedIncome/ForwardRate.lean`, `Actuarial/Mortality.lean`, `FixedIncome/HazardCurve.lean` | NEW (2026-05-23 principle-audit pass) |
| L1 (Girsanov) | **The risk-neutral measure derived from the physical measure** (static Girsanov). `BSCallHyp.exists_of_physical`: `Q := P.withDensity(exp(c·W−c²/2))` is a probability measure under which the recentred driver is standard normal, so `BSCallHyp` holds — the EMM is *constructed*, not assumed. Chain: `gaussian_esscher_pdf` → `gaussianReal_withDensity_esscher` → `map_withDensity_comp` (upstreamable) → `hasLaw_esscher_tilt` → `hasLaw_sub_const`. `bsTerminal_physical_eq_riskNeutral` shows the same asset is repriced with drift `μ→r`. See [`leaps.md`](leaps.md). | `Foundations/GaussianGirsanov.lean` | NEW (2026-05-23, leap 1) |
| L2 (genesis cascade) | **Physical → EMM → pricing.** `discounted_terminal_eq_S0_of_physical` (the constructed `Q` is a genuine EMM: `E_Q[e^{−rT}S_T]=S₀`) and `bs_call_formula_of_physical` (full physical→price chain). Additive bridges consuming the prior pricing theorems — `GaussianGirsanov` made load-bearing. | `Foundations/GaussianGirsanov.lean` | NEW (2026-05-23, leap 2) |
| L3 (Margrabe) | **Multivariate exchange option = one-asset BS on the ratio.** Effective vol `√(σ₁²+σ₂²−2ρσ₁σ₂)` (`margrabe_effective_variance`, via covariance bilinearity — makes the `BivariateGaussian` covariance machinery load-bearing); `margrabe_eq_bsVGarman` (Margrabe is a `GarmanNormalForm` instance, its 4th consumer); `margrabe_parity`; `margrabe_price_via_call` (price-level: `S²₀·E_Q[max(R_T−1,0)] = margrabePrice` via `bs_call_formula` on `R=S¹/S²`). | `BlackScholes/ExchangeOption.lean` | NEW (2026-05-23, leap 3) |
| L4 (adapted Itô isometry) | **The genuinely-stochastic Itô isometry**, for *random adapted* integrands — distinct from the deterministic Wiener integral (`WienerIntegralL2.lean`). Cross-terms vanish by the weak Markov property `IsPreBrownian.indepFun_shift` (`ΔBₖ ⊥ 𝓕_{tₖ}`), not by covariance. `ito_isometry_discrete`: `E[(Σ φₖ·ΔBₖ)²] = Σ E[φₖ²]·Δtₖ`; capstone `ito_isometry_brownian_self` (`∫₀ᵀ B dB`, fully discharged). Makes `IsPreBrownian.hasIndepIncrements`/`indepFun_shift` load-bearing, overturning the prior "increment independence is WIP upstream" framing. See [`leaps.md`](leaps.md). | `Foundations/ItoIsometryAdapted.lean` | NEW (2026-05-23, leap 4 discrete) |
| L3-grounding (Margrabe) | **The ratio's `BSCallHyp` derived, not assumed** — closes leap 3 end-to-end. `normalizedSpread_hasLaw_std`: the normalized log-spread driver `(σ₁W₁−σ₂W₂)/σ_eff` of a jointly-gaussian pair is `N(0,1)` (gaussianity preserved under `HasGaussianLaw.map_of_measurable`; variance pinned to 1 by `margrabe_effective_variance` — makes `Foundations/BivariateGaussian` load-bearing). `margrabe_bsCallHyp_of_gaussian`: the two-asset grounding reduces to leap-1 Girsanov (`BSCallHyp.exists_of_physical`) on that single effective driver. `margrabe_price_of_gaussian` composes the grounding with `margrabe_price_via_call` for a hypothesis-free exchange-option *price*. See [`leaps.md`](leaps.md). | `BlackScholes/MargrabeGrounding.lean` | NEW (2026-05-23, leap 3 grounding) |
| VS-drift | **Variance-swap drift immunity**: realized variance of GBM log-returns → `σ²T` in **L²** for **any** drift parameter — the fair strike is a QV functional, immune to the physical-vs-risk-neutral drift. The GBM log-price is an Itô process with constant-slope drift, so `ItoProcessQV.tendsto_qv_ito_process` applies verbatim; strengthens phase 34 (expectation-level, risk-neutral drift only) to mean-square concentration for every drift. First pricing consumer of `ItoProcessQV`. | `Foundations/VarianceSwapDriftImmunity.lean` | NEW (2026-06-06) |
| FtD | **First-to-default spread additivity**: basket survival = `survivalProbability (Σ rates) 0 t` and the FtD credit spread = `Σ` single-name hazards, for jointly independent exponential default times. Pure bridge — `ExpMin.minimum_survival` (previously consumed only by `dist-exp-min`) rewritten in the `Credit.lean` vocabulary; the spread reading falls out of the existing `creditSpread_eq_hazard`. | `FixedIncome/FirstToDefault.lean` | NEW (2026-06-06) |
| Merton | **Merton (1976) jump-diffusion as a Poisson mixture**: `mertonCallPrice := ∫ n, C_BS(spot_n, vol_n) ∂(poissonMeasure Λ)` — the price is an honest expectation over the jump count; the textbook series, the compensation identity `E[spot_N] = S₀` (new Poisson pgf `E[x^N] = e^{Λ(x−1)}`, `Foundations/PoissonPgf.lean`, absent from Mathlib), and put–call parity are theorems. Every term separately grounded as a discounted conditional expected payoff via `bs_call_formula`/`bs_put_formula` on `(ℝ, gaussianReal 0 1)`. Terminal-mixture-law scope; the jump SDE is upstream-gated. | `BlackScholes/MertonJumpDiffusion.lean` + `Foundations/PoissonPgf.lean` | NEW (2026-06-06) |
| FK | **Feynman–Kac → Black–Scholes PDE keystone** (closes the two-tower gap): the BS PDE `−∂_τV + ½σ²S²∂_SSV + rS∂_SV − rV = 0` derived **independently of Itô**, from the heat-kernel representation `feynmanU g t x = ∫ z, g z · K(t, z−x) dz`. The crux is the heat kernel's **joint Fréchet-differentiability** `hasFDerivAt_heatKernel` (the one genuinely-2D ingredient — makes a single curve chain rule available), feeding `hasDerivAt_feynmanU_{t,x,xx}` (dominated differentiation under the integral, routed through the parametric skeleton `hasDerivAt_integral_mul_kernelFamily`) and the kernel identity `feynmanU_heat_equation` (`∂_t K = ½ ∂_xx K`). The BS Greeks `hasDerivAt_bsV_{tau,S,SS}_fk` follow by the log-transform `S = eˣ` + discount, and the drift cancellation (`U_x` coeff `−(r−σ²/2)−½σ²+r = 0`, `U_xx` coeff `−½σ²+½σ²=0`) assembles the PDE. Makes the previously-orphan `feynmanU` heat flow load-bearing for pricing. Constant-coefficient scope; variable-coefficient FK (local-vol/Heston) + fully-general continuous-`g` PDE + uniqueness remain open. **Supersedes** [`feynman-kac-growth-deferred.md`](feynman-kac-growth-deferred.md). | `Foundations/FeynmanKacHeatEquation.lean` + `BlackScholes/PDEFromFeynmanKac.lean` (corpus `sc-bs-pde-feynman-kac`) | NEW (2026-06-08) |
| WG | **The deterministic-integrand Wiener integral is Gaussian → Vasicek terminal law derived** (the *first Itô-tower consumer in FixedIncome*, an Itô-side counterpart to the Itô-independent FK bridge above). `Foundations/WienerIntegralGaussian.lean` proves `μ.map (wienerIntegralLp B hB T f) = gaussianReal 0 ‖f‖²` — the distribution the isometry construction (`WienerIntegralL2`) left open, via the characteristic-function route: simple-process Gaussianity (`IsGaussianProcess.of_isGaussianProcess` on the scaled-increment family + `HasGaussianLaw.map_eq_gaussianReal`, mean `0` + variance the isometry) then density + a `|t|`-Lipschitz-charFun `DenseRange.induction_on` + `Measure.ext_of_charFun`. Its consumer `FixedIncome/VasicekSDEGaussian.lean` (`vasicekShortRate_hasLaw_gaussian`) makes the Vasicek SDE terminal law a *theorem*: `r_T = mean + σ ∫₀ᵀ e^{−κ(T−s)} dB_s ~ N(vasicekSDEMean, σ²(1−e^{−2κT})/(2κ))`, with the variance pinned by the FTC integral `∫₀ᵀ e^{−2κ(T−s)} ds` and the affine map via `gaussianReal_const_mul`/`gaussianReal_const_add`. Retires row 41's "stated, not derived". Honest scope: deterministic integrand (the genuinely-random-integrand local-martingale Itô formula remains the open localization frontier). | `Foundations/WienerIntegralGaussian.lean` + `FixedIncome/VasicekSDEGaussian.lean` (corpus `sc-wiener-integral-gaussian`, `mf-vasicek-sde-terminal-gaussian`) | NEW (2026-06-27) |

## Bridges planned but deferred

| # | Name | Reason for deferring |
|---|------|----------------------|
| B | Discounted price as Mathlib `Martingale` | Requires defining the price process structure (vs. just the terminal). Significant additive work. |
| D | `SnellEnvelope` over Mathlib `StoppingTime` | Requires reworking the recursive Binomial price definition to thread filtration. |
| 27 | Vasicek from `IsPreBrownian` | Requires stochastic integral for `∫_0^t e^{-κ(t-s)} dW_s` term; BM package's stochastic integral has sorries. |
| 25 | Variance swap from QV | Partially superseded 2026-06-06: the L²-equipartition version is DONE from our own `ItoProcessQV` (`VarianceSwapDriftImmunity.lean`, arbitrary drift). The *pathwise* QV version stays gated on the BM package. |
| 4 | CRR via Mathlib CLT/Skorohod | Significant refactor of `CRRConvergence.lean`. |
| 6 | NoArbitrage via `LinearMap` | Refactor of `NoArbitrageDerivations.lean`. |

## Conclusion

Foundations is **not** slop. It fills Mathlib gaps and shouldn't be deleted.
The architectural bridge gap is real but the remedy is additive constructors
(Bridge A pattern) rather than wholesale replacement. The 4664 LOC stays;
new pricing entry points (BS, Bachelier, eventually Vasicek/CIR via Itô)
gain optional BM-based constructors that compose with existing pricing
machinery.

The largest single foundation file is `DoobLpMaximalInequality.lean` (1019
LOC) — the original strong-type Doob `Lᵖ` maximal inequality, which consumes
Mathlib's weak-type `maximal_ineq` and fills in the strong-type form.

## Summit A — continuous-time Itô formula (2026-06-02)

The bounded-derivative continuous-time L² Itô formula (`ito_formula_L2_bddDeriv`,
`Foundations/ItoFormulaCLM.lean`) is a five-module chain that reuses, rather than
reinvents, the Mathlib / BrownianMotion-package machinery:

- **A1** `WeightedQuadraticVariation.lean` — weighted QV via the weak-Markov/Gaussian-
  kurtosis engine (`memLp_increment_sq_centered_two`, `IsPreBrownian.hasLaw_sub`); the
  Riemann-sum convergence is built from scratch (Mathlib has no Riemann-sum lemma) with a
  `Nat.find` partition-cell argument + `tendsto_integral_of_dominated_convergence`.
- **A2** `ItoFormulaRemainder.lean` + `GaussianMoments.integral_pow6_gaussianReal` — the
  Gaussian 6th moment reuses Degenne's `centralMoment_two_mul_gaussianReal` (package); the
  cubic Taylor bound reuses Mathlib's `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`.
- **A3** `ItoIntegralRiemannBridge.lean` — generalizes `ItoIntegralBrownian.itoIntegralCLM_T_brownian`
  (integrand `id → φ`), reusing the entire `stepSP` / `simpleAssembly_T` / `itoIntegralCLM_T`
  CLM stack; the trim-L² limit reuses `memLp_uncurry_trim_T` + Mathlib's
  `aestronglyMeasurable_of_tendsto_ae` / `tendsto_integral_of_dominated_convergence`.
- **A-core / A4** `ItoFormulaC2.lean` / `ItoFormulaCLM.lean` — assemble `DiscreteIto.discrete_ito_formula`
  with A1/A2/A3 via uniqueness of L² limits.

**Bridge opportunity:** the one clean upstream candidate remains `IsPiSystem` for
`ElementaryPredictableSet` (off the Summit-A critical path; see
`docs/ito-integral-clm-deferred.md`). No reinvention introduced.

**Upstream opportunity (2026-06-03 audit):** the BrownianMotion package ships
`StochasticIntegral/SquareIntegrable.lean` with sorry'd
`IsSquareIntegrable.ae_tendsto_limitProcess` and `tendsto_eLpNorm_two_limitProcess`;
our sorry-free `L2MartingaleConvergence` engine (a.e. + L² convergence off our Doob
L^p maximal inequality) is the natural donor toward discharging both upstream. The
package's `QuadraticVariation.lean` (Doob–Meyer predictable-part abstraction, sorry'd)
is orthogonal to our partition-limit QV files — no overlap either way.
