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
| N | **Change of numéraire — the abstract backbone consumed by the BS stock numéraire.** `Foundations/Numeraire.changeOfNumeraire` is the general price-invariance law `N₀·𝔼^{Q^N}[X/N_T] = B₀·𝔼^Q[X/B_T]` for `Q^N = Q.withDensity((N_T·B₀)/(N₀·B_T))` (a pure `integral_withDensity_eq_integral_toReal_smul` transport + cancellation of `N_T`, no integrability hypothesis), with `numeraireMeasure_isProbabilityMeasure` for the `N/B`-martingale normalization. `BlackScholes/StockNumeraire.stockNumeraireMeasure_eq_numeraireMeasure` proves the previously hand-rolled stock-numéraire measure `dQ^(S)/dQ = e^{−rT}·S_T/S₀` **is** the instance `B_T = e^{rT}`, `B₀ = 1`, `N = S`, so `Φ(d₁) = Q^(S)(S_T > K)` now stands on the general theorem. First IV↔I numéraire seam. | `Foundations/Numeraire.lean`, `BlackScholes/StockNumeraire.lean` | NEW (2026-07-03); WIRED (corpus `mf-change-of-numeraire`) |
| N.2 | **Exchange option as a second change-of-numéraire instance.** `BlackScholes/ExchangeOption.exchangeOption_numeraire_price`: Margrabe's `S²`-numéraire valuation `S²₀·𝔼^{Q^(S²)}[max(S¹/S²−1,0)] = 𝔼^Q[max(S¹−S²,0)]` is `changeOfNumeraire` at `X =` exchange payoff, `N = S²`, `B ≡ 1`, composed with the existing `exchange_payoff_eq_ratio`. Makes the informal "value in the `S²`-numéraire" a theorem-level instance. (Garman's normal form is closed-form `d₁/d₂` algebra — no measure — so not wireable; not fabricated.) | `BlackScholes/ExchangeOption.lean` | NEW (2026-07-03); WIRED (corpus `mf-exchange-numeraire`) |
| N.3 | **Numéraire-portfolio ⟹ EMM (Kelly, discrete).** `Performance/KellyNumeraire.kellyNumeraire_isRiskNeutral`: the growth-optimal (Kelly) terminal wealth, used as deflator, sends the physical measure to the risk-neutral one — the GOP-deflated probabilities `q₊ = p/W*₊ = 1/(b+1)`, `q₋ = (1−p)/W*₋ = b/(b+1)` are `p`-independent (the Kelly first-order condition `1+f*b = p(b+1)`) and make the bet a martingale (`q₊·b + q₋·(−1) = 0`). Consumes `kellyFraction` / `kellyGrowth_deriv_at_kelly` from `Performance/Ratios`. The discrete shadow of the continuous Long/Platen benchmark theorem. Wires `Performance/Kelly` ⟷ EMM — the IV↔I seam the architecture doc named ABSENT. | `Performance/KellyNumeraire.lean` | NEW (2026-07-03); WIRED (corpus `mf-kelly-numeraire-emm`) |
| N.4 | **T-forward measure — the zero-coupon bond as a fourth change-of-numéraire instance.** `FixedIncome/ForwardMeasure.forwardMeasure` takes `Q^T = numeraireMeasure Q (e^{rT}) 1 1 e^{−rT}` (bond slots `N_T = P(T,T) = 1`, `N_0 = P(0,T) = e^{−rT}`, money-market reference `B_T = e^{rT}`, `B_0 = 1`); `forwardMeasure_price` reads off `e^{−rT}·𝔼^{Q^T}[X] = 𝔼^Q[e^{−rT}X]` from `changeOfNumeraire`, and combined with the discounted-terminal EMM property (`Forward.discounted_terminal_eq_S0`) yields the forward price `𝔼^{Q^T}[S_T] = S_0·e^{rT} = S_0/P(0,T) = F(0,T)` (`forwardMeasure_bs_expected_terminal`). Honest scope: the constant-rate ZCB gives `dQ^T/dQ = 1` so `Q^T = Q`; the construction carries verbatim to a stochastic short rate where `Q^T ≠ Q`. The finance-delivery track's next numéraire instance after the stock (N) and `S²` (N.2). | `FixedIncome/ForwardMeasure.lean` | NEW (2026-07-07); WIRED (corpus `mf-forward-measure-spot`) |
| 53 | Pricing kernel from two-state FTAP: discounted EMM weights `q_state = e^{−rT} · q^{EMM}` form a valid pricing kernel — non-negative, sums to bond price, linear in payoff. Composes `Foundations/StatePrices.lean` (linear functional axioms) with `Foundations/FTAPTwoState.lean` (Phase 37 EMM construction). Bond price + monotonicity from FTAP, not assumed separately. *(Round 6: the composition made definitional — `statePrices_two_state := e^{−rT} · emmWeight{Up,Down}` consumes FTAPTwoState's named weights, and the kernel IS `statePricePricing`, its lemmas consumed from `StatePrices`.)* | `Foundations/PricingKernel.lean` | NEW (phase 53); WIRED (corpus `mf-pricing-kernel-butterfly`, 2026-06-09); recomposed (round 6, 2026-06-09) |
| 53a | **Payoff convexity through a non-negative linear pricing functional** (`ConvexPricingFunctional`): call-price convexity in strike, butterfly non-negativity, implied-PDF non-negativity — one principle, consumed by `PricingKernel`'s FTAP butterfly (corpus `mf-pricing-kernel-butterfly`). One of the five documented Foundations→pricing application bridges; this row records its layering exception. | `Foundations/ConvexPricingFunctional.lean` | catalogued (round 6, 2026-06-09) |
| 44a+b | CRR binomial scheme as discrete-Itô process: per-step drift `(2p − 1)·σ√Δt` (= `q · log u + (1−q) · log d`) and per-step QV `4p(1−p)·σ²·Δt` (= variance of log-return), identified algebraically (44a). Summed over `n` steps: drift → `(r − σ²/2)·T`, QV → `σ²·T` (44b, composing existing `crr_drift_limit_n` from `DriftLimit.lean` and `crr_variance_limit` from `CRRConvergence.lean`). Connects Phase 35 discrete-Itô framework to existing CRR machinery. | `Binomial/CRRDiscreteIto.lean` | NEW (phase 44a+b) |
| 44c | CRR → BS price convergence: the n-step binomial call price converges to the Black-Scholes call price (`binomialPrice_call_tendsto_bs`), via a characteristic-function + Lévy-continuity route to convergence in distribution and a put-call-parity argument (the bounded put converges weakly; parity lifts it to the call — no triangular-array CLT needed). The literal closed form `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)` is `binomialPrice_call_tendsto_bs_closed`, chaining that put-parity limit through `bs_put_formula` (on the standardised terminal law) + `Phi_neg`. | `Binomial/CRRCharFun.lean`, `Binomial/CRRClosedForm.lean` | DONE (phase 44c) |
| 42 | Multi-state FTAP: **forward direction proved in arbitrary finite state + finite assets** (`noArbitrage_of_emm_multi`: EMM ⟹ no arbitrage, by the `Finset.sum_comm` swap + `Finset.sum_pos'` positivity argument). **The open piece** (Phase 42c): constructing `q` from no-arbitrage via Hahn-Banach separation / Farkas (Mathlib has Hahn-Banach in normed spaces but not specialised to finite-dim with positivity cone). Forward direction generalises Phase 37. | `Foundations/FTAPMultiState.lean` | NEW (phase 42 forward); WIRED forward (corpus `mf-ftap-multi-state-forward`, 2026-06-09) |
| 40 (GBM specialisation) | **Itô's lemma L¹-expectation form specialised to GBM-log** (`f = log` on `dS = r S dt + σ S dB`). `bsLogReturn r σ T Z := (r − σ²/2)·T + σ·√T·Z` collapses `log(bsTerminal/S_0)` to a linear function of `Z`. Under `BSCallHyp`: `E_Q[bsLogReturn] = (r − σ²/2)·T` (the Itô-corrected drift integrated) and `Var_Q[bsLogReturn] = σ²·T` (the QV over `[0, T]`). **First L¹-form Itô identity** in the library — the path-wise version remains gated on full L²-density convergence (which Nagy 2026 also leaves "structurally verified"). | `BlackScholes/GBMLogMoments.lean` | NEW (phase 40 GBM specialisation) |
| 28 | **Forward-rate / hazard / force-of-mortality via Mathlib `intervalIntegral` + the `ExponentialDiscount` principle** (was deferred below). `forwardRate_eq_neg_log_discount`, `force_eq_neg_log_deriv_survival`, `hazard_eq_neg_log_deriv_survival` express `rate = −d/dt log Q` against the actual discount `exp(−H)`, via `rate_eq_neg_log_deriv` + the FTC (`integral_hasDerivAt_right`). Mortality/HazardCurve previously stated this only in prose. Makes `Foundations/ExponentialDiscount` load-bearing (0 → 3 consumers). | `FixedIncome/ForwardRate.lean`, `Actuarial/Mortality.lean`, `FixedIncome/HazardCurve.lean` | NEW (2026-05-23 principle-audit pass) |
| L1 (Girsanov) | **The risk-neutral measure derived from the physical measure** (static Girsanov). `BSCallHyp.exists_of_physical`: `Q := P.withDensity(exp(c·W−c²/2))` is a probability measure under which the recentred driver is standard normal, so `BSCallHyp` holds — the EMM is *constructed*, not assumed. Chain: `gaussian_esscher_pdf` → `gaussianReal_withDensity_esscher` → `map_withDensity_comp` (upstreamable) → `hasLaw_esscher_tilt` → `hasLaw_sub_const`. `bsTerminal_physical_eq_riskNeutral` shows the same asset is repriced with drift `μ→r`. See [`leaps.md`](leaps.md). | `Foundations/GaussianGirsanov.lean` | NEW (2026-05-23, leap 1) |
| L2 (genesis cascade) | **Physical → EMM → pricing.** `discounted_terminal_eq_S0_of_physical` (the constructed `Q` is a genuine EMM: `E_Q[e^{−rT}S_T]=S₀`) and `bs_call_formula_of_physical` (full physical→price chain). Additive bridges consuming the prior pricing theorems — `GaussianGirsanov` made load-bearing. | `Foundations/GaussianGirsanov.lean` | NEW (2026-05-23, leap 2) |
| Girsanov-continuous (const → simple → continuous-adapted → **bounded predictable** θ, full `Q`-BM) | **The distributional Girsanov, continuous-time, constant θ — FULLY CLOSED.** Under `Q = P.withDensity(exp(−θ X_T − ½θ² T))`, the drift-corrected `B^θ_t = X_t + θ t` is a genuine `Q`-Brownian motion (`Btheta_isQBrownianMotion`): zero start, Gaussian increments `B^θ_t − B^θ_s ~ N(0, t−s)` (`Btheta_increment_map_eq_gaussianReal`; marginal `Btheta_map_eq_gaussianReal`), **and** independence of disjoint increments (`Btheta_increments_indepFun`). The laws come from the Bayes engine `changeOfMeasure_setIntegral_eq` + Wald `P`-martingales (`Wald(−θ)`, `Wald(a−θ)`) giving every `Q`-conditional MGF, then Mathlib's complex-MGF machinery (`integrableExpSet_eq_of_mgf` → `eqOn_complexMGF_of_mgf` → `ext_of_complexMGF_eq`). **The increment independence dissolves the presumed Mathlib gap** ("conditional-MGF ⟹ independence" is absent — only the reverse `condExp_indep_eq` exists): instead of that lemma, `indepFun_iff_charFun_prod` reduces independence to the joint charFun factorising, and the joint charFun at `w=(w₁,w₂)` is the charFun-at-`1` of the Gaussian law of the linear combination `w₁·I₁+w₂·I₂` (from the joint-MGF factorisation — a `condExp_mul_of_stronglyMeasurable_left` pull-out), so it factors into the marginal Gaussian charFuns (`charFun_gaussianReal`) — **no adapted-integrand Itô formula**. Since 2026-07-06 the whole chain is factored through the reusable, process-agnostic `Foundations/ExpMartingaleQBrownian.isQBrownianMotion_of_expMartingale`: const-θ supplies only its exponential martingale (`expBtheta_isQMartingale`, packaged as `IsExpQMartingale`) and instantiates the characterization — the same module now also instantiated for the **simple (piecewise-constant adapted) θ** case (`Btheta_simple_isQBrownianMotion`, corpus `gir-simple-adapted`, `full`, `Foundations/GirsanovSimpleTheta.lean`): supply the simple-θ exponential martingale — via the spine `simple_spine_ae` (`E^{−c}·exp(a·B^θ − ½a²·) =ᵐ E^{a−c}`, the tilted simple Doléans density) fed to the Bayes engine, with an `L²`-Hölder mixed-time integrability (`Z_T² = E^{−2c}_T·exp(∑ c_i²Δτ_i)`) — and read off the `Q`-Brownian properties. This is the general bounded-**adapted**-θ Girsanov for the simple case, strictly beyond constant θ. **Continuous bounded-adapted θ is now CLOSED too (2026-07-09):** `Foundations/GirsanovAdaptedTheta.Btheta_isQBrownianMotion_adapted` (corpus `gir-thm-9.1.8`, `full`) proves `B^θ_u = B_u + ∫₀ᵘθ ds` is a `Q`-Brownian motion for bounded `𝓕`-adapted path-continuous θ under `Q = μ.withDensity(exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds))` — spine-free, passing the simple-θ identity to the limit through the a.e.-subsequence set-integral engine `tendsto_setIntegral_of_subseq_ae_of_sq_bound` (route-A L⁴/AM-GM uniform `L²`), no adapted-integrand Itô formula and no Novikov crux. **Bounded PREDICTABLE θ is now CLOSED too (2026-07-10, Rung 1):** `Foundations/GirsanovPredictableTheta.Btheta_isQBrownianMotion_predictable_of_bdd` (corpus `gir-thm-9.1.8-predictable`, `full`) drops the path-continuity of `gir-thm-9.1.8` and proves `B^θ_u = B_u + driftContinuousMod θ̂ u` is a `Q`-Brownian motion for a bounded **predictable** θ — the honest domain of the Itô `L²` integral. `driftContinuousMod θ̂` is the genuinely-`𝓕`-adapted modification of the honest drift `∫₀ᵘθds` (so `IsExpQMartingale.adapted` holds with strong, not merely a.e., measurability). The front half is a **Route-B marshalled** density approximation (`Foundations/SimpleProcessPartition.lean`): θ is approximated in `L²` by dense simple processes marshalled into single-partition `(s,c)` form, so `isExpQMartingale_BthetaSimple` applies per `n`; now **all three** integrand functionals — the stochastic integral `∑cᵢΔB → ∫θdB`, the drift `∑cᵢΔτ → ∫₀ᵘθds`, and the quadratic variation `∑cᵢ²Δτ → ∫₀ᵀθ²ds` — converge in `μ`-measure (via the drift-modification tower's `L²`-slice energy identity `drift_slice_energy_eq`), and are fused through a common a.e.-subsequence (`exists_subseq_tendsto_ae₂`) into the same set-integral engine plus a generic Fatou-`L²` limit (`memLp_two_of_subseq_ae_of_sq_bound`), keyed on the partition-generic uniform moment bounds of `Foundations/GirsanovSimpleDoleansMoments.lean`. The const → simple → continuous-adapted → **predictable (Rung 1)** arc is COMPLETE; only the strictly more general `L²`/progressive-θ under Novikov (unbounded, Rung 2, `sc-thm-9.1.8`) remains open. | `Foundations/GirsanovConstantTheta.lean`, `Foundations/GirsanovSimpleTheta.lean`, `Foundations/GirsanovAdaptedTheta.lean`, `Foundations/GirsanovPredictableTheta.lean`, `Foundations/GirsanovSimpleDoleansMoments.lean`, `Foundations/SimpleProcessPartition.lean`, `Foundations/ExpMartingaleQBrownian.lean` | NEW (2026-07-05); WIRED (corpus `gir-const-theta-marginal`, `gir-const-theta-qbm`, `gir-simple-adapted`, `gir-thm-9.1.8`, `gir-thm-9.1.8-predictable`); abstraction + simple-θ 2026-07-06; continuous-adapted 2026-07-09; bounded-predictable 2026-07-10 |
| L3 (Margrabe) | **Multivariate exchange option = one-asset BS on the ratio.** Effective vol `√(σ₁²+σ₂²−2ρσ₁σ₂)` (`margrabe_effective_variance`, via covariance bilinearity — makes the `BivariateGaussian` covariance machinery load-bearing); `margrabe_eq_bsVGarman` (Margrabe is a `GarmanNormalForm` instance, its 4th consumer); `margrabe_parity`; `margrabe_price_via_call` (price-level: `S²₀·E_Q[max(R_T−1,0)] = margrabePrice` via `bs_call_formula` on `R=S¹/S²`). | `BlackScholes/ExchangeOption.lean` | NEW (2026-05-23, leap 3) |
| L4 (adapted Itô isometry) | **The genuinely-stochastic Itô isometry**, for *random adapted* integrands — distinct from the deterministic Wiener integral (`WienerIntegralL2.lean`). Cross-terms vanish by the weak Markov property `IsPreBrownian.indepFun_shift` (`ΔBₖ ⊥ 𝓕_{tₖ}`), not by covariance. `ito_isometry_discrete`: `E[(Σ φₖ·ΔBₖ)²] = Σ E[φₖ²]·Δtₖ`; capstone `ito_isometry_brownian_self` (`∫₀ᵀ B dB`, fully discharged). Makes `IsPreBrownian.hasIndepIncrements`/`indepFun_shift` load-bearing, overturning the prior "increment independence is WIP upstream" framing. See [`leaps.md`](leaps.md). | `Foundations/ItoIsometryAdapted.lean` | NEW (2026-05-23, leap 4 discrete) |
| L3-grounding (Margrabe) | **The ratio's `BSCallHyp` derived, not assumed** — closes leap 3 end-to-end. `normalizedSpread_hasLaw_std`: the normalized log-spread driver `(σ₁W₁−σ₂W₂)/σ_eff` of a jointly-gaussian pair is `N(0,1)` (gaussianity preserved under `HasGaussianLaw.map_of_measurable`; variance pinned to 1 by `margrabe_effective_variance` — makes `Foundations/BivariateGaussian` load-bearing). `margrabe_bsCallHyp_of_gaussian`: the two-asset grounding reduces to leap-1 Girsanov (`BSCallHyp.exists_of_physical`) on that single effective driver. `margrabe_price_of_gaussian` composes the grounding with `margrabe_price_via_call` for a hypothesis-free exchange-option *price*. See [`leaps.md`](leaps.md). | `BlackScholes/MargrabeGrounding.lean` | NEW (2026-05-23, leap 3 grounding) |
| VS-drift | **Variance-swap drift immunity**: realized variance of GBM log-returns → `σ²T` in **L²** for **any** drift parameter — the fair strike is a QV functional, immune to the physical-vs-risk-neutral drift. The GBM log-price is an Itô process with constant-slope drift, so `ItoProcessQV.tendsto_qv_ito_process` applies verbatim; strengthens phase 34 (expectation-level, risk-neutral drift only) to mean-square concentration for every drift. First pricing consumer of `ItoProcessQV`. | `Foundations/VarianceSwapDriftImmunity.lean` | NEW (2026-06-06) |
| FtD | **First-to-default spread additivity**: basket survival = `survivalProbability (Σ rates) 0 t` and the FtD credit spread = `Σ` single-name hazards, for jointly independent exponential default times. Pure bridge — `ExpMin.minimum_survival` (previously consumed only by `dist-exp-min`) rewritten in the `Credit.lean` vocabulary; the spread reading falls out of the existing `creditSpread_eq_hazard`. | `FixedIncome/FirstToDefault.lean` | NEW (2026-06-06) |
| Merton | **Merton (1976) jump-diffusion as a Poisson mixture**: `mertonCallPrice := ∫ n, C_BS(spot_n, vol_n) ∂(poissonMeasure Λ)` — the price is an honest expectation over the jump count; the textbook series, the compensation identity `E[spot_N] = S₀` (new Poisson pgf `E[x^N] = e^{Λ(x−1)}`, `Foundations/PoissonPgf.lean`, absent from Mathlib), and put–call parity are theorems. Every term separately grounded as a discounted conditional expected payoff via `bs_call_formula`/`bs_put_formula` on `(ℝ, gaussianReal 0 1)`. Terminal-mixture-law scope; the jump SDE is upstream-gated. | `BlackScholes/MertonJumpDiffusion.lean` + `Foundations/PoissonPgf.lean` | NEW (2026-06-06) |
| FK | **Feynman–Kac → Black–Scholes PDE keystone** (closes the two-tower gap): the BS PDE `−∂_τV + ½σ²S²∂_SSV + rS∂_SV − rV = 0` derived **independently of Itô**, from the heat-kernel representation `feynmanU g t x = ∫ z, g z · K(t, z−x) dz`. The crux is the heat kernel's **joint Fréchet-differentiability** `hasFDerivAt_heatKernel` (the one genuinely-2D ingredient — makes a single curve chain rule available), feeding `hasDerivAt_feynmanU_{t,x,xx}` (dominated differentiation under the integral, routed through the parametric skeleton `hasDerivAt_integral_mul_kernelFamily`) and the kernel identity `feynmanU_heat_equation` (`∂_t K = ½ ∂_xx K`). The BS Greeks `hasDerivAt_bsV_{tau,S,SS}_fk` follow by the log-transform `S = eˣ` + discount, and the drift cancellation (`U_x` coeff `−(r−σ²/2)−½σ²+r = 0`, `U_xx` coeff `−½σ²+½σ²=0`) assembles the PDE. Makes the previously-orphan `feynmanU` heat flow load-bearing for pricing. Constant-coefficient scope; variable-coefficient FK (local-vol/Heston) + fully-general continuous-`g` PDE + uniqueness remain open. **Supersedes** [`feynman-kac-growth-deferred.md`](feynman-kac-growth-deferred.md). | `Foundations/FeynmanKacHeatEquation.lean` + `BlackScholes/PDEFromFeynmanKac.lean` (corpus `sc-bs-pde-feynman-kac`) | NEW (2026-06-08) |
| WG | **The deterministic-integrand Wiener integral is Gaussian → Vasicek terminal law derived** (the *first Itô-tower consumer in FixedIncome*, an Itô-side counterpart to the Itô-independent FK bridge above). `Foundations/WienerIntegralGaussian.lean` proves `μ.map (wienerIntegralLp B hB T f) = gaussianReal 0 ‖f‖²` — the distribution the isometry construction (`WienerIntegralL2`) left open, via the characteristic-function route: simple-process Gaussianity (`IsGaussianProcess.of_isGaussianProcess` on the scaled-increment family + `HasGaussianLaw.map_eq_gaussianReal`, mean `0` + variance the isometry) then density + a `|t|`-Lipschitz-charFun `DenseRange.induction_on` + `Measure.ext_of_charFun`. Its consumer `FixedIncome/VasicekSDEGaussian.lean` (`vasicekShortRate_hasLaw_gaussian`) makes the Vasicek SDE terminal law a *theorem*: `r_T = mean + σ ∫₀ᵀ e^{−κ(T−s)} dB_s ~ N(vasicekSDEMean, σ²(1−e^{−2κT})/(2κ))`, with the variance pinned by the FTC integral `∫₀ᵀ e^{−2κ(T−s)} ds` and the affine map via `gaussianReal_const_mul`/`gaussianReal_const_add`. Retires row 41's "stated, not derived". Honest scope: deterministic integrand (the genuinely-random-integrand local-martingale Itô formula remains the open localization frontier). | `Foundations/WienerIntegralGaussian.lean` + `FixedIncome/VasicekSDEGaussian.lean` (corpus `sc-wiener-integral-gaussian`, `mf-vasicek-sde-terminal-gaussian`) | NEW (2026-06-27) |
| WG.2 | **Vasicek zero-coupon bond price — the affine term structure** (the *second* Itô-tower consumer in FixedIncome, one integration up from WG). `FixedIncome/VasicekBondPrice.vasicekBondPrice_affine` prices the bond `P(0,T) = 𝔼[exp(−∫₀ᵀ r_s ds)]` as the Gaussian Laplace transform of the integrated short rate, collapsing to `P(0,T) = A(T)·exp(−B(T)·r₀)`, `B(T) = (1−e^{−κT})/κ`. Fubini-free: the integrated rate `∫₀ᵀ r_s ds = M(T) + σ∫₀ᵀ g dB` is carried in its Wiener representation (integrated OU kernel `g(u) = (1−e^{−κ(T−u)})/κ`, the deterministic time-order swap cited as the modelling bridge — parity with WG's OU-solution model), its Gaussian law `N(M, σ²V)` from `wienerIntegralLp_hasLaw_gaussian` + the FTC variance integral `∫₀ᵀ g² = V(T)` (`vasicekIntegratedKernel_integral_sq`), and the price factors `exp(−M)·𝔼[exp(−σ∫g dB)] = exp(−M + σ²V/2)` by the centred Gaussian MGF `integral_exp_mul_gaussianReal_zero` at `−σ`. Makes `vasicekShortRate_hasLaw_gaussian`'s Gaussian machinery load-bearing for *pricing*, not just the marginal law. | `FixedIncome/VasicekBondPrice.lean` (corpus `mf-vasicek-bond-price`) | NEW (2026-07-07) |
| WG.3 | **The Wiener integral of a step indicator is the increment → geometric-Asian lognormality.** `Foundations/WienerIntegralIndicator.wienerIntegralLp_stepIndicator` records the defining identity `∫ 𝟙_{(s,t]} dB = B_t − B_s` (`LinearMap.extendOfNorm_eq` on the single-basis coefficient, since both assembly maps are `Finsupp.linearCombination` of their generators) — the piece that lets a finite sum of Brownian values be read as one Wiener integral of a deterministic step kernel. First consumer `BlackScholes/AsianGeometric.asianGeom_driver_hasLaw`: the two-date geometric-Asian log-driver `(B_s + B_t)/2` is Gaussian `N(0, (3s+t)/4)` (`= ∫ ½(𝟙_{(0,s]} + 𝟙_{(0,t]}) dB`, `wienerIntegralLp_hasLaw_gaussian` for the law, variance the kernel `L²`-norm via the Brownian covariance `integral_mul_eval` `∫ B_u·B_v = min(u,v)` + zero-start `B_0 = 0`). Makes the geometric average a priceable lognormal, complementing the AM-GM payoff bound `mf-asian-geom-le-arith-two`. Honest scope: two dates; the n-date Finset covariance sum is unblocked by the same crux. | `Foundations/WienerIntegralIndicator.lean` + `BlackScholes/AsianGeometric.lean` (corpus `mf-asian-geom-driver-gaussian`) | NEW (2026-07-08) |

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

**Rung-3 unlock — the localized Itô formula reaches GBM (2026-06-28).** The
bounded-derivative time-dependent formula `ito_formula_td_L2_bddDeriv` cannot reach the
Black–Scholes value function `f(t,x) = S₀ exp((r−σ²/2)t + σx)` (derivatives `∝ exp(σx)`,
unbounded). `Foundations/ItoFormulaLocalized.lean` lifts it to **at-most-exponential
growth** (`ito_formula_td_localized`, corpus `sc-ito-formula-localized`, `full`) by an
L²-cutoff localization that *consumes* the bounded engine rather than re-proving it:
- the smooth truncation `SmoothTrunc` is the antiderivative of a Mathlib `ContDiffBump` —
  smoothness + compact support hand every derivative and bound to Mathlib, no explicit
  calculus (`ContDiff.deriv'`, `HasCompactSupport.exists_bound_of_continuous`);
- the dominated-convergence dominators are integrable because Brownian marginals have
  *every* exponential moment — `Foundations/BrownianExpMoment.lean` transfers Mathlib's
  Gaussian MGF (`mgf_id_gaussianReal`) along `B_s ~ N(0,s)`, a small reusable base stone;
- the new reusable base stone `pathIntegral_expGrowth_memLp` (the exp-growth path integral
  in L²) reuses the exposed `WeightedQuadraticVariation.tendsto_riemann_continuous`
  (generalized to a *local* bound) via Fatou over Riemann sums + discrete Cauchy–Schwarz —
  no Tonelli, no joint measurability;
- the limit is identified by the Itô **isometry** `itoIntegralCLM_T_norm` (Cauchy transfer)
  + completeness + CLM **continuity** — the deep Itô tower (QV, isometry, CLM) carries the
  pricing weight with zero new analytic machinery beyond the cutoff.

**The rung-3 unlock realized — GBM decomposed by the Itô integral (2026-06-28).** The localized
formula was the *capability*; `Foundations/ItoFormulaGBM.lean` is the **first actual
pricing-ward consumer of the analytic Itô tower** (corpus `sc-ito-formula-gbm`,
`sc-discounted-gbm-ito`, both `full`). This closes the standing two-tower disconnect *on the
Itô side*: until now the deep tower (`ItoIntegralCLM`/`ItoFormulaTD`/`ItoFormulaLocalized`) had
**zero** pricing consumers — GBM/BS pricing ran via the algebraic `ItoLemma`/`PDEFromIto` tower
and Feynman–Kac, and `discountedGBM_isMartingale` (`ContinuousFTAP.lean`) was proved via the
Wald exponential, never the Itô integral.
- `ito_formula_gbm`: `Ŝ(T) − Ŝ(0) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ m·Ŝ ds` for the GBM value
  `Ŝ(t)=S₀ exp((m−σ²/2)t+σ B_t)`, the stochastic term the **genuine continuous Itô integral**.
- Route = **localization in time** (the classic argument): the GBM value is `t`-exponential and
  fails the localized formula's `t`-uniform growth, so the localized formula is applied to the
  time-localized exponent `S₀ exp((m−σ²/2)·φₙ(t)+σx)` (`φₙ=SmoothTrunc.cut n`, `n=⌈T⌉₊`), the
  identity on `[0,T]` yet globally bounded; on `[0,T]` `φₙ=id`, `φₙ'=1`, so the localization
  drift `(m−σ²/2)·Ŝ` and the Itô correction `½σ²·Ŝ` collapse to `m·Ŝ`. The only new ingredient
  is the plateau-slope lemma `SmoothTrunc.phi'_eq_one_of_lt` (derivative-uniqueness vs `id`).
- `discountedGBM_eq_itoIntegral` (`m=0`): the drift vanishes, so the discounted-GBM increment
  is a **pure Itô integral** — the Itô-integral content of the discounted-GBM martingale.
  *Open:* re-grounding `discountedGBM_isMartingale` at the **process** level (all `t`, Brownian
  filtration) on the Itô integral, which this terminal-time decomposition opens.

**The Itô formula against a general Itô process (2026-06-28).** `Foundations/ItoFormulaItoProcess.lean`
generalizes the GBM decomposition from the exponential value function to an arbitrary `C³`
exponential-growth `f`. For the constant-coefficient Itô process `X_t = X₀ + b·t + σ B_t`,
`ito_formula_itoProcess` gives `f(X_T) − f(X₀) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ (f'(X)·b + ½f''(X)·σ²) ds`
— i.e. `∫ f'(X) dX + ½∫ f''(X)σ² ds`, the diffusion the genuine continuous Itô integral. Same
time-localization of the `b·t` exponent as GBM (`ito_formula_gbm` is the `f = S₀·exp` case);
constant coefficients keep the diffusion integrand `σ f'(X_s)` a function of `B_s`, which the tower
handles directly. The shared `SmoothTrunc` plateau lemmas (`cut_eq_id_of_abs_le`,
`cutD1_eq_one_of_abs_lt`, `phi'_eq_one_of_lt`) now live in `ItoFormulaLocalized.lean` so both
formulas consume them. *Open:* **adapted**-coefficient drift/diffusion — the random-integrand
semimartingale Itô formula, a new tower layer.

## Itô's lemma as a process — analytic Itô tower ↔ pathwise CLM tower

`ItoFormulaProcess.lean` (`ito_formula_td_process`) bridges the two Itô towers that had run in
parallel: the **analytic** terminal Itô-formula tower (`ItoFormulaTD`/`…Localized`, a single
fixed-`T` `Lp` statement) and the **pathwise** continuous-local-martingale tower
(`ItoIntegralProcess…LocalMartingaleInfinite`, the integral as a process on `[0,∞)`). It lifts the
terminal formula to a process identity for every `t ≤ T` — `f(t,B_t) − f(0,B_0) =ᵐ itoProcessL2Inf
t F + ∫₀ᵗ (f_t + ½f_xx) ds` — so the compensated process is (a modification of) a continuous local
martingale: *Itô's lemma as a semimartingale decomposition*. The bridge is **one new stone**, the
canonical-witness exposure `ito_formula_td_L2_bddDeriv_explicit` (`gfx =ᵐ [f_x(·,B)]`) plus the
zero-extension `exists_fullHorizon_extension`; the horizon-matching is the *existing*
`itoProcessL2Inf_eq_itoProcessCLM`. No Markov property, no PDE. This makes the `[0,∞)` CLM tower
load-bearing as an Itô-formula consumer for the first time, and is the prerequisite for the
unrestricted-`C²` (Summit C) Itô formula. *Open:* Summit C; **adapted**-coefficient (random
integrand) drift/diffusion.

## The convex-duality unification — pricing tower ↔ risk tower (Phase 1, 2026-06-29)

`Foundations/ConvexDuality.lean` is the shared root that makes the no-arbitrage (pricing) and
coherent-risk (risk) towers one Hahn–Banach theorem. The cone-separation root
`exists_pos_separating_of_cone_disjoint_simplex` and its point-from-cone companion
`exists_separating_of_not_mem_cone` share two atoms (`functional_eq_sum_single`,
`functional_nonneg_on_cone`); the FTAP kernel `ConvexSeparation.exists_pos_dual_of_disjoint_stdSimplex`
is **re-derived** from the root (pricing side), and `RiskMeasures/AcceptanceSet.coherentRisk_isLUB` (the
finite-state ADEH representation, with `RiskMeasures/WorstCaseRisk.worstCase_isLUB` a concrete instance —
worst-case loss = sup over the whole simplex) is its risk-side instance.
`Foundations/SuperhedgingDuality.emm_le_superReplication` wires superhedging as the EMM bound. This is the
architecture doc's #1 unification (I↔IV), realized: *the FTAP separating functional and the coherent-risk
representation are the same separation theorem* — the two most-disconnected towers made one. *Open:* the
superhedging strong-duality **equality** (a finite-dim Farkas / polyhedral-cone-closedness Mathlib gap);
the Gaussian CVaR robust form (the continuous instance).

## The Girsanov change of measure — pricing tower ↔ Itô/Brownian tower (Phase 2, 2026-06-30)

The Black–Scholes equivalent martingale measure is now *constructed* as an explicit Girsanov density
change of the physical measure, not taken as given. `Foundations/Girsanov.bs_discounted_isQMartingale`
tilts `P` by `Q = withDensity(exp(−θX_T − ½θ²T))` (constant market price of risk `θ = (μ−r)/σ`) and
proves the discounted stock `S_0·exp((μ−r−σ²/2)t + σX_t)` a `Q`-martingale on `[0,T]` — retiring the
Wald shortcut of `ContinuousFTAP.discountedGBM_isMartingale`, which took `Q = P` from the start.

The bridge's reusable core is `Foundations/ChangeOfMeasure.changeOfMeasure_setIntegral_eq`, the abstract
Bayes engine: if the density process `Z` and the product `Z·D` are both `P`-martingales (with `Z_T ≥ 0`,
`D` adapted), then `D` is a `Q`-martingale on `[0,T]` — no stochastic calculus, only conditional
expectations (a Bayes pull-out via `condExp_mul_of_stronglyMeasurable_left`, plus a martingale
set-integral). The BS instance feeds it two Wald exponentials — `Z = waldExponential(−θ)` and
`Z·D = S_0·waldExponential(σ−θ)`, both `IsFilteredPreBrownian.waldExponential_isMartingale` (using
`μ−r = σθ`); the one genuinely new estimate is the mixed-time integrability of `D_u·Z_T`, handled by
AM–GM (`exp(σX_u)exp(−θX_T) ≤ exp(2σX_u)+exp(−2θX_T)`, each Gaussian-MGF-integrable).

This partially wires the architecture doc's Girsanov seam (I↔II), on the **martingale side**. **The
distributional side is now fully closed for constant θ** (`Btheta_isQBrownianMotion`, above): drift
removal → `Q`-Brownian, Gaussian *and independent* increments, reached via `indepFun_iff_charFun_prod`
on the Gaussian joint law. *Open:* the *general bounded-adapted*-`θ` Girsanov (`gir-thm-9.1.8`, the
drift-corrected `B^θ = B − ∫θ ds` for adapted `θ`) — its adapted drift needs an adapted-integrand Itô
formula / pathwise quadratic variation the Itô tower does not yet expose (every `ito_formula_*` is a
function of `B_t`, and the Itô-integral QV exists only in expectation).

## The continuous first-FTAP frame — pricing tower ↔ no-arbitrage (meaning 1, 2026-07-12)

`Foundations/ContinuousMarket` (the model-agnostic EMM frame) ↔ `Foundations/ContinuousFTAP`
(the `F = ℝ` discounted-GBM instance) ↔ `Foundations/NoArbitrageCore` (shared with the discrete FTAP).

- **ContinuousMarket → ContinuousFTAP.** `IsEMM` / `NoArbitrageSimple` / `isEMM_noArbitrageSimple`
  (the general forward theorem) are instantiated by `discountedGBM_isEMM` /
  `discountedGBM_noArbitrageSimple`, which package the existing `discountedGBM_isMartingale` (the
  operational continuous FTAP) as a concrete EMM. The frame gives the GBM martingale property its
  economic payoff: no simple-strategy arbitrage.
- **NoArbitrageCore shared by discrete + continuous.** `ae_zero_of_nonneg_of_integral_zero` (nonneg +
  zero mean ⟹ vanishes) is the common closing step of BOTH `FTAP.emm_implies_no_arbitrage` (discrete,
  via a martingale transform) and `ContinuousMarket.isEMM_noArbitrageSimple` (continuous, term-by-term
  via the bilinear `condExp` pull-out). One argument, two settings; each supplies its own zero-integral.
- **Seam to meaning 2.** `IsEMM`-on-a-process is exactly what Delbaen–Schachermayer produces, so the
  frame is a strict sub-object of the DS one and meaning 2 (NFLVR, admissible strategies, the converse)
  is additive. The physical-measure Girsanov EMM `Q ≠ P` (bounded-horizon) is the meaning-1.5 bridge.
