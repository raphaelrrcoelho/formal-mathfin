/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Axiom audit — the "axioms-clean" claim, build-enforced

The library's headline claim is that every `full` derivation is
`#print axioms`-clean: it depends only on the three standard Mathlib
axioms `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no extra
axioms.

This file turns that claim from a docstring assertion (in `docs/coverage.md`)
into a **build-enforced invariant**. Each `#guard_msgs in #print axioms`
block below pins the axiom dependencies of a headline / load-bearing
theorem. If any audited theorem ever picks up `sorryAx` (a `sorry` slipped
in) or a new axiom (a dependency changed), the `#guard_msgs` check fails and
**the build breaks**.

The audited set spans every area of the library — it is representative, not
exhaustive; extend it when a new load-bearing theorem lands. A theorem that
appears here is certified axioms-clean by `lake build`, not by assertion.

Note: pure-algebra theorems (closed by `ring`/`field_simp`) may legitimately
depend on a *subset* of the three (or none); those are pinned to their
actual set below. The invariant we enforce is "no `sorryAx`, no axiom
outside the standard three", which the pinned messages capture exactly.
-/

namespace MathFin.AxiomAudit

/-! ## Black-Scholes core -/

/-- info: 'MathFin.bs_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.bs_call_formula

/-- info: 'MathFin.bsP_eq_bsV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.bsP_eq_bsV

/-- info: 'MathFin.hasDerivAt_bsV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.hasDerivAt_bsV_S

/-- info: 'MathFin.bs_pde_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.bs_pde_holds

/-- info: 'MathFin.expected_terminal_eq_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.expected_terminal_eq_forward

/-! ## Feynman–Kac → Black–Scholes-PDE keystone -/

/-- info: 'MathFin.FeynmanKacHeatEquation.feynmanU_heat_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.FeynmanKacHeatEquation.feynmanU_heat_equation

/-- info: 'MathFin.bsV_satisfies_bs_pde_via_feynmanKac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.bsV_satisfies_bs_pde_via_feynmanKac

/-! ## Garman normal form + consumer-side corollaries -/

/-- info: 'MathFin.bsV_eq_bsVGarman_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.bsV_eq_bsVGarman_standard

/-- info: 'MathFin.black_futures_price_eq_bsVGarman' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.black_futures_price_eq_bsVGarman

/-- info: 'MathFin.bs_dividends_price_eq_bsVGarman' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.bs_dividends_price_eq_bsVGarman

/-! ## Gaussian MGF + lognormal moments -/

/-- info: 'MathFin.integral_exp_affine_gaussianPDFReal_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.integral_exp_affine_gaussianPDFReal_univ

/-- info: 'MathFin.nthMoment_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.nthMoment_terminal

/-- info: 'MathFin.secondMoment_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.secondMoment_terminal

/-- info: 'MathFin.variance_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.variance_terminal

/-- info: 'MathFin.bsLogReturn_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.bsLogReturn_mean

/-! ## Exponential-discount principle + the rate-recovery retrofits -/

/-- info: 'MathFin.rate_eq_neg_log_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.rate_eq_neg_log_deriv

/-- info: 'MathFin.forwardRate_eq_neg_log_discount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.forwardRate_eq_neg_log_discount

/-- info: 'MathFin.force_eq_neg_log_deriv_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.force_eq_neg_log_deriv_survival

/-- info: 'MathFin.hazard_eq_neg_log_deriv_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.hazard_eq_neg_log_deriv_survival

/-! ## Static Girsanov: the risk-neutral measure derived -/

/-- info: 'MathFin.gaussian_esscher_pdf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.gaussian_esscher_pdf

/-- info: 'MathFin.gaussianReal_withDensity_esscher' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.gaussianReal_withDensity_esscher

/-- info: 'MathFin.BSCallHyp.exists_of_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.BSCallHyp.exists_of_physical

/-- info: 'MathFin.bsTerminal_physical_eq_riskNeutral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.bsTerminal_physical_eq_riskNeutral

/-- info: 'MathFin.discounted_terminal_eq_S0_of_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.discounted_terminal_eq_S0_of_physical

/-- info: 'MathFin.bs_call_formula_of_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.bs_call_formula_of_physical

/-- info: 'MathFin.discounted_physical_terminal_eq_S0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discounted_physical_terminal_eq_S0

/-! ## Margrabe exchange option (first multivariate result) -/

/-- info: 'MathFin.margrabe_effective_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.margrabe_effective_variance

/-- info: 'MathFin.exchange_payoff_eq_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.exchange_payoff_eq_ratio

/-- info: 'MathFin.margrabe_eq_bsVGarman' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.margrabe_eq_bsVGarman

/-- info: 'MathFin.margrabe_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.margrabe_parity

/-- info: 'MathFin.margrabe_price_via_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.margrabe_price_via_call

/-! ## Convex pricing functional + FTAP / state-price wiring -/

/-- info: 'MathFin.statePricePricing_convexOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.statePricePricing_convexOn

/-- info: 'MathFin.callPrice_finiteState_butterfly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.callPrice_finiteState_butterfly_nonneg

/-- info: 'MathFin.stateprice_call_butterfly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.stateprice_call_butterfly_nonneg

/-! ## Binomial trees -/

/-- info: 'MathFin.americanCallPrice_le_binomialPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.americanCallPrice_le_binomialPrice

/-! ## Variance swap (QV limit) -/

/-- info: 'MathFin.tendsto_expected_bsLogPrice_equipartition_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.tendsto_expected_bsLogPrice_equipartition_sum

/-! ## L² quadratic variation of Brownian motion (Summit 1) + its in-probability corollary -/

/-- info: 'MathFin.QuadraticVariationL2.tendsto_qv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.QuadraticVariationL2.tendsto_qv

/-- info: 'MathFin.QuadraticVariationL2.tendstoInMeasure_qv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.QuadraticVariationL2.tendstoInMeasure_qv

/-- info: 'MathFin.BrownianQuadraticVariation.qv_equals_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.BrownianQuadraticVariation.qv_equals_t

/-! ## Expectation-form Itô / Feynman–Kac (the QV → ½f″ correction, from first principles) -/

/-- info: 'MathFin.FeynmanKacHeatEquation.heatConvolution_eq_add_integral_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.FeynmanKacHeatEquation.heatConvolution_eq_add_integral_deriv

/-- info: 'MathFin.FeynmanKacHeatEquation.expectation_ito' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.FeynmanKacHeatEquation.expectation_ito

/-- info: 'MathFin.FeynmanKacHeatEquation.expectation_ito_isPreBrownian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MathFin.FeynmanKacHeatEquation.expectation_ito_isPreBrownian

/-! ## Adapted Itô isometry (increment-independence cornerstone) -/

/-- info: 'MathFin.ItoIsometryAdapted.integral_adapted_mul_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.ItoIsometryAdapted.integral_adapted_mul_increment

/-- info: 'MathFin.ItoIsometryAdapted.integral_adapted_sq_mul_increment_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIsometryAdapted.integral_adapted_sq_mul_increment_sq

/-- info: 'MathFin.ItoIsometryAdapted.ito_isometry_discrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.ItoIsometryAdapted.ito_isometry_discrete

/-- info: 'MathFin.ItoIsometryAdapted.ito_isometry_brownian_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.ItoIsometryAdapted.ito_isometry_brownian_self

/-- info: 'MathFin.ItoIsometryAdapted.integral_adapted_mul_increment_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIsometryAdapted.integral_adapted_mul_increment_sq

/-- info: 'MathFin.ItoIsometryAdapted.ito_isometry_discrete_bilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIsometryAdapted.ito_isometry_discrete_bilinear

/-! ## Predictable-rectangle pairing (inner-product core of the continuous Itô integral) -/

/-- info: 'MathFin.ItoIsometryAdapted.adapted_indepFun_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIsometryAdapted.adapted_indepFun_forward

/-- info: 'MathFin.ItoIsometryAdapted.integral_two_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIsometryAdapted.integral_two_increment

/-- info: 'MathFin.ItoIsometryAdapted.rect_increment_pairing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIsometryAdapted.rect_increment_pairing

/-! ## Continuous Itô integral — foundational bridge (AdaptedAt ↔ natural filtration) -/

/-- info: 'MathFin.ItoIntegralL2.adaptedAt_of_measurable_natural' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralL2.adaptedAt_of_measurable_natural

/-! ## Continuous Itô integral as a CLM on `[0,T]` — the headline -/

/-- info: 'MathFin.ItoIntegralCLM.generateFrom_predictableRect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.ItoIntegralCLM.generateFrom_predictableRect

/-- info: 'MathFin.ItoIntegralCLM.assembly_isometry_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.ItoIntegralCLM.assembly_isometry_T

/-- info: 'MathFin.ItoIntegralCLM.simpleAssembly_T_denseRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.ItoIntegralCLM.simpleAssembly_T_denseRange

/-- info: 'MathFin.ItoIntegralCLM.itoIntegralCLM_T_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.ItoIntegralCLM.itoIntegralCLM_T_norm

/-! ## Unbounded-horizon `[0,∞)` Itô integral CLM (Summit B / B2) -/

/-- info: 'MathFin.ItoIntegralL2.itoIntegralL2_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.ItoIntegralL2.itoIntegralL2_norm

/-! ## Process-level elementary Itô integral `t ↦ (V●B)_t` — genuine `L²` content -/

/-- info: 'MathFin.ItoIntegralProcess.memLp_itoSimpleProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.ItoIntegralProcess.memLp_itoSimpleProcess

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcess_eq_itoSimple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.ItoIntegralProcess.itoSimpleProcess_eq_itoSimple

/-! ## Keystone `∫₀ᵀ B dB = ½(B_T² − B₀² − T)` through the CLM (its first genuine consumer) -/

/-- info: 'MathFin.ItoIntegralBrownian.itoIntegralCLM_T_brownian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.ItoIntegralBrownian.itoIntegralCLM_T_brownian

/-! ## Discrete squaring identity (the pathwise Itô keystone) -/

/-- info: 'MathFin.discrete_squaring_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.discrete_squaring_identity

/-! ## Itô's lemma for f(x) = x² — the L² continuous form (the QF-keystone) -/

/-- info: 'MathFin.itoSquared_L2_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.itoSquared_L2_tendsto

/-- info: 'MathFin.itoSquared_L2_tendsto_div2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.itoSquared_L2_tendsto_div2

/-! ## Itô chain items 3-6: polynomial remainders, 2D Itô, GBM-SDE, BS-PDE -/

/-- info: 'MathFin.discrete_cubing_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.discrete_cubing_identity

/-- info: 'MathFin.discrete_ito_formula_2d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.discrete_ito_formula_2d

/-- info: 'MathFin.hasDerivAt_gbmValue_space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.hasDerivAt_gbmValue_space

/-- info: 'MathFin.gbm_solves_sde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.gbm_solves_sde

/-- info: 'MathFin.bs_pde_eq_itoDrift2D_minus_rV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.bs_pde_eq_itoDrift2D_minus_rV

/-! ## Margrabe BSCallHyp grounding (leap-3 closure via gaussian vector) -/

/-- info: 'MathFin.normalizedSpread_hasLaw_std' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.normalizedSpread_hasLaw_std

/-- info: 'MathFin.margrabe_bsCallHyp_of_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.margrabe_bsCallHyp_of_gaussian

/-- info: 'MathFin.margrabe_price_of_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.margrabe_price_of_gaussian

/-! ## Portfolio / risk / performance -/

/-- info: 'MathFin.portfolioVarTwo_ge_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.portfolioVarTwo_ge_min

/-- info: 'MathFin.gaussianVaR_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.gaussianVaR_translation

/-- info: 'MathFin.gaussianCVaR_sub_VaR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.gaussianCVaR_sub_VaR

/-- info: 'MathFin.sharpeRatio_affine_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MathFin.sharpeRatio_affine_invariant

/-! ## Certified cross-domain bridges -/

/-- info: 'MathFin.portfolioVarN_diag_eq_herfindahl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarN_diag_eq_herfindahl

/-- info: 'MathFin.survivalFromForce_eq_hazardSurvival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.survivalFromForce_eq_hazardSurvival

/-- info: 'MathFin.gompertz_cumHazard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gompertz_cumHazard

/-! ## CRR → Black–Scholes characteristic-function convergence (the distributional CLT heart) -/

/-- info: 'MathFin.crr_charFun_pow_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_charFun_pow_tendsto

/-- info: 'MathFin.crr_charFun_pow_tendsto_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_charFun_pow_tendsto_gaussian

/-- info: 'MathFin.crr_tendsto_gaussian_inDistribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_tendsto_gaussian_inDistribution

/-! ## Continuous-time first FTAP (discounted GBM price is a Q-martingale) -/

/-- info: 'MathFin.discountedGBM_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discountedGBM_isMartingale

/-! ## Binomial pricing as discounted risk-neutral expectation (CRR→BS price bridge) -/

/-- info: 'MathFin.binomialPrice_eq_integral_convPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomialPrice_eq_integral_convPow

/-! ## CRR → Black–Scholes call-price convergence (the named theorem) -/

/-- info: 'MathFin.binomialPrice_call_tendsto_bs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomialPrice_call_tendsto_bs

/-! ## CRR → Black–Scholes call price in literal closed form `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)` -/

/-- info: 'MathFin.binomialPrice_call_tendsto_bs_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomialPrice_call_tendsto_bs_closed

/-! ## Summit A: bounded-derivative continuous-time Itô formula in L² (CLM-identified) -/

/-- info: 'MathFin.tendsto_weighted_qv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_weighted_qv

/-- info: 'MathFin.tendsto_ito_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_ito_remainder

/-- info: 'MathFin.ItoIntegralRiemannBridge.itoIntegralCLM_T_of_bdd_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.ItoIntegralRiemannBridge.itoIntegralCLM_T_of_bdd_cont

/-- info: 'MathFin.ito_formula_L2_bddDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_L2_bddDeriv

/-! ## Summit A′: time-dependent Itô formula in L² (CLM-identified) -/

/-- info: 'MathFin.tendsto_weighted_qv_process' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_weighted_qv_process

/-- info: 'MathFin.tendsto_ito_remainder_td' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_ito_remainder_td

/-- info: 'MathFin.ItoIntegralRiemannBridgeTD.itoIntegralCLM_T_of_bdd_cont_td' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.ItoIntegralRiemannBridgeTD.itoIntegralCLM_T_of_bdd_cont_td

/-- info: 'MathFin.ito_formula_td_L2_bddDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_td_L2_bddDeriv

/-! ## Localized (exponential-growth) time-dependent Itô formula — the rung-3 unlock to GBM -/

/-- info: 'MathFin.pathIntegral_expGrowth_memLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.pathIntegral_expGrowth_memLp

/-- info: 'MathFin.ito_formula_td_localized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_td_localized

/-! ## Itô → pricing bridge: geometric Brownian motion decomposed by the Itô integral

`ItoFormulaGBM.lean`: the **first pricing-ward consumer of the analytic Itô tower** (which
until now had none — GBM/BS pricing ran via separate algebraic towers and the Wald
exponential). The localized formula, applied to the *time-localized* GBM exponent
`(t,x) ↦ S₀ exp((m−σ²/2)·φₙ(t) + σx)` (identity on `[0,T]`, globally bounded so the
exp-growth hypotheses hold uniformly in time), yields `ito_formula_gbm`:
`Ŝ(T) − Ŝ(0) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ m·Ŝ ds`. Setting `m = 0`
(`discountedGBM_eq_itoIntegral`) makes the drift vanish — the Itô-integral content of the
discounted-GBM martingale, grounding it on the continuous Itô integral rather than the Wald
exponential. -/

/-- info: 'MathFin.ito_formula_gbm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_gbm

/-- info: 'MathFin.discountedGBM_eq_itoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discountedGBM_eq_itoIntegral

/-! ## Itô formula against a constant-coefficient Itô process

`ItoFormulaItoProcess.lean`: generalizes the GBM decomposition from the exponential value
function to an arbitrary `C³` exponential-growth `f`. For `X_t = X₀ + b·t + σ B_t`,
`ito_formula_itoProcess` gives `f(X_T) − f(X₀) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ (f'(X)·b + ½f''(X)·σ²) ds`
— i.e. `∫ f'(X) dX + ½∫ f''(X)σ² ds`, the diffusion the genuine Itô integral. Same
time-localization of the `b·t` exponent as the GBM case; constant coefficients keep the
diffusion integrand a function of `B`. -/

/-- info: 'MathFin.ito_formula_itoProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_itoProcess

/-! ## The time-dependent Itô formula as a process (semimartingale decomposition)

`ItoFormulaProcess.lean`: lifts the terminal Itô formula (a single fixed-horizon `Lp` statement)
to a process identity holding for **every** `t ≤ T`: `f(t,B_t) − f(0,B_0) =ᵐ itoProcessL2Inf t F +
∫₀ᵗ (f_t + ½f_xx) ds`, the stochastic term the genuine Itô-integral *process* — a continuous `L²`
martingale with an everywhere-continuous local-martingale modification. The witness is canonical
(`ito_formula_td_L2_bddDeriv_explicit` exposes `gfx =ᵐ [f_x(·,B)]`); the construction is the
zero-extension `exists_fullHorizon_extension` fed to the existing `[0,∞)` horizon-consistency. No
Markov property, no PDE — entirely inside the Itô tower. -/

/-- info: 'MathFin.ito_formula_td_L2_bddDeriv_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_td_L2_bddDeriv_explicit

/-- info: 'MathFin.ito_formula_td_process' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_td_process

/-! ## Carr–Madan static replication / spanning formula -/

/-- info: 'MathFin.carrMadan_spanning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.carrMadan_spanning

/-- info: 'MathFin.carrMadan_log_spanning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.carrMadan_log_spanning

/-! ## Binomial martingale representation (market completeness) -/

/-- info: 'MathFin.binomial_martingale_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomial_martingale_representation

/-! ## Path-1 upgrades (2026-06-04): reduced cores earned to full derivations -/

/-- info: 'MathFin.submartingale_optional_sampling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.submartingale_optional_sampling

/-- info: 'MathFin.portfolioVarN_covariance_eq_variance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarN_covariance_eq_variance

/-- info: 'MathFin.gaussianCVaR_isLeast_ruObjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_isLeast_ruObjective

/-- info: 'MathFin.survival_probability_eq_Phi_distanceToDefault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.survival_probability_eq_Phi_distanceToDefault

/-- info: 'MathFin.newtonStep_quadratic_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.newtonStep_quadratic_error

/-- info: 'MathFin.newtonSeq_tendsto_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.newtonSeq_tendsto_root

/-- info: 'MathFin.snellAux_le_of_supermartingale_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.snellAux_le_of_supermartingale_of_ge

/-- info: 'MathFin.snellAux_eq_discounted_americanPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.snellAux_eq_discounted_americanPrice

/-- info: 'MathFin.discounted_americanPrice_supermartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.discounted_americanPrice_supermartingale

/-- info: 'MathFin.discounted_intrinsic_le_americanPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.discounted_intrinsic_le_americanPrice

-- Poisson-process theory + Itô-process QV (2026-06-05 full-push round)

/-- info: 'MathFin.PoissonSuperposition.poissonMeasure_conv_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.PoissonSuperposition.poissonMeasure_conv_poissonMeasure

/-- info: 'MathFin.PoissonSuperposition.indepFun_map_add_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.PoissonSuperposition.indepFun_map_add_poissonMeasure

/-- info: 'MathFin.PoissonThinning.markedPoissonMeasure_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.PoissonThinning.markedPoissonMeasure_eq_prod

/-- info: 'MathFin.PoissonThinning.thinned_streams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PoissonThinning.thinned_streams

/-- info: 'MathFin.PoissonCounting.map_count_eq_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.PoissonCounting.map_count_eq_poissonMeasure

/-- info: 'MathFin.PoissonInterarrival.map_firstArrival_eq_expMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.PoissonInterarrival.map_firstArrival_eq_expMeasure

/-- info: 'MathFin.PoissonInterarrival.survival_factorizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.PoissonInterarrival.survival_factorizes

/-- info: 'MathFin.ItoProcessQV.tendsto_qv_ito_process' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.ItoProcessQV.tendsto_qv_ito_process

-- Finance layer over the Poisson/QV track (2026-06-06): variance-swap drift
-- immunity, first-to-default additivity, Poisson pgf, Merton jump-diffusion

/-- info: 'MathFin.tendsto_realizedVariance_gbm_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.tendsto_realizedVariance_gbm_L2

/-- info: 'MathFin.firstToDefault_spread_eq_sum_hazards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.firstToDefault_spread_eq_sum_hazards

/-- info: 'MathFin.PoissonPgf.integral_pow_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MathFin.PoissonPgf.integral_pow_poissonMeasure

/-- info: 'MathFin.mertonCallTerm_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonCallTerm_eq_integral

/-- info: 'MathFin.integral_mertonSpot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_mertonSpot

/-- info: 'MathFin.merton_put_call_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.merton_put_call_parity

-- Merton dominance + classic display; Markov path law (2026-06-06): jump
-- risk is never free (spot convexity + compensation identity), the
-- Λ′ = Λ(1+k) textbook display (rate-shift identity), and Saporito 1.1.2
-- derived from the pin's Ionescu–Tulcea trajectory kernels

/-- info: 'MathFin.bsV_spot_convexOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_spot_convexOn

/-- info: 'MathFin.bsV_le_mertonCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_le_mertonCallPrice

/-- info: 'MathFin.mertonCallPrice_eq_classic_tsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonCallPrice_eq_classic_tsum

/-- info: 'MathFin.markovPathMeasure_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.markovPathMeasure_cylinder

-- Blueprint-spine closure (2026-06-06): every spine node is axiom-pinned.
-- Gap found by tests/test_values.py::test_blueprint_spine_is_audited on its
-- first run — seven tagged headliners (including bs_identity, the magic
-- identity itself) had no guard.

/-- info: 'MathFin.WienerIntegralL2.wiener_assembly_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.WienerIntegralL2.wiener_assembly_isometry

/-- info: 'MathFin.ItoIntegralCLM.itoIntegralCLM_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralCLM.itoIntegralCLM_T

/-- info: 'MathFin.discrete_ito_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discrete_ito_formula

/-- info: 'MathFin.hasLaw_esscher_tilt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasLaw_esscher_tilt

/-- info: 'MathFin.BSCallHyp.of_isPreBrownian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.BSCallHyp.of_isPreBrownian

/-- info: 'MathFin.bs_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_identity

/-- info: 'MathFin.bs_pde_from_no_arbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_pde_from_no_arbitrage

-- Values round 6 (2026-06-09): Andre's reflection-principle counting
-- bijection (Binomial/PathReflection.lean), wired to the corpus as
-- `mf-reflection-principle-counting`.

/-- info: 'MathFin.reflectionPrincipleEquiv_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.reflectionPrincipleEquiv_below

-- Summit B / B1a (2026-06-10): the elementary Itô integral, viewed as a process
-- `t ↦ (V●B)_t`, is an adapted L² martingale
-- (Foundations/ItoIntegralProcessMartingale.lean). Infrastructure for the
-- gated Girsanov/Lévy/martingale-representation/SDE cluster; no corpus entry
-- yet (the `full` entry lands with B1b, the general integrand).

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcess_adaptedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcess.itoSimpleProcess_adaptedAt

/-- info: 'MathFin.ItoIntegralProcess.condExp_adapted_mul_increment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcess.condExp_adapted_mul_increment

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcess_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcess.itoSimpleProcess_isMartingale

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcess_isometry_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcess.itoSimpleProcess_isometry_time

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcessLp_l2_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcess.itoSimpleProcessLp_l2_continuous

-- Summit B / B3 (2026-06-13): the elementary Itô integral as a continuous LOCAL
-- MARTINGALE — pathwise continuity (given continuous Brownian paths) + Degenne's
-- `Martingale.IsLocalMartingale` (`Foundations/ItoIntegralProcessLocalMartingale.lean`).
-- The localization entry point; consumes the upstream local-martingale class.

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcess_pathContinuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcess.itoSimpleProcess_pathContinuous

/-- info: 'MathFin.ItoIntegralProcess.itoSimpleProcess_isLocalMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcess.itoSimpleProcess_isLocalMartingale

-- Summit B / B1b (2026-06-12): the GENERAL-integrand Itô integral
-- `(φ●B)_t = ∫₀ᵗ φ dB` for `φ ∈ L2Predictable[0,T]`, built by extending B1a's
-- t-process along the dense `simpleAssembly_T` (`Foundations/ItoIntegralProcessGeneral.lean`).
-- The key identity `(φ●B)_t = E[∫₀ᵀ φ dB | 𝓕_t]` gives the L² martingale property,
-- a.e.-adaptedness, the contraction and terminal Itô isometry, and L²-continuity.
-- The explicit time-indexed isometry E[(φ●B)_t²] = ∫₀ᵗ E[φ²] ds is deferred.

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoProcessCLM_eq_condExpL2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessGeneral.itoProcessCLM_eq_condExpL2

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoIntegralProcessGen_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessGeneral.itoIntegralProcessGen_isMartingale

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoProcessCLM_aeStronglyMeasurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessGeneral.itoProcessCLM_aeStronglyMeasurable

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_le

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_terminal

/-- info: 'MathFin.ItoIntegralProcessGeneral.itoIntegralProcessGen_l2_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessGeneral.itoIntegralProcessGen_l2_continuous

-- The deferred per-`t` Itô isometry `E[(φ●B)_t²] = ∫_{(0,t]×Ω} φ²`
-- (`Foundations/ItoIntegralProcessIsometry.lean`), proved by density-transferring the
-- band-restricted simple-process isometry against the band-truncation CLM.
/-- info: 'MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessGeneral.itoProcessCLM_norm_sq

-- Covariation of Itô integrals (2026-06-23): the BILINEAR Itô isometry. The Itô
-- integral, bundled as a `LinearIsometry` (`itoIsometry_T`), preserves the
-- L²-inner product (`LinearIsometry.inner_map_map`, polarization of the norm
-- isometry), giving `𝔼[(∫φ dB)(∫ψ dB)] = ⟪φ, ψ⟫` and, on the diagonal, the Itô
-- isometry itself (`Foundations/ItoIntegralCovariation.lean`). The bilinear
-- completion of B1 and the covariance backbone for covariance-swap pricing.

/-- info: 'MathFin.ItoIntegralCovariation.itoIsometry_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralCovariation.itoIsometry_T

/-- info: 'MathFin.ItoIntegralCovariation.inner_itoIntegralCLM_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralCovariation.inner_itoIntegralCLM_T

/-- info: 'MathFin.ItoIntegralCovariation.covariation_itoIntegralCLM_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralCovariation.covariation_itoIntegralCLM_T

/-- info: 'MathFin.ItoIntegralCovariation.variance_itoIntegralCLM_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralCovariation.variance_itoIntegralCLM_T

-- Continuous modification of the general-integrand Itô process (2026-06-26): the
-- first PATHWISE-regularity result for the general integrand and the tower→pricing
-- gate. Simple approximants `Vₙ ● B` (B3-continuous) are a.s.-uniformly Cauchy on
-- `[0,T]` (Doob's continuous-time maximal inequality + Borel–Cantelli on a fast
-- subsequence), so their uniform limit `itoContinuousMod` is pathwise continuous,
-- equals the L² process `itoProcessCLM T t φ` a.e. at every `t ≤ T` (a modification,
-- via `tendstoInMeasure_ae_unique`), and is bundled by `exists_continuous_modification_itoProcess`
-- (`Foundations/ItoIntegralProcessContinuousModification.lean`). Non-redundant: Degenne's
-- general càdlàg modification is `sorry`-backed, and this L²+Doob route yields a
-- genuinely continuous (not merely càdlàg) version.

/-- info: 'MathFin.ItoIntegralProcessContinuousModification.itoContinuousMod_modification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessContinuousModification.itoContinuousMod_modification

/-- info: 'MathFin.ItoIntegralProcessContinuousModification.itoContinuousMod_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessContinuousModification.itoContinuousMod_continuousOn

/-- info: 'MathFin.ItoIntegralProcessContinuousModification.exists_continuous_modification_itoProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessContinuousModification.exists_continuous_modification_itoProcess

-- The IsLocalMartingale follow-on (`Foundations/ItoIntegralProcessLocalMartingaleGeneral.lean`):
-- the everywhere-continuous representative of the modification, adapted to the
-- NULL-AUGMENTED Brownian filtration `𝓕ᴮ ⊔ 𝓝`, is a genuine `IsLocalMartingale`.
-- The measure-theoretic heart is `condExp_sup_nulls` — conditioning on the null
-- augmentation agrees a.e. with conditioning on `𝓕ᴮ` (proved via the σ-algebra crux
-- `exists_ae_eq_of_sup_nulls`), which transfers the L² martingale property to the
-- a.e.-defined modification while repairing it into an everywhere-continuous adapted
-- process — the `∀ ω, IsCadlag` hypothesis of Degenne's `Martingale.IsLocalMartingale`.
/-- info: 'MathFin.ItoIntegralProcessLocalMartingaleGeneral.exists_continuous_localMartingale_modification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoIntegralProcessLocalMartingaleGeneral.exists_continuous_localMartingale_modification

-- The [0,∞) crown (`Foundations/ItoIntegralProcessLocalMartingaleInfinite.lean`): the per-horizon
-- continuous local martingales are glued — horizon consistency (`itoProcessL2Inf_eq_itoProcessCLM`,
-- itself resting on the `[0,T]` `SimpleProcess` clamp) makes each a modification of the SAME
-- unbounded-horizon process, and `indistinguishable_of_modification_on` agrees them on overlaps —
-- into a single everywhere-continuous local martingale on the WHOLE half-line, whose martingale
-- property is the GLOBAL `itoProcessL2Inf_isMartingale` through `condExp_sup_nulls` (no horizon clamp).
/-- info: 'MathFin.ItoLocalMartingaleInfinite.exists_continuous_localMartingale_modification_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoLocalMartingaleInfinite.exists_continuous_localMartingale_modification_infinite

/-! ## Finite-Ω Fundamental Theorem of Asset Pricing (Harrison–Pliska, 2026-06-25) -/

-- The separating-dual kernel (`Foundations/ConvexSeparation.lean`): a finite-dim
-- subspace disjoint from the standard simplex admits a strictly-positive
-- annihilating dual (finite-dimensional geometric Hahn–Banach). The geometric
-- core shared by the single- and multi-period FTAP backward directions.
/-- info: 'MathFin.exists_pos_dual_of_disjoint_stdSimplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.exists_pos_dual_of_disjoint_stdSimplex

-- Multi-state single-period FTAP, now a biconditional (`FTAPMultiState.lean`):
-- the backward direction (no arbitrage ⟹ EMM) via the separating-dual kernel.
/-- info: 'MathFin.hasEMM_multi_iff_not_hasArbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasEMM_multi_iff_not_hasArbitrage

-- Finite-Ω multi-period FTAP (`FTAPDiscrete.lean`): NoArbitrage ⟺ ∃ EMM, the
-- finite case of Dalang–Morton–Willinger. Backward via global separation of the
-- attainable-gains subspace from the simplex; forward via transform telescoping.
/-- info: 'MathFin.ftap_discrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ftap_discrete

-- General-Ω one-period FTAP (`FTAPOnePeriod.lean`): NoArbitrage ⟺ ∃ EMM for a
-- scalar L⁰ return on an arbitrary probability space (Föllmer–Schied 1.55 /
-- one-period DMW). Backward via the bounded-density reduction to L¹, the scalar
-- no-arbitrage dichotomy, and the two-region balancing `withDensity` — no
-- Hahn–Banach, no Kreps–Yan.
/-- info: 'MathFin.OnePeriod.ftap_one_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.OnePeriod.ftap_one_period

-- General-Ω one-period FTAP, d assets (`FTAPOnePeriodVector.lean`): NoArbitrage ⟺ ∃ EMM
-- for a non-redundant ℝᵈ-valued L⁰ return on an arbitrary probability space. Backward via
-- the explicit Esscher / minimal-divergence density z = σ⟪θ₀,Y⟫ minimising the softplus
-- potential — no Hahn–Banach, no L⁰-cone closedness, no measurable selection.
/-- info: 'MathFin.OnePeriodVector.ftap_one_period_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.OnePeriodVector.ftap_one_period_vector

/-! ## Itô → pricing bridge: the deterministic-integrand Wiener integral is Gaussian

`WienerIntegralGaussian.lean`: a deterministic-integrand Itô integral
`∫ f dB` is `gaussianReal 0 ‖f‖²` (charFun route: simple-process Gaussianity +
density + Lévy / `Measure.ext_of_charFun`). Its first pricing consumer is the
Vasicek terminal law (`VasicekSDEGaussian.lean`): the SDE solution
`r_T = mean + σ ∫₀ᵀ e^{−κ(T−s)} dB_s` has the posited law `N(mean, σ²(1−e^{−2κT})/(2κ))`,
**derived** rather than assumed — the first Itô-tower consumer in FixedIncome. -/

/-- info: 'MathFin.WienerIntegralL2.wienerIntegralLp_map_eq_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.WienerIntegralL2.wienerIntegralLp_map_eq_gaussianReal

/-- info: 'MathFin.vasicekShortRate_hasLaw_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.vasicekShortRate_hasLaw_gaussian

/-! ## The Brownian exit times as a localizing sequence — the localization engine

`ExitTime.lean`: the exit times `τ_N = inf {t : N ≤ |B_t|}` of the closed exterior form the
repo's first genuine `IsLocalizingSequence` (`isLocalizingSequence_exitTime`). Each `τ_N` is a
stopping time for the **raw** Brownian filtration (`isStoppingTime_exitTime`) — the closed
exterior makes `{τ_N ≤ i}` the attained-`sInf` event, a rational `⋂ₘ⋃_{q≤i}` measurable in
`𝓕_i` with **no right-continuity** (the open-exterior route would need `𝓕_{i⁺}`, i.e. Blumenthal).
Monotone in `N` and escaping to `⊤` a.s. (continuous paths bounded on compacts), it is the
localization machinery that lifts the bounded-derivative Itô formula toward unbounded
coefficients (Summit C). -/

/-- info: 'MathFin.isStoppingTime_exitTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.isStoppingTime_exitTime

/-- info: 'MathFin.isLocalizingSequence_exitTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.isLocalizingSequence_exitTime

end MathFin.AxiomAudit
