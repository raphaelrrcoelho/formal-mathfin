/-
  GENERATED FILE — do not edit by hand.

  Exhaustive axiom audit: every MathFin constant consumed in PROOF POSITION
  by a benchmark snippet is #guard_msgs-pinned to its exact axiom set, so no
  benchmark-cited theorem can pick up `sorryAx` (a `sorry`) or a non-standard
  axiom without breaking `lake build`.

  The curated, storied audit is MathFin/AxiomAudit.lean (headliners + dated
  narrative); THIS file is its machine-written closure over the benchmark
  corpus (245 constants). Scope: proof-position MathFin names only —
  statement-position defs are exercised by elaboration + the verification
  ledger, and library_wrapper entries cite upstream names.

  Regenerate:  python3 -m tools.verify.axiom_audit_gen --write
  Freshness:   tests/test_values.py::test_axiom_audit_gen_is_fresh
  (Excluded from CI kernel replay like AxiomAudit: whole-library closure.)
-/
import MathFin

namespace MathFin.AxiomAuditGen

/-- info: 'MathFin.ErlangSum.sum_iidExp_law_gammaMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ErlangSum.sum_iidExp_law_gammaMeasure

/-- info: 'MathFin.FeynmanKacHeatEquation.feynmanKac_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.FeynmanKacHeatEquation.feynmanKac_boundary

/-- info: 'MathFin.FeynmanKacHeatEquation.feynmanU_eq_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.FeynmanKacHeatEquation.feynmanU_eq_expectation

/-- info: 'MathFin.ItoProcessQV.tendsto_qv_ito_process' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ItoProcessQV.tendsto_qv_ito_process

/-- info: 'MathFin.OnePeriod.ftap_one_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.OnePeriod.ftap_one_period

/-- info: 'MathFin.OnePeriodVector.ftap_one_period_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.OnePeriodVector.ftap_one_period_vector

/-- info: 'MathFin.Phi_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.Phi_le_one

/-- info: 'MathFin.PoissonInterarrival.survival_factorizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PoissonInterarrival.survival_factorizes

/-- info: 'MathFin.PoissonPgf.integral_pow_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PoissonPgf.integral_pow_poissonMeasure

/-- info: 'MathFin.PoissonSuperposition.indepFun_map_add_poissonMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PoissonSuperposition.indepFun_map_add_poissonMeasure

/-- info: 'MathFin.PoissonThinning.thinned_streams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.PoissonThinning.thinned_streams

/-- info: 'MathFin.WienerIntegralL2.wienerIntegralLp_integral_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.WienerIntegralL2.wienerIntegralLp_integral_sq

/-- info: 'MathFin.WienerIntegralL2.wienerIntegralLp_map_eq_gaussianReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.WienerIntegralL2.wienerIntegralLp_map_eq_gaussianReal

/-- info: 'MathFin.almgrenChrissPath_satisfies_EL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.almgrenChrissPath_satisfies_EL

/-- info: 'MathFin.am_gm_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.am_gm_two

/-- info: 'MathFin.annuityDue_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.annuityDue_closed_form

/-- info: 'MathFin.annuityValue_closed_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.annuityValue_closed_form

/-- info: 'MathFin.asian_payoff_geom_le_arith_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.asian_payoff_geom_le_arith_two

/-- info: 'MathFin.bachelier_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bachelier_call_formula

/-- info: 'MathFin.bermudan_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bermudan_sandwich

/-- info: 'MathFin.beta_linearity_finset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.beta_linearity_finset

/-- info: 'MathFin.beta_linearity_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.beta_linearity_two

/-- info: 'MathFin.beta_market' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.beta_market

/-- info: 'MathFin.beta_of_riskFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.beta_of_riskFree

/-- info: 'MathFin.binomialPrice_call_tendsto_bs_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomialPrice_call_tendsto_bs_closed

/-- info: 'MathFin.binomialPrice_le_americanPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomialPrice_le_americanPrice

/-- info: 'MathFin.binomialRN_expectation_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomialRN_expectation_one

/-- info: 'MathFin.binomial_martingale_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.binomial_martingale_representation

/-- info: 'MathFin.blackLitterman_mean_eq_precision_weighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.blackLitterman_mean_eq_precision_weighted

/-- info: 'MathFin.blackLitterman_var_eq_inv_sum_precision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.blackLitterman_var_eq_inv_sum_precision

/-- info: 'MathFin.black_futures_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.black_futures_formula

/-- info: 'MathFin.bondPortfolio_immunization_first_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bondPortfolio_immunization_first_order

/-- info: 'MathFin.bondPortfolio_immunization_second_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bondPortfolio_immunization_second_order

/-- info: 'MathFin.bondPortfolio_single_bond_conv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bondPortfolio_single_bond_conv

/-- info: 'MathFin.bondPortfolio_single_bond_dur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bondPortfolio_single_bond_dur

/-- info: 'MathFin.bondPortfolio_single_bond_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bondPortfolio_single_bond_value

/-- info: 'MathFin.bootstrap_consistency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bootstrap_consistency

/-- info: 'MathFin.bootstrap_solve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bootstrap_solve

/-- info: 'MathFin.bootstrap_solve_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bootstrap_solve_first

/-- info: 'MathFin.bootstrap_solve_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bootstrap_solve_second

/-- info: 'MathFin.box_spread_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.box_spread_identity

/-- info: 'MathFin.breedenLitzenberger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.breedenLitzenberger

/-- info: 'MathFin.brownian_markov_property' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.brownian_markov_property

/-- info: 'MathFin.bsP_le_K_disc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsP_le_K_disc

/-- info: 'MathFin.bsV_ge_forward_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_ge_forward_lower_bound

/-- info: 'MathFin.bsV_le_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_le_S

/-- info: 'MathFin.bsV_le_mertonCallPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_le_mertonCallPrice

/-- info: 'MathFin.bsV_satisfies_bs_pde_via_feynmanKac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_satisfies_bs_pde_via_feynmanKac

/-- info: 'MathFin.bsV_strict_gt_immediate_exercise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bsV_strict_gt_immediate_exercise

/-- info: 'MathFin.bs_asset_or_nothing_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_asset_or_nothing_formula

/-- info: 'MathFin.bs_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_call_formula

/-- info: 'MathFin.bs_cash_or_nothing_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_cash_or_nothing_formula

/-- info: 'MathFin.bs_dividends_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_dividends_call_formula

/-- info: 'MathFin.bs_put_call_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_put_call_parity

/-- info: 'MathFin.bs_put_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bs_put_formula

/-- info: 'MathFin.bull_call_spread_payoff_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.bull_call_spread_payoff_le

/-- info: 'MathFin.butterfly_payoff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.butterfly_payoff_nonneg

/-- info: 'MathFin.cappedCall_eq_bull_spread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cappedCall_eq_bull_spread

/-- info: 'MathFin.carrMadan_log_spanning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.carrMadan_log_spanning

/-- info: 'MathFin.carrMadan_spanning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.carrMadan_spanning

/-- info: 'MathFin.cds_leg_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cds_leg_equality

/-- info: 'MathFin.chooser_via_pcp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.chooser_via_pcp

/-- info: 'MathFin.cml_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cml_equation

/-- info: 'MathFin.cml_mean_at_stdev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cml_mean_at_stdev

/-- info: 'MathFin.cml_sharpeRatio_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.cml_sharpeRatio_invariant

/-- info: 'MathFin.coherentRisk_isLUB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.coherentRisk_isLUB

/-- info: 'MathFin.compoundPoisson_mgf_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.compoundPoisson_mgf_identity

/-- info: 'MathFin.couponBondPrice_strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.couponBondPrice_strictAnti

/-- info: 'MathFin.creditSpread_eq_hazard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.creditSpread_eq_hazard

/-- info: 'MathFin.creditSpread_eq_time_avg_hazard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.creditSpread_eq_time_avg_hazard

/-- info: 'MathFin.crrProb_tendsto_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crrProb_tendsto_half

/-- info: 'MathFin.crr_drift_limit_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_drift_limit_h

/-- info: 'MathFin.crr_drift_limit_n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_drift_limit_n

/-- info: 'MathFin.crr_one_step_martingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_one_step_martingale

/-- info: 'MathFin.crr_tendsto_gaussian_inDistribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_tendsto_gaussian_inDistribution

/-- info: 'MathFin.crr_variance_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.crr_variance_limit

/-- info: 'MathFin.discountedGBM_eq_itoIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discountedGBM_eq_itoIntegral

/-- info: 'MathFin.discountedGBM_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discountedGBM_isMartingale

/-- info: 'MathFin.discounted_americanPrice_supermartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discounted_americanPrice_supermartingale

/-- info: 'MathFin.discounted_intrinsic_le_americanPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discounted_intrinsic_le_americanPrice

/-- info: 'MathFin.discrete_cubing_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.discrete_cubing_identity

/-- info: 'MathFin.doob_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.doob_decomposition

/-- info: 'MathFin.emm_implies_no_arbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.emm_implies_no_arbitrage

/-- info: 'MathFin.emm_le_superReplication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.emm_le_superReplication

/-- info: 'MathFin.exists_pos_separating_of_cone_disjoint_simplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.exists_pos_separating_of_cone_disjoint_simplex

/-- info: 'MathFin.expected_terminal_eq_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.expected_terminal_eq_forward

/-- info: 'MathFin.firstToDefault_spread_eq_sum_hazards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.firstToDefault_spread_eq_sum_hazards

/-- info: 'MathFin.forward_price_eq_spot_div_discount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.forward_price_eq_spot_div_discount

/-- info: 'MathFin.ftap_discrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ftap_discrete

/-- info: 'MathFin.garman_kohlhagen_call_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.garman_kohlhagen_call_formula

/-- info: 'MathFin.gaussianCVaR_additive_at_rho_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_additive_at_rho_one

/-- info: 'MathFin.gaussianCVaR_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_affine

/-- info: 'MathFin.gaussianCVaR_isLeast_ruObjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_isLeast_ruObjective

/-- info: 'MathFin.gaussianCVaR_monotone_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_monotone_mean

/-- info: 'MathFin.gaussianCVaR_positiveHomogeneity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_positiveHomogeneity

/-- info: 'MathFin.gaussianCVaR_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_standard

/-- info: 'MathFin.gaussianCVaR_sub_VaR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_sub_VaR

/-- info: 'MathFin.gaussianCVaR_subadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_subadditive

/-- info: 'MathFin.gaussianCVaR_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianCVaR_translation

/-- info: 'MathFin.gaussianPDFReal_zero_one_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianPDFReal_zero_one_neg

/-- info: 'MathFin.gaussianVaR_additive_at_rho_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_additive_at_rho_one

/-- info: 'MathFin.gaussianVaR_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_affine

/-- info: 'MathFin.gaussianVaR_monotone_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_monotone_mean

/-- info: 'MathFin.gaussianVaR_positiveHomogeneity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_positiveHomogeneity

/-- info: 'MathFin.gaussianVaR_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_standard

/-- info: 'MathFin.gaussianVaR_subadditive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_subadditive

/-- info: 'MathFin.gaussianVaR_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_translation

/-- info: 'MathFin.gaussianVaR_volatility_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gaussianVaR_volatility_scaling

/-- info: 'MathFin.geom_mean_le_arith_mean_n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.geom_mean_le_arith_mean_n

/-- info: 'MathFin.gompertz_cumulative_force' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.gompertz_cumulative_force

/-- info: 'MathFin.hasDerivAt_T_mul_spotRate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_T_mul_spotRate

/-- info: 'MathFin.hasDerivAt_bachelierV_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bachelierV_S

/-- info: 'MathFin.hasDerivAt_bachelierV_SS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bachelierV_SS

/-- info: 'MathFin.hasDerivAt_bachelierV_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bachelierV_T

/-- info: 'MathFin.hasDerivAt_bachelierV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bachelierV_sigma

/-- info: 'MathFin.hasDerivAt_blackV_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_blackV_F

/-- info: 'MathFin.hasDerivAt_blackV_FF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_blackV_FF

/-- info: 'MathFin.hasDerivAt_blackV_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_blackV_T

/-- info: 'MathFin.hasDerivAt_blackV_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_blackV_r

/-- info: 'MathFin.hasDerivAt_blackV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_blackV_sigma

/-- info: 'MathFin.hasDerivAt_bondPortfolioDur_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bondPortfolioDur_r

/-- info: 'MathFin.hasDerivAt_bondPortfolioValue_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bondPortfolioValue_r

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsAssetDigital_S

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_SS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsAssetDigital_SS

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsAssetDigital_r

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsAssetDigital_sigma

/-- info: 'MathFin.hasDerivAt_bsAssetDigital_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsAssetDigital_tau

/-- info: 'MathFin.hasDerivAt_bsCashDigital_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsCashDigital_S

/-- info: 'MathFin.hasDerivAt_bsCashDigital_SS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsCashDigital_SS

/-- info: 'MathFin.hasDerivAt_bsCashDigital_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsCashDigital_r

/-- info: 'MathFin.hasDerivAt_bsCashDigital_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsCashDigital_sigma

/-- info: 'MathFin.hasDerivAt_bsCashDigital_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsCashDigital_tau

/-- info: 'MathFin.hasDerivAt_bsP_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsP_K

/-- info: 'MathFin.hasDerivAt_bsP_KK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsP_KK

/-- info: 'MathFin.hasDerivAt_bsP_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsP_S

/-- info: 'MathFin.hasDerivAt_bsP_SS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsP_SS

/-- info: 'MathFin.hasDerivAt_bsP_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsP_r

/-- info: 'MathFin.hasDerivAt_bsP_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsP_sigma

/-- info: 'MathFin.hasDerivAt_bsP_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsP_tau

/-- info: 'MathFin.hasDerivAt_bsVDiv_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsVDiv_S

/-- info: 'MathFin.hasDerivAt_bsVDiv_SS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsVDiv_SS

/-- info: 'MathFin.hasDerivAt_bsVDiv_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsVDiv_q

/-- info: 'MathFin.hasDerivAt_bsVDiv_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsVDiv_r

/-- info: 'MathFin.hasDerivAt_bsVDiv_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsVDiv_sigma

/-- info: 'MathFin.hasDerivAt_bsVDiv_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsVDiv_tau

/-- info: 'MathFin.hasDerivAt_bsV_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsV_K

/-- info: 'MathFin.hasDerivAt_bsV_KK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsV_KK

/-- info: 'MathFin.hasDerivAt_bsV_charm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsV_charm

/-- info: 'MathFin.hasDerivAt_bsV_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsV_r

/-- info: 'MathFin.hasDerivAt_bsV_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsV_sigma

/-- info: 'MathFin.hasDerivAt_bsV_vanna' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsV_vanna

/-- info: 'MathFin.hasDerivAt_bsV_volga' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsV_volga

/-- info: 'MathFin.hasDerivAt_bsd1_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsd1_K

/-- info: 'MathFin.hasDerivAt_bsd2_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_bsd2_K

/-- info: 'MathFin.hasDerivAt_neg_bondPortfolioDur_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_neg_bondPortfolioDur_r

/-- info: 'MathFin.hasDerivAt_neg_log_zcb_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasDerivAt_neg_log_zcb_T

/-- info: 'MathFin.hasEMM_multi_iff_not_hasArbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hasEMM_multi_iff_not_hasArbitrage

/-- info: 'MathFin.hazardSurvival_eq_const_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hazardSurvival_eq_const_survival

/-- info: 'MathFin.hazard_eq_neg_log_deriv_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.hazard_eq_neg_log_deriv_survival

/-- info: 'MathFin.herfindahl_card_inv_le_of_sum_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.herfindahl_card_inv_le_of_sum_one

/-- info: 'MathFin.impliedVol_bracket_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.impliedVol_bracket_exists

/-- info: 'MathFin.implied_volatility_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.implied_volatility_unique

/-- info: 'MathFin.informationRatio_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.informationRatio_scale_invariant

/-- info: 'MathFin.integral_log_forward_div_bsTerminal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_log_forward_div_bsTerminal_eq

/-- info: 'MathFin.integral_mertonSpot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.integral_mertonSpot

/-- info: 'MathFin.isLocalizingSequence_exitTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.isLocalizingSequence_exitTime

/-- info: 'MathFin.isTangent_of_proportional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.isTangent_of_proportional

/-- info: 'MathFin.ito_formula_gbm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_gbm

/-- info: 'MathFin.ito_formula_itoProcess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_itoProcess

/-- info: 'MathFin.ito_formula_td_localized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_td_localized

/-- info: 'MathFin.ito_formula_td_process' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_td_process

/-- info: 'MathFin.ito_formula_unrestricted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_unrestricted

/-- info: 'MathFin.ito_formula_unrestricted_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.ito_formula_unrestricted_local

/-- info: 'MathFin.joint_stdev_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.joint_stdev_le

/-- info: 'MathFin.kellyFraction_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kellyFraction_eq_zero_iff

/-- info: 'MathFin.kellyFraction_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kellyFraction_lt_one

/-- info: 'MathFin.kellyFraction_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kellyFraction_pos_iff

/-- info: 'MathFin.kellyGrowth_deriv_at_kelly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kellyGrowth_deriv_at_kelly

/-- info: 'MathFin.kellyGrowth_n_periods' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kellyGrowth_n_periods

/-- info: 'MathFin.kelly_n_periods_deriv_at_kelly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kelly_n_periods_deriv_at_kelly

/-- info: 'MathFin.kmvPD_eq_one_sub_survival_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.kmvPD_eq_one_sub_survival_probability

/-- info: 'MathFin.log_forward_div_bsTerminal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.log_forward_div_bsTerminal_eq

/-- info: 'MathFin.lognormalTerminalPDF_change_of_variables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.lognormalTerminalPDF_change_of_variables

/-- info: 'MathFin.lookback_payoff_ge_vanilla' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.lookback_payoff_ge_vanilla

/-- info: 'MathFin.lp_continuous_martingale_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.lp_continuous_martingale_full

/-- info: 'MathFin.markovPathMeasure_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.markovPathMeasure_cylinder

/-- info: 'MathFin.martingaleTransform_isMartingale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.martingaleTransform_isMartingale

/-- info: 'MathFin.martingale_ae_tendsto_and_eLpNorm_two_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.martingale_ae_tendsto_and_eLpNorm_two_tendsto

/-- info: 'MathFin.mertonCallPrice_eq_classic_tsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonCallPrice_eq_classic_tsum

/-- info: 'MathFin.mertonCallPrice_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.mertonCallPrice_eq_tsum

/-- info: 'MathFin.merton_put_call_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.merton_put_call_parity

/-- info: 'MathFin.minPortfolioVarTwo_perfect_anticorr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.minPortfolioVarTwo_perfect_anticorr

/-- info: 'MathFin.minimum_survival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.minimum_survival

/-- info: 'MathFin.modifiedNumerator_eq_macaulayNumerator_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.modifiedNumerator_eq_macaulayNumerator_div

/-- info: 'MathFin.noArbitrage_of_emm_multi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.noArbitrage_of_emm_multi

/-- info: 'MathFin.nthMoment_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.nthMoment_terminal

/-- info: 'MathFin.portfolioVarN_covariance_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarN_covariance_nonneg

/-- info: 'MathFin.portfolioVarN_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarN_diag

/-- info: 'MathFin.portfolioVarN_equal_weights_iid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarN_equal_weights_iid

/-- info: 'MathFin.portfolioVarN_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarN_smul

/-- info: 'MathFin.portfolioVarN_two_asset_compat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarN_two_asset_compat

/-- info: 'MathFin.portfolioVarTwo_at_minVarWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarTwo_at_minVarWeight

/-- info: 'MathFin.portfolioVarTwo_eq_quad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarTwo_eq_quad

/-- info: 'MathFin.portfolioVarTwo_ge_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.portfolioVarTwo_ge_min

/-- info: 'MathFin.powerForward_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.powerForward_price

/-- info: 'MathFin.putCall_parity_from_no_arbitrage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.putCall_parity_from_no_arbitrage

/-- info: 'MathFin.quanto_correction_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.quanto_correction_factor

/-- info: 'MathFin.replicating_payoff_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.replicating_payoff_down

/-- info: 'MathFin.replicating_payoff_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.replicating_payoff_up

/-- info: 'MathFin.replicating_portfolio_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.replicating_portfolio_cost

/-- info: 'MathFin.riskParityWeightTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.riskParityWeightTwo

/-- info: 'MathFin.risk_parity_equal_contribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.risk_parity_equal_contribution

/-- info: 'MathFin.secondMoment_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.secondMoment_terminal

/-- info: 'MathFin.second_FTAP_single_period' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.second_FTAP_single_period

/-- info: 'MathFin.sharpeRatio_scaleT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.sharpeRatio_scaleT

/-- info: 'MathFin.sharpeRatio_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.sharpeRatio_scale_invariant

/-- info: 'MathFin.sharpeSqTwo_critical_iff_crossProduct_FOC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.sharpeSqTwo_critical_iff_crossProduct_FOC

/-- info: 'MathFin.sortinoRatio_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.sortinoRatio_scale_invariant

/-- info: 'MathFin.sortinoRatio_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.sortinoRatio_translation

/-- info: 'MathFin.spectralRisk_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.spectralRisk_translation

/-- info: 'MathFin.statePricePricing_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.statePricePricing_add

/-- info: 'MathFin.statePricePricing_eq_riskNeutral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.statePricePricing_eq_riskNeutral

/-- info: 'MathFin.stateprice_call_butterfly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.stateprice_call_butterfly_nonneg

/-- info: 'MathFin.submartingale_optional_sampling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.submartingale_optional_sampling

/-- info: 'MathFin.survival_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.survival_at_zero

/-- info: 'MathFin.survival_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.survival_pos

/-- info: 'MathFin.survival_probability_eq_Phi_distanceToDefault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.survival_probability_eq_Phi_distanceToDefault

/-- info: 'MathFin.survival_strictAnti_of_pos_hazard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.survival_strictAnti_of_pos_hazard

/-- info: 'MathFin.swaption_payer_receiver_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.swaption_payer_receiver_parity

/-- info: 'MathFin.tendsto_realizedVariance_gbm_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.tendsto_realizedVariance_gbm_L2

/-- info: 'MathFin.trackingErrorSq_ge_diff_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.trackingErrorSq_ge_diff_sq

/-- info: 'MathFin.trackingErrorSq_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.trackingErrorSq_self

/-- info: 'MathFin.treynorRatio_scale_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.treynorRatio_scale_invariant

/-- info: 'MathFin.triangleNoArb_solve_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.triangleNoArb_solve_third

/-- info: 'MathFin.varianceSwap_log_contribution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.varianceSwap_log_contribution

/-- info: 'MathFin.varianceSwap_log_eq_QV_limit_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.varianceSwap_log_eq_QV_limit_value

/-- info: 'MathFin.variance_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.variance_terminal

/-- info: 'MathFin.vasicekDeterministic_at_halfLife' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.vasicekDeterministic_at_halfLife

/-- info: 'MathFin.vasicekDeterministic_solves_ODE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.vasicekDeterministic_solves_ODE

/-- info: 'MathFin.vasicekShortRate_hasLaw_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.vasicekShortRate_hasLaw_gaussian

/-- info: 'MathFin.worstCase_isLUB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.worstCase_isLUB

/-- info: 'MathFin.zcb_at_maturity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.zcb_at_maturity

/-- info: 'MathFin.zcb_convexity_eq_time_to_maturity_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.zcb_convexity_eq_time_to_maturity_sq

/-- info: 'MathFin.zcb_duration_eq_time_to_maturity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.zcb_duration_eq_time_to_maturity

/-- info: 'MathFin.zcb_yield_eq_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MathFin.zcb_yield_eq_rate

end MathFin.AxiomAuditGen
