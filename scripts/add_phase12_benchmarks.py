#!/usr/bin/env python3
"""Append Phase-12 theorems to mathematical_finance.json."""
import json
import os

ROOT = "/home/rapha/code/automated_proofs_quantfin"
BENCH = os.path.join(ROOT, "benchmarks", "mathematical_finance.json")


def make_entry(theorem_id, name, description, lean_code, chapter, reference,
               difficulty="intermediate", status="full", scope=""):
    return {
        "id": theorem_id,
        "name": name,
        "description": description,
        "domain": "mathematical_finance",
        "code": {"lean": lean_code},
        "metadata": {
            "chapter": chapter,
            "reference": reference,
            "difficulty": difficulty,
            "formalization_status": status,
            "formalization_scope": scope or f"Full formal proof. Re-export from HybridVerify. Axioms-clean.",
        },
    }


def lean_reexport(import_path, theorem_signature, theorem_name):
    """Build a `Lean re-export` string for the benchmark entry."""
    return (
        "import Mathlib\n"
        f"import {import_path}\n\n"
        "open MeasureTheory ProbabilityTheory Real\n"
        "open scoped NNReal\n"
        "open HybridVerify\n\n"
        f"{theorem_signature} :=\n"
        f"  HybridVerify.{theorem_name}\n"
    )


NEW_THEOREMS = [
    # ---------- Wave 1 ----------
    make_entry(
        "mf-chooser-decompose",
        "Chooser Option Payoff Decomposition (via Put-Call Parity)",
        "At the chooser date t, max(C_t, P_t) = C_t + max(0, K·e^{-r(T-t)} - S_t). Hence a chooser = long call (strike K, mat. T) + long put-payoff at date t with adjusted strike.",
        lean_reexport(
            "HybridVerify.BlackScholes.Chooser",
            "theorem chooser_via_pcp_thm (C P S K_disc : ℝ) (hPCP : C - P = S - K_disc) :\n    max C P = C + max 0 (K_disc - S)",
            "chooser_via_pcp _ _ _ _ hPCP",
        ),
        14,
        "Chooser options (Hull 26.7, Rubinstein 1991)",
    ),
    make_entry(
        "mf-capped-call-bull-spread",
        "Capped Call equals Bull Call Spread",
        "min(max(S - K₁, 0), K₂ - K₁) = max(S - K₁, 0) - max(S - K₂, 0). Pure pointwise algebra via case split on S.",
        lean_reexport(
            "HybridVerify.BlackScholes.CappedCall",
            "theorem capped_call_eq_bull_spread_thm (S K₁ K₂ : ℝ) (h : K₁ ≤ K₂) :\n    min (max (S - K₁) 0) (K₂ - K₁) = max (S - K₁) 0 - max (S - K₂) 0",
            "cappedCall_eq_bull_spread S K₁ K₂ h",
        ),
        14,
        "Capped call decomposition (Hull 11.2)",
    ),
    make_entry(
        "mf-bull-call-spread-payoff-le",
        "Bull-Call Spread Payoff Non-Negativity",
        "For K₁ ≤ K₂, max(S - K₂, 0) ≤ max(S - K₁, 0): the bull-call spread payoff is non-negative everywhere.",
        lean_reexport(
            "HybridVerify.BlackScholes.Spreads",
            "theorem bull_call_spread_payoff_le_thm (S K₁ K₂ : ℝ) (h : K₁ ≤ K₂) :\n    max (S - K₂) 0 ≤ max (S - K₁) 0",
            "bull_call_spread_payoff_le S K₁ K₂ h",
        ),
        14,
        "Bull-call spread no-arb (Hull 11.5)",
    ),
    make_entry(
        "mf-butterfly-payoff-nonneg",
        "Butterfly Spread Payoff Non-Negativity",
        "For K₁ ≤ K₃ with K₂ = (K₁+K₃)/2, max(S-K₁, 0) - 2·max(S-K₂, 0) + max(S-K₃, 0) ≥ 0. The butterfly payoff is non-negative — the foundation for Breeden-Litzenberger's implied PDF.",
        lean_reexport(
            "HybridVerify.BlackScholes.Spreads",
            "theorem butterfly_payoff_nonneg_thm (S K₁ K₃ : ℝ) (h : K₁ ≤ K₃) :\n    0 ≤ max (S - K₁) 0 - 2 * max (S - (K₁ + K₃) / 2) 0 + max (S - K₃) 0",
            "butterfly_payoff_nonneg S K₁ K₃ h",
        ),
        14,
        "Butterfly spread (Hull 11.5)",
    ),
    make_entry(
        "mf-lookback-payoff-ge-vanilla",
        "Lookback Call Payoff ≥ Vanilla Call Payoff",
        "Since the running max M ≥ S_T, max(M - K, 0) ≥ max(S_T - K, 0). Hence lookback call ≥ vanilla call (static lower bound).",
        lean_reexport(
            "HybridVerify.BlackScholes.Lookback",
            "theorem lookback_payoff_ge_vanilla_thm (M S K : ℝ) (h : S ≤ M) :\n    max (S - K) 0 ≤ max (M - K) 0",
            "lookback_payoff_ge_vanilla M S K h",
        ),
        14,
        "Lookback option lower bound (Hull 26.8)",
    ),
    make_entry(
        "mf-bermudan-sandwich",
        "Bermudan Sandwich: European ≤ Bermudan ≤ American",
        "For nested exercise sets Eur ⊆ Berm ⊆ Amer, the optimal-stopping values are sandwiched in the same order (monotonicity of Finset.sup' under subset inclusion).",
        lean_reexport(
            "HybridVerify.Binomial.Bermudan",
            "theorem bermudan_sandwich_thm {ι : Type*} {Eur Berm Amer : Finset ι}\n    (hEB : Eur ⊆ Berm) (hBA : Berm ⊆ Amer) (hEurNE : Eur.Nonempty) (v : ι → ℝ) :\n    Eur.sup' hEurNE v ≤ Berm.sup' (hEurNE.mono hEB) v ∧\n      Berm.sup' (hEurNE.mono hEB) v ≤ Amer.sup' (hEurNE.mono (hEB.trans hBA)) v",
            "bermudan_sandwich hEB hBA hEurNE v",
        ),
        14,
        "Bermudan sandwich (Hull 26.6, Rogers-Williams Vol 2)",
    ),
    make_entry(
        "mf-macaulay-modified-discrete",
        "Modified Duration equals Macaulay Duration divided by (1+y)",
        "Under discrete annual compounding, the modified duration numerator equals the Macaulay duration numerator divided by (1+y). At the level of price-sensitivities, -dP/dy = D_mod · P where D_mod = D_mac / (1+y).",
        lean_reexport(
            "HybridVerify.FixedIncome.MacaulayModified",
            "theorem modifiedNumerator_eq_macaulayNumerator_div_thm {ι : Type*}\n    (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ) (y : ℝ) (hy : 1 + y ≠ 0) :\n    HybridVerify.modifiedNumerator s t c y =\n      HybridVerify.macaulayNumerator s t c y / (1 + y)",
            "modifiedNumerator_eq_macaulayNumerator_div s t c y hy",
        ),
        11,
        "Macaulay vs Modified duration (Fabozzi 4.3)",
    ),
    # ---------- Wave 2 ----------
    make_entry(
        "mf-nth-moment-terminal",
        "n-th Moment of the Terminal Asset Price (Power-Forward Moment)",
        "Under the BS lognormal hypothesis, E_Q[S_T^n] = S_0^n · exp(n·r·T + n(n-1)/2 · σ²·T). Generalizes the forward (n=1) and second moment (n=2). Derivation: gaussian MGF at c = n·σ·√T.",
        lean_reexport(
            "HybridVerify.BlackScholes.PowerOption",
            "theorem nthMoment_terminal_thm {Ω : Type*} {mΩ : MeasurableSpace Ω}\n    {Q : Measure Ω} [IsProbabilityMeasure Q]\n    {S_0 K r σ T : ℝ} {Z : Ω → ℝ} (n : ℕ)\n    (h : BSCallHyp Q S_0 K r σ T Z) :\n    ∫ ω, (bsTerminal S_0 r σ T (Z ω))^n ∂Q =\n      S_0^n *\n        Real.exp ((n : ℝ) * r * T + (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T)",
            "nthMoment_terminal n h",
        ),
        14,
        "Power options under lognormal (Hull 26.10, Heynen-Kat 1996)",
    ),
    make_entry(
        "mf-power-forward-price",
        "Power-Forward Price under BS Lognormal",
        "Discounted n-th moment of S_T equals S_0^n · exp((n-1)·r·T + n(n-1)/2 · σ² T). Generalizes spot-forward parity (n=1: price = S_0).",
        lean_reexport(
            "HybridVerify.BlackScholes.PowerOption",
            "theorem powerForward_price_thm {Ω : Type*} {mΩ : MeasurableSpace Ω}\n    {Q : Measure Ω} [IsProbabilityMeasure Q]\n    {S_0 K r σ T : ℝ} {Z : Ω → ℝ} (n : ℕ)\n    (h : BSCallHyp Q S_0 K r σ T Z) :\n    Real.exp (-(r * T)) *\n      (∫ ω, (bsTerminal S_0 r σ T (Z ω))^n ∂Q) =\n      S_0^n *\n        Real.exp ((((n : ℝ) - 1) * r * T) +\n                  (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T)",
            "powerForward_price n h",
        ),
        14,
        "Power forward price (Heynen-Kat 1996)",
    ),
    make_entry(
        "mf-hazard-survival-const",
        "Time-Varying Hazard Survival Reduces to Constant Form",
        "When the hazard function is constant h(u) ≡ h₀, the cumulative hazard ∫₀^t h₀ du = h₀·t and the survival probability exp(-cumHazard) matches the constant-hazard formula exp(-h₀(T-t)) at t=0.",
        lean_reexport(
            "HybridVerify.FixedIncome.HazardCurve",
            "theorem hazardSurvival_eq_const_survival_thm (h_0 T : ℝ) :\n    HybridVerify.hazardSurvival (fun _ => h_0) T =\n      HybridVerify.survivalProbability h_0 0 T",
            "hazardSurvival_eq_const_survival h_0 T",
        ),
        12,
        "Time-varying hazard credit (Lando, Credit Risk Modeling)",
    ),
    make_entry(
        "mf-credit-spread-time-avg-hazard",
        "Credit Spread as Time-Averaged Hazard",
        "Under time-varying hazard h(u), the credit spread c(T) = -log(S(T))/T = H(T)/T where H is the cumulative hazard. The spread is the time-averaged hazard.",
        lean_reexport(
            "HybridVerify.FixedIncome.HazardCurve",
            "theorem creditSpread_eq_time_avg_hazard_thm {h : ℝ → ℝ} {T : ℝ} (hT : 0 < T) :\n    -Real.log (HybridVerify.hazardSurvival h T) / T = HybridVerify.cumHazard h T / T",
            "creditSpread_eq_time_avg_hazard hT",
        ),
        12,
        "Hazard curve and credit spread (Lando, Credit Risk Modeling)",
    ),
    # ---------- Wave 3 ----------
    make_entry(
        "mf-breeden-litzenberger",
        "Breeden-Litzenberger: Implied Risk-Neutral PDF from Option Prices",
        "The second strike-derivative of the BS call equals the discounted lognormal PDF: ∂²_K bsV(K) = e^{-rT} · ϕ(d_2)/(K σ √T), which is the risk-neutral PDF of S_T at K times the discount factor.",
        lean_reexport(
            "HybridVerify.BlackScholes.BreedenLitzenberger",
            "theorem breedenLitzenberger_thm {S_0 r σ : ℝ} (hS : 0 < S_0) (hσ : 0 < σ)\n    {K T : ℝ} (hK : 0 < K) (hT : 0 < T) :\n    HasDerivAt (fun k => -(Real.exp (-(r * T)) * Phi (bsd2 S_0 k r σ T)))\n      (Real.exp (-(r * T)) * HybridVerify.lognormalTerminalPDF S_0 r σ T K) K",
            "breedenLitzenberger hS hσ hK hT",
        ),
        14,
        "Breeden-Litzenberger 1978 (state-price densities from option prices)",
        difficulty="advanced",
    ),
    make_entry(
        "mf-impliedvol-bracket",
        "Bisection Bracket Existence for Implied Volatility",
        "By IVT and strict monotonicity, any target price strictly between f(σ_lo) and f(σ_hi) admits a unique implied volatility σ ∈ (σ_lo, σ_hi). This is the bisection-method correctness statement.",
        lean_reexport(
            "HybridVerify.BlackScholes.BisectionIV",
            "theorem impliedVol_bracket_exists_thm {f : ℝ → ℝ} {σ_lo σ_hi C_obs : ℝ}\n    (h_lo_lt_hi : σ_lo < σ_hi)\n    (h_cont : ContinuousOn f (Set.Icc σ_lo σ_hi))\n    (h_mono : StrictMonoOn f (Set.Icc σ_lo σ_hi))\n    (h_brkt : f σ_lo < C_obs ∧ C_obs < f σ_hi) :\n    ∃! σ : ℝ, σ ∈ Set.Ioo σ_lo σ_hi ∧ f σ = C_obs",
            "impliedVol_bracket_exists h_lo_lt_hi h_cont h_mono h_brkt",
        ),
        14,
        "Bisection method for implied vol (Press et al., Numerical Recipes)",
    ),
    # ---------- Wave 4 ----------
    make_entry(
        "mf-risk-parity-2-asset",
        "Two-Asset Risk-Parity Equal Contribution",
        "For two assets, the risk-parity weights w₁ = σ₂/(σ₁+σ₂), w₂ = σ₁/(σ₁+σ₂) make each asset contribute equally to portfolio variance — independent of correlation.",
        lean_reexport(
            "HybridVerify.Portfolio.RiskParity",
            "theorem risk_parity_equal_contribution_thm (σ₁ σ₂ ρ : ℝ) (hσ : σ₁ + σ₂ ≠ 0) :\n    let w₁ := HybridVerify.riskParityWeightTwo σ₁ σ₂\n    let w₂ := HybridVerify.riskParityWeightTwo σ₂ σ₁\n    w₁ * (w₁ * σ₁^2 + w₂ * ρ * σ₁ * σ₂) =\n      w₂ * (w₁ * ρ * σ₁ * σ₂ + w₂ * σ₂^2)",
            "risk_parity_equal_contribution σ₁ σ₂ ρ hσ",
        ),
        10,
        "Risk parity (Maillard-Roncalli-Teiletche 2010)",
    ),
    make_entry(
        "mf-black-litterman-1d-mean",
        "Black-Litterman 1D Posterior Mean (Precision-Weighted)",
        "Posterior mean in the 1D Black-Litterman update equals (s₁²π + s₀²Q)/(s₀²+s₁²), the precision-weighted combination of prior π and view Q.",
        lean_reexport(
            "HybridVerify.Portfolio.BlackLitterman",
            "theorem blackLitterman_mean_eq_precision_weighted_thm\n    (π Q s0sq s1sq : ℝ) (h₀ : 0 < s0sq) (h₁ : 0 < s1sq) :\n    HybridVerify.posteriorMean1d π Q s0sq s1sq =\n      (π / s0sq + Q / s1sq) / (1 / s0sq + 1 / s1sq)",
            "blackLitterman_mean_eq_precision_weighted π Q s0sq s1sq h₀ h₁",
        ),
        10,
        "Black-Litterman 1992 (posterior via gaussian conjugacy)",
    ),
    make_entry(
        "mf-black-litterman-1d-variance",
        "Black-Litterman 1D Posterior Variance (Harmonic Mean)",
        "Posterior variance s₀²s₁²/(s₀²+s₁²) = 1/(1/s₀² + 1/s₁²): precision (1/variance) is additive in independent gaussian updates.",
        lean_reexport(
            "HybridVerify.Portfolio.BlackLitterman",
            "theorem blackLitterman_var_eq_inv_sum_precision_thm\n    (s0sq s1sq : ℝ) (h₀ : 0 < s0sq) (h₁ : 0 < s1sq) :\n    HybridVerify.posteriorVariance1d s0sq s1sq = 1 / (1 / s0sq + 1 / s1sq)",
            "blackLitterman_var_eq_inv_sum_precision s0sq s1sq h₀ h₁",
        ),
        10,
        "Black-Litterman 1992 (posterior precision additivity)",
    ),
    make_entry(
        "mf-tangent-portfolio-foc",
        "Tangent Portfolio First-Order Condition (Two-Asset)",
        "At the closed-form tangent weight w₁^T = (σ₂²r₁ - ρσ₁σ₂r₂)/D, the Sharpe-ratio FOC r₂(Σw)₁ = r₁(Σw)₂ holds: marginal-variance contributions are proportional to marginal excess returns.",
        lean_reexport(
            "HybridVerify.Portfolio.TangentPortfolio",
            "theorem tangentTwo_satisfies_FOC_thm (r₁ r₂ σ₁ σ₂ ρ : ℝ) :\n    let D := σ₂^2 * r₁ + σ₁^2 * r₂ - ρ * σ₁ * σ₂ * (r₁ + r₂)\n    let w_num := σ₂^2 * r₁ - ρ * σ₁ * σ₂ * r₂\n    let one_sub_w_num := σ₁^2 * r₂ - ρ * σ₁ * σ₂ * r₁\n    r₂ * (w_num * σ₁^2 + one_sub_w_num * ρ * σ₁ * σ₂) =\n      r₁ * (w_num * ρ * σ₁ * σ₂ + one_sub_w_num * σ₂^2)",
            "tangentTwo_satisfies_FOC r₁ r₂ σ₁ σ₂ ρ",
        ),
        10,
        "Tangent portfolio (Markowitz 1952, Sharpe 1964)",
    ),
    # ---------- Wave 5 ----------
    make_entry(
        "mf-forward-rate-nonflat",
        "Forward Rate from Non-Flat Spot-Rate Curve",
        "When the spot rate R(T) is differentiable, d/dT [T · R(T)] = R(T) + T · R'(T) (product rule). This is the instantaneous forward rate, generalizing the flat-curve case.",
        lean_reexport(
            "HybridVerify.FixedIncome.ForwardRate",
            "theorem hasDerivAt_T_mul_spotRate_thm {R : ℝ → ℝ} {R'_T T : ℝ}\n    (hR : HasDerivAt R R'_T T) :\n    HasDerivAt (fun t => t * R t) (R T + T * R'_T) T",
            "hasDerivAt_T_mul_spotRate hR",
        ),
        11,
        "Forward rate from spot rate (Fabozzi 5.2, Hull 4.7)",
    ),
    make_entry(
        "mf-vasicek-deterministic-ode",
        "Vasicek Deterministic ODE Solution",
        "The closed form r(t) = θ + (r₀ - θ)·e^{-κt} solves the deterministic part of the Vasicek SDE dr/dt = κ(θ - r(t)). Exhibits exponential mean reversion to θ at rate κ.",
        lean_reexport(
            "HybridVerify.FixedIncome.Vasicek",
            "theorem vasicekDeterministic_solves_ODE_thm (r₀ θ κ t : ℝ) :\n    HasDerivAt (HybridVerify.vasicekDeterministic r₀ θ κ)\n      (κ * (θ - HybridVerify.vasicekDeterministic r₀ θ κ t)) t",
            "vasicekDeterministic_solves_ODE r₀ θ κ t",
        ),
        12,
        "Vasicek 1977 short-rate model (deterministic part)",
    ),
    # ---------- Wave 6 ----------
    make_entry(
        "mf-cvar-rockafellar-uryasev",
        "Rockafellar-Uryasev Form for Gaussian CVaR",
        "Gaussian CVaR rewrites as CVaR_α = VaR_α + σ · (ϕ(z)/(1-α) - z), the additive form of CVaR that motivates the variational characterization CVaR = inf_c [c + (1/(1-α))·E[(L-c)⁺]].",
        lean_reexport(
            "HybridVerify.RiskMeasures.RockafellarUryasev",
            "theorem gaussianCVaR_rockafellarUryasev_thm (μ σ z α : ℝ) :\n    HybridVerify.gaussianCVaR μ σ z α =\n      HybridVerify.gaussianVaR μ σ z +\n        σ * (gaussianPDFReal 0 1 z / (1 - α) - z)",
            "gaussianCVaR_rockafellarUryasev μ σ z α",
        ),
        13,
        "Rockafellar-Uryasev 2000 (CVaR optimization)",
    ),
    make_entry(
        "mf-spectral-risk-translation",
        "Spectral Risk Measure Translation Invariance",
        "Discrete spectral risk Σ φ_i Q_i with normalized weights (Σ φ = 1) satisfies translation invariance: ρ(Q + c) = ρ(Q) + c.",
        lean_reexport(
            "HybridVerify.RiskMeasures.Spectral",
            "theorem spectralRisk_translation_thm {ι : Type*} (s : Finset ι) (φ : ι → ℝ)\n    (Q : ι → ℝ) (c : ℝ) (h_norm : ∑ i ∈ s, φ i = 1) :\n    HybridVerify.spectralRiskFinite s φ (fun i => Q i + c) =\n      HybridVerify.spectralRiskFinite s φ Q + c",
            "spectralRisk_translation s φ Q c h_norm",
        ),
        13,
        "Spectral risk measures (Acerbi 2002)",
    ),
    make_entry(
        "mf-herfindahl-cauchy-schwarz",
        "Herfindahl-Hirschman Index Lower Bound by Cauchy-Schwarz",
        "Under unit-budget constraint (Σ w_i = 1), the Cauchy-Schwarz inequality gives HHI = Σ w_i² ≥ 1/n where n = card s. Equality at equal weights.",
        lean_reexport(
            "HybridVerify.RiskMeasures.Concentration",
            "theorem herfindahl_card_inv_le_of_sum_one_thm {ι : Type*}\n    (s : Finset ι) (w : ι → ℝ) (hs : s.Nonempty) (h_sum : ∑ i ∈ s, w i = 1) :\n    (s.card : ℝ)⁻¹ ≤ HybridVerify.herfindahl s w",
            "herfindahl_card_inv_le_of_sum_one s w hs h_sum",
        ),
        13,
        "Concentration risk via Herfindahl (Hirschman 1945; Cauchy-Schwarz)",
    ),
    # ---------- Wave 7 ----------
    make_entry(
        "mf-annuity-due-closed-form",
        "Annuity-Due Geometric Closed Form",
        "Σ_{k=0}^{n-1} v^k = (1 - v^n)/(1 - v) for v ≠ 1. The annuity-due present value formula, mirror of the immediate-annuity case.",
        lean_reexport(
            "HybridVerify.Actuarial.Insurance",
            "theorem annuityDueValue_thm (v : ℝ) (n : ℕ) (hv : v ≠ 1) :\n    ∑ k ∈ Finset.range n, v ^ k = (1 - v ^ n) / (1 - v)",
            "annuityDueValue v n hv",
        ),
        11,
        "Annuity-due formula (Bowers et al., Actuarial Mathematics)",
    ),
    make_entry(
        "mf-gompertz-cumulative-force",
        "Gompertz Cumulative Force of Mortality",
        "∫₀^t B·e^{c·u} du = (B/c)·(e^{c·t} - 1) for c ≠ 0. The closed-form cumulative force of mortality under the Gompertz law μ(t) = B·e^{c·t}.",
        lean_reexport(
            "HybridVerify.Actuarial.Mortality",
            "theorem gompertz_cumulative_force_thm (B c t : ℝ) (hc : c ≠ 0) :\n    ∫ u in (0:ℝ)..t, B * Real.exp (c * u) =\n      (B / c) * (Real.exp (c * t) - 1)",
            "gompertz_cumulative_force B c t hc",
        ),
        11,
        "Gompertz mortality law (Bowers et al., Actuarial Mathematics)",
    ),
    # ---------- Wave 9 ----------
    make_entry(
        "mf-bsV-forward-lower-bound",
        "European Call Forward Lower Bound (No-Arb)",
        "Under risk-neutral lognormal hypothesis, bsV ≥ S_0 - K·e^{-rT}. Proof: bsV = bsP + S_0 - K·e^{-rT} (put-call parity) and bsP ≥ 0 (integral of (K-S_T)⁺ is non-negative).",
        lean_reexport(
            "HybridVerify.Binomial.AmericanCallNoDividend",
            "theorem bsV_ge_forward_lower_bound_thm {Ω : Type*} {mΩ : MeasurableSpace Ω}\n    {Q : Measure Ω} [IsProbabilityMeasure Q]\n    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}\n    (h : BSCallHyp Q S_0 K r σ T Z) :\n    S_0 - K * Real.exp (-(r * T)) ≤ bsV K r σ S_0 T",
            "bsV_ge_forward_lower_bound h",
        ),
        9,
        "European call lower bound (Hull 11.3, Shreve 4.5)",
    ),
    make_entry(
        "mf-merton-1973-no-early-exercise",
        "Merton 1973: American = European for Non-Dividend Call",
        "Under positive interest rate and BS lognormal hypothesis, bsV > S - K. Strict dominance over immediate-exercise payoff implies American call equals European call (early exercise never optimal).",
        lean_reexport(
            "HybridVerify.Binomial.AmericanCallNoDividend",
            "theorem bsV_strict_gt_immediate_exercise_thm {Ω : Type*} {mΩ : MeasurableSpace Ω}\n    {Q : Measure Ω} [IsProbabilityMeasure Q]\n    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}\n    (h : BSCallHyp Q S_0 K r σ T Z) (hr : 0 < r) :\n    S_0 - K < bsV K r σ S_0 T",
            "bsV_strict_gt_immediate_exercise h hr",
        ),
        9,
        "Merton 1973 (American call on non-dividend stock)",
        difficulty="advanced",
    ),
]


def main():
    with open(BENCH, "r") as f:
        data = json.load(f)
    existing_ids = {t["id"] for t in data["theorems"]}
    added = 0
    for entry in NEW_THEOREMS:
        if entry["id"] in existing_ids:
            print(f"skip (exists): {entry['id']}")
            continue
        data["theorems"].append(entry)
        added += 1
    with open(BENCH, "w") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    print(f"Added {added} new benchmark entries. Total: {len(data['theorems'])}.")


if __name__ == "__main__":
    main()
