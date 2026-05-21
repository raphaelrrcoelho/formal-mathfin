#!/usr/bin/env python3
"""Append Phase-13 theorems to mathematical_finance.json."""
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
            "formalization_scope": scope or
                "Full formal proof. Re-export from HybridVerify. Axioms-clean.",
        },
    }


def lean_reexport(import_path, theorem_signature, theorem_call):
    return (
        "import Mathlib\n"
        f"import {import_path}\n\n"
        "open MeasureTheory ProbabilityTheory Real\n"
        "open scoped NNReal\n"
        "open HybridVerify\n\n"
        f"{theorem_signature} :=\n"
        f"  HybridVerify.{theorem_call}\n"
    )


NEW_THEOREMS = [
    make_entry(
        "mf-kmv-merton-pd",
        "KMV-Merton Risk-Neutral Probability of Default",
        "Under the Merton (1974) structural credit model, the risk-neutral PD at maturity equals Φ(−d_2^KMV), where d_2^KMV is the BS d_2 with firm value V_0 as spot and face debt F as strike.",
        lean_reexport(
            "HybridVerify.FixedIncome.KMVMerton",
            "theorem kmvPD_le_one_thm (V_0 F r σ_V T : ℝ) :\n    HybridVerify.kmvPD V_0 F r σ_V T ≤ 1",
            "kmvPD_le_one V_0 F r σ_V T",
        ),
        12,
        "Merton 1974 structural credit; KMV (Moody's) commercial implementation",
        difficulty="advanced",
    ),
    make_entry(
        "mf-kmv-survival-Phi-d2",
        "KMV-Merton Survival Probability = Φ(d_2^KMV)",
        "1 − PD = Φ(d_2^KMV): the risk-neutral probability that the firm does not default at maturity.",
        lean_reexport(
            "HybridVerify.FixedIncome.KMVMerton",
            "theorem kmv_survival_eq_Phi_d2_thm (V_0 F r σ_V T : ℝ) :\n    1 - HybridVerify.kmvPD V_0 F r σ_V T = Phi (HybridVerify.kmvDistanceToDefault V_0 F r σ_V T)",
            "kmv_survival_eq_Phi_d2 V_0 F r σ_V T",
        ),
        12,
        "Merton 1974 / KMV survival probability",
    ),
    make_entry(
        "mf-state-price-pricing-linear",
        "Arrow-Debreu State-Price Pricing: Linearity",
        "Linear pricing functional `V_0(X + Y) = V_0(X) + V_0(Y)` from Arrow-Debreu state prices.",
        lean_reexport(
            "HybridVerify.Foundations.StatePrices",
            "theorem statePricePricing_add_thm {ι : Type*}\n    (s : Finset ι) (q X Y : ι → ℝ) :\n    HybridVerify.statePricePricing s q (fun i => X i + Y i) =\n      HybridVerify.statePricePricing s q X + HybridVerify.statePricePricing s q Y",
            "statePricePricing_add s q X Y",
        ),
        9,
        "Arrow-Debreu state prices (Arrow 1953, Debreu 1959)",
    ),
    make_entry(
        "mf-state-price-risk-neutral",
        "State Prices as Risk-Neutral Expectation",
        "If q_i = e^{-rT} · ν_i where ν is the risk-neutral measure, then V_0(X) = e^{-rT} · E^ν[X].",
        lean_reexport(
            "HybridVerify.Foundations.StatePrices",
            "theorem statePricePricing_eq_riskNeutral_thm {ι : Type*}\n    (s : Finset ι) (ν X : ι → ℝ) (rT : ℝ) :\n    HybridVerify.statePricePricing s (fun i => Real.exp (-rT) * ν i) X =\n      Real.exp (-rT) * ∑ i ∈ s, ν i * X i",
            "statePricePricing_eq_riskNeutral s ν X rT",
        ),
        9,
        "State prices and risk-neutral pricing equivalence (Arrow-Debreu)",
    ),
    make_entry(
        "mf-triangle-arbitrage-unique",
        "Triangle Arbitrage: Third Rate Uniquely Determined",
        "Given two non-zero exchange rates S_AB, S_BC, the no-arb constraint S_AB·S_BC·S_CA = 1 uniquely determines S_CA = 1/(S_AB·S_BC).",
        lean_reexport(
            "HybridVerify.Foundations.TriangleArbitrage",
            "theorem triangleNoArb_solve_third_thm {S_AB S_BC : ℝ}\n    (h_ab : S_AB ≠ 0) (h_bc : S_BC ≠ 0) :\n    ∃! S_CA : ℝ, HybridVerify.TriangleNoArb S_AB S_BC S_CA",
            "triangleNoArb_solve_third h_ab h_bc",
        ),
        9,
        "Triangle arbitrage (classical FX no-arb)",
    ),
    make_entry(
        "mf-vasicek-half-life",
        "Vasicek/OU Half-Life at log 2 / κ",
        "At t = log(2)/κ the gap between r(t) and θ has closed to half its initial value.",
        lean_reexport(
            "HybridVerify.FixedIncome.MeanReversionHalfLife",
            "theorem vasicekDeterministic_at_halfLife_thm (r₀ θ κ : ℝ) (hκ : 0 < κ) :\n    HybridVerify.vasicekDeterministic r₀ θ κ (HybridVerify.meanReversionHalfLife κ) - θ =\n      (r₀ - θ) / 2",
            "vasicekDeterministic_at_halfLife r₀ θ κ hκ",
        ),
        12,
        "Mean-reversion half-life (Vasicek 1977, Ornstein-Uhlenbeck)",
    ),
    make_entry(
        "mf-quanto-correction-factor",
        "Quanto Correction Factor exp(-ρ σ_S σ_FX T)",
        "Ratio of the quanto-adjusted forward to the un-adjusted domestic forward equals exp(-ρ σ_S σ_FX T).",
        lean_reexport(
            "HybridVerify.BlackScholes.Quanto",
            "theorem quanto_correction_factor_thm (S_0 r_dom ρ σ_S σ_FX T : ℝ) (hS : 0 < S_0) :\n    HybridVerify.quantoForward S_0 r_dom ρ σ_S σ_FX T / (S_0 * Real.exp (r_dom * T))\n      = Real.exp (-(ρ * σ_S * σ_FX * T))",
            "quanto_correction_factor S_0 r_dom ρ σ_S σ_FX T hS",
        ),
        14,
        "Quanto correction (Reiner 1992, Hull 31.4)",
    ),
    make_entry(
        "mf-cds-fair-spread",
        "CDS Fair Spread: c = h · (1 − R)",
        "Under constant hazard h with recovery R, the fair CDS spread c = h · (1 − R), via leg equality.",
        lean_reexport(
            "HybridVerify.FixedIncome.CDS",
            "theorem cds_leg_equality_thm (h R factor c : ℝ) (h_factor_ne : factor ≠ 0) :\n    c * factor = (1 - R) * h * factor ↔ c = HybridVerify.cdsFairSpread h R",
            "cds_leg_equality h R factor c h_factor_ne",
        ),
        12,
        "CDS pricing under constant hazard with recovery (Jarrow-Turnbull)",
    ),
    make_entry(
        "mf-binomial-girsanov-RN-norm",
        "Discrete Girsanov: E^P[dQ/dP] = 1",
        "In a single-period binomial, the Radon-Nikodym derivative Z = dQ/dP satisfies E^P[Z] = 1.",
        lean_reexport(
            "HybridVerify.Binomial.Girsanov",
            "theorem binomialRN_expectation_one_thm (p q : ℝ)\n    (hp : p ≠ 0) (hp1 : p ≠ 1) :\n    p * HybridVerify.binomialRN p q true + (1 - p) * HybridVerify.binomialRN p q false = 1",
            "binomialRN_expectation_one p q hp hp1",
        ),
        7,
        "Discrete-time Girsanov / measure change (Shreve I, Ch 1)",
    ),
    make_entry(
        "mf-swaption-parity",
        "Black Model Payer-Receiver Swaption Parity",
        "V^payer − V^receiver = A · (F − K) — the swap-rate analog of put-call parity.",
        lean_reexport(
            "HybridVerify.Futures.Swaption",
            "theorem swaption_payer_receiver_parity_thm (A F K σ T : ℝ) :\n    HybridVerify.blackPayerSwaption A F K σ T - HybridVerify.blackReceiverSwaption A F K σ T =\n      A * (F - K)",
            "swaption_payer_receiver_parity A F K σ T",
        ),
        15,
        "Black model for swaptions (Black 1976 specialisation)",
    ),
    make_entry(
        "mf-compound-poisson-mgf",
        "Compound Poisson MGF Algebraic Core",
        "e^{-λ} · e^{λM} = e^{λ(M − 1)}: the algebraic core of the compound-Poisson MGF identity E[e^{tS}] = exp(λ(M_X(t) − 1)).",
        lean_reexport(
            "HybridVerify.Actuarial.CompoundPoisson",
            "theorem compoundPoisson_mgf_identity_thm (lam M : ℝ) :\n    Real.exp (-lam) * Real.exp (lam * M) = Real.exp (lam * (M - 1))",
            "compoundPoisson_mgf_identity lam M",
        ),
        11,
        "Compound Poisson MGF (Cramér-Lundberg actuarial theory)",
    ),
    make_entry(
        "mf-carr-madan-log",
        "Carr-Madan Log-Payoff Algebra",
        "log(S) − log(F) = log(S/F): the algebraic identity used in the Carr-Madan static replication of the log payoff.",
        lean_reexport(
            "HybridVerify.Foundations.CarrMadan",
            "theorem carrMadan_log_payoff_algebra_thm (S F : ℝ) (hS : 0 < S) (hF : 0 < F) :\n    Real.log S - Real.log F = Real.log (S / F)",
            "carrMadan_log_payoff_algebra S F hS hF",
        ),
        14,
        "Carr-Madan static replication (Carr-Madan 2001)",
    ),
    make_entry(
        "mf-second-FTAP-single-period",
        "Second FTAP (Single-Period Binomial)",
        "Under no-arbitrage, the risk-neutral measure in the single-period binomial is uniquely determined by the martingale condition.",
        lean_reexport(
            "HybridVerify.Binomial.SecondFTAP",
            "theorem second_FTAP_single_period_thm {u d r : ℝ} (h : HybridVerify.BinomialNoArb u d r) :\n    ∃! q : ℝ, q * u + (1 - q) * d = Real.exp r",
            "second_FTAP_single_period h",
        ),
        7,
        "Second Fundamental Theorem of Asset Pricing (Harrison-Pliska 1981, single-period)",
        difficulty="advanced",
    ),
    make_entry(
        "mf-almgren-chriss-EL",
        "Almgren-Chriss Trajectory Satisfies EL Equation",
        "The closed-form Almgren-Chriss optimal-execution trajectory X(t) = X_0 · sinh(κ(T-t))/sinh(κT) satisfies the Euler-Lagrange equation X''(t) = κ² · X(t).",
        lean_reexport(
            "HybridVerify.Foundations.AlmgrenChriss",
            "theorem almgrenChrissPath_satisfies_EL_thm (X_0 κ T : ℝ)\n    (hT : Real.sinh (κ * T) ≠ 0) (t : ℝ) :\n    HasDerivAt (fun s : ℝ =>\n        -(X_0 * κ * Real.cosh (κ * (T - s)) / Real.sinh (κ * T)))\n      (κ^2 * HybridVerify.almgrenChrissPath X_0 κ T t) t",
            "almgrenChrissPath_satisfies_EL X_0 κ T hT t",
        ),
        16,
        "Almgren-Chriss optimal execution (Almgren-Chriss 2000)",
        difficulty="advanced",
    ),
    make_entry(
        "mf-newton-raphson-fixed-at-root",
        "Newton-Raphson Iteration: Fixed Point at a Root",
        "If f(σ) = 0, then the Newton iteration σ_{n+1} = σ_n - f(σ_n)/f'(σ_n) leaves σ unchanged.",
        lean_reexport(
            "HybridVerify.BlackScholes.NewtonRaphsonIV",
            "theorem newtonStep_fixed_at_root_thm (f f' : ℝ → ℝ) {σ : ℝ} (h_root : f σ = 0) :\n    HybridVerify.newtonStep f f' σ = σ",
            "newtonStep_fixed_at_root f f' h_root",
        ),
        14,
        "Newton-Raphson root-finding (classical numerical analysis)",
    ),
    make_entry(
        "mf-tangent-portfolio-N-sufficient",
        "N-Asset Tangent Portfolio Sufficient Condition",
        "If Σw = λ · μ_excess for some scalar λ, then w satisfies the cross-product Sharpe FOC: r_j · (Σw)_i = r_i · (Σw)_j.",
        lean_reexport(
            "HybridVerify.Portfolio.TangentPortfolioN",
            "theorem isTangent_of_proportional_thm {ι : Type*}\n    (s : Finset ι) (μ_excess : ι → ℝ) (Sg : ι → ι → ℝ) (w : ι → ℝ) (lam : ℝ)\n    (h : ∀ i ∈ s, (∑ k ∈ s, Sg i k * w k) = lam * μ_excess i) :\n    HybridVerify.IsTangentPortfolioN s μ_excess Sg w",
            "isTangent_of_proportional s μ_excess Sg w lam h",
        ),
        10,
        "N-asset tangent portfolio (Markowitz 1952, Sharpe 1964; matrix-inverse characterisation)",
    ),
    make_entry(
        "mf-lognormal-cov-differential",
        "Lognormal-Gaussian Change of Variables (Differential)",
        "The implied PDF f(K) and the standard-normal PDF are related by f(K) · K · σ · √T = ϕ(d_2(K)): the Jacobian of the substitution K ↦ z = -d_2(K).",
        lean_reexport(
            "HybridVerify.BlackScholes.LognormalCOV",
            "theorem lognormalTerminalPDF_change_of_variables_thm\n    {S_0 r σ T K : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :\n    HybridVerify.lognormalTerminalPDF S_0 r σ T K * (K * σ * Real.sqrt T) =\n      gaussianPDFReal 0 1 (bsd2 S_0 K r σ T)",
            "lognormalTerminalPDF_change_of_variables hK hσ hT",
        ),
        14,
        "Lognormal-gaussian change of variables (BS density jacobian)",
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
