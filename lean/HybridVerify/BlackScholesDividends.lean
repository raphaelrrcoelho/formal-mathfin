/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholesCall

/-!
# Black-Scholes-Merton call price with continuous dividend yield

Extension of `bs_call_formula` to an asset paying a continuous dividend yield
`q ≥ 0`. The risk-neutral dynamics become `S_T = S_0 · exp((r − q − σ²/2) T + σ √T Z)`,
i.e., the drift is the **effective rate** `r − q`. The discounted-payoff formula is

  `V_q = S_0 · e^{-qT} · Φ(d₁) − K · e^{-rT} · Φ(d₂)`,

where `d₁ = (log(S_0/K) + (r − q + σ²/2) T) / (σ √T)` and `d₂ = d₁ − σ √T`,
i.e., `bsd1 / bsd2` evaluated at the effective rate `r − q`.

Derivation: apply `bs_call_formula` with rate parameter `r − q`, then
multiply through by the additional discount `e^{-qT}` (since the discount on
the LHS uses the actual rate `r`, not the drift `r − q`).
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Black-Scholes-Merton call** pricing formula with continuous dividend yield `q`.

Given a risk-neutral hypothesis with effective drift `r − q`
(`BSCallHyp Q S_0 K (r − q) σ T Z`), the discounted (by the **actual rate** `r`)
expected payoff of the European call is

  `S_0 · e^{-qT} · Φ(d₁) − K · e^{-rT} · Φ(d₂)`,

with `d_i = bsdi S_0 K (r − q) σ T`.

Proof: factor `e^{-rT} = e^{-qT} · e^{-(r−q)T}` to apply `bs_call_formula`. -/
theorem bs_dividends_call_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r q σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K (r - q) σ T Z) :
    ∫ ω, Real.exp (-r * T) * max (bsTerminal S_0 (r - q) σ T (Z ω) - K) 0 ∂Q
      = S_0 * Real.exp (-(q * T)) * Phi (bsd1 S_0 K (r - q) σ T)
        - K * Real.exp (-(r * T)) * Phi (bsd2 S_0 K (r - q) σ T) := by
  have h_bs := bs_call_formula h
  -- e^{-rT} = e^{-qT} · e^{-(r-q)T}
  have h_factor :
      (fun ω => Real.exp (-r * T) * max (bsTerminal S_0 (r - q) σ T (Z ω) - K) 0)
      = (fun ω => Real.exp (-(q * T)) *
          (Real.exp (-(r - q) * T) * max (bsTerminal S_0 (r - q) σ T (Z ω) - K) 0)) := by
    funext ω
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [h_factor, integral_const_mul, h_bs]
  have h_combine : Real.exp (-(q * T)) * Real.exp (-(r - q) * T) = Real.exp (-(r * T)) := by
    rw [← Real.exp_add]; congr 1; ring
  linear_combination -(K * Phi (bsd2 S_0 K (r - q) σ T)) * h_combine

/-- **Garman-Kohlhagen FX option pricing formula** for a European call on a
foreign currency. Identical to the dividends formula with `q = r_f` (the foreign
risk-free rate); the domestic rate `r_d` plays the role of `r`. The two payment
streams (foreign currency yields `r_f` continuously to the holder, domestic
funding costs `r_d`) net to an effective drift `r_d − r_f`. -/
theorem garman_kohlhagen_call_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r_d r_f σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K (r_d - r_f) σ T Z) :
    ∫ ω, Real.exp (-r_d * T) * max (bsTerminal S_0 (r_d - r_f) σ T (Z ω) - K) 0 ∂Q
      = S_0 * Real.exp (-(r_f * T)) * Phi (bsd1 S_0 K (r_d - r_f) σ T)
        - K * Real.exp (-(r_d * T)) * Phi (bsd2 S_0 K (r_d - r_f) σ T) :=
  bs_dividends_call_formula (q := r_f) h

end HybridVerify
