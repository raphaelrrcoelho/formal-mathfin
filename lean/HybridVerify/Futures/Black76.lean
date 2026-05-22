/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholes.Call

/-!
# Black-76 formula for options on futures

The **Black formula** (Black 1976) prices European options on futures
contracts. Under the risk-neutral measure, the futures price is a
martingale (zero drift), so

    F_T = F · exp(-σ²T/2 + σ √T · Z),   Z ~ N(0, 1).

The European call payoff `max(F_T − K, 0)` discounted gives

    V_Black = e^{−rT} · [F · Φ(d_1) − K · Φ(d_2)],

where `d_1 = (log(F/K) + σ²T/2) / (σ √T)` and `d_2 = d_1 − σ √T`.

This is identical to `bs_call_formula` specialized to `r = 0` in the
BS-drift, then post-discounted by `e^{-rT}` (the discount-rate is now
**independent** of the underlying's drift). The proof is therefore a
direct algebraic specialization.
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Black-76 formula** for European call options on futures.

Given the risk-neutral hypothesis `BSCallHyp Q F K 0 σ T Z` (i.e., the futures
price has zero drift under `Q`), the discounted expected payoff under an
**independent** discount rate `r` is

    e^{-rT} · [F · Φ(d_1) − K · Φ(d_2)],

where `d_i = bsdi F K 0 σ T`.

Real derivation: applies `bs_call_formula` with `r = 0` (no
intra-formula discounting) and multiplies through by the external
discount factor `e^{-rT}`. -/
theorem black_futures_formula {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {F K σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q F K 0 σ T Z) (r : ℝ) :
    ∫ ω, Real.exp (-r * T) * max (bsTerminal F 0 σ T (Z ω) - K) 0 ∂Q
      = Real.exp (-r * T) *
          (F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T)) := by
  rw [integral_const_mul]
  have h_bs := bs_call_formula h
  -- Specialize r=0 in bs_call_formula
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, mul_one] at h_bs
  -- h_bs : ∫ ω, max (bsTerminal F 0 σ T (Z ω) - K) 0 ∂Q
  --        = F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T)
  rw [h_bs]

/-! ## Black model for swaptions (folded from `Swaption.lean`)

A swaption with strike `K`, forward swap rate `F`, annuity `A`, vol `σ`,
expiry `T` prices via the Black-76 formula scaled by the annuity numéraire.

Payer-receiver parity `V^payer − V^receiver = A · (F − K)` is the swap-rate
analog of put-call parity, with the same one-line proof via `Φ` symmetry. -/

/-- **Payer swaption price under the Black model**: `A · [F · Φ(d_1) − K · Φ(d_2)]`. -/
noncomputable def blackPayerSwaption (A F K σ T : ℝ) : ℝ :=
  A * (F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T))

/-- **Receiver swaption price under the Black model**:
`A · [K · Φ(−d_2) − F · Φ(−d_1)]`. -/
noncomputable def blackReceiverSwaption (A F K σ T : ℝ) : ℝ :=
  A * (K * Phi (-(bsd2 F K 0 σ T)) - F * Phi (-(bsd1 F K 0 σ T)))

/-- **Payer-receiver swaption parity**: `V^payer − V^receiver = A · (F − K)`.
The same `Phi`-symmetry proof as put-call parity, scaled by the annuity. -/
theorem swaption_payer_receiver_parity (A F K σ T : ℝ) :
    blackPayerSwaption A F K σ T - blackReceiverSwaption A F K σ T =
      A * (F - K) := by
  unfold blackPayerSwaption blackReceiverSwaption
  have h_d1 := Phi_add_Phi_neg (bsd1 F K 0 σ T)
  have h_d2 := Phi_add_Phi_neg (bsd2 F K 0 σ T)
  linear_combination A * F * h_d1 - A * K * h_d2

end HybridVerify
