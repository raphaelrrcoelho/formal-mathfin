/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholes.Call
import HybridVerify.Futures.Black76

/-!
# Black model for swaptions

A **payer swaption** with strike `K`, forward swap rate `F`, annuity factor
`A`, lognormal vol `σ`, and expiry `T` pays at expiry

  `(F_T − K)⁺ · A`

(equivalent to entering a swap that pays the fixed leg `K` against the
floating leg, valued through the annuity numéraire). Under the **annuity
measure**, the forward swap rate `F_T` is a lognormal martingale with
volatility `σ`. The price collapses to the Black-76 formula with annuity
scaling:

  `V^payer = A · [F · Φ(d_1) − K · Φ(d_2)]`,
  `V^receiver = A · [K · Φ(−d_2) − F · Φ(−d_1)]`,

where `d_1, d_2` are the Black-76 quantities (i.e. BS `d_1, d_2` with `r = 0`,
since the annuity numéraire absorbs the discounting).

## Results

* `blackPayerSwaption`: payer-swaption price.
* `blackReceiverSwaption`: receiver-swaption price.
* `swaption_payer_receiver_parity`: `V^payer − V^receiver = A · (F − K)`.
  The fixed-floating leg-value difference, exactly analogous to put-call parity.
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Payer swaption price under the Black model**: `A · [F Φ(d_1) − K Φ(d_2)]`,
where `d_1, d_2` are the Black-76 quantities. -/
noncomputable def blackPayerSwaption (A F K σ T : ℝ) : ℝ :=
  A * (F * Phi (bsd1 F K 0 σ T) - K * Phi (bsd2 F K 0 σ T))

/-- **Receiver swaption price under the Black model**: `A · [K Φ(−d_2) − F Φ(−d_1)]`. -/
noncomputable def blackReceiverSwaption (A F K σ T : ℝ) : ℝ :=
  A * (K * Phi (-(bsd2 F K 0 σ T)) - F * Phi (-(bsd1 F K 0 σ T)))

/-- **Payer-receiver swaption parity**: `V^payer − V^receiver = A · (F − K)`.

The annuity-scaled analogue of put-call parity. Same one-line algebraic
identity that drives put-call parity, dressed for the swap setting. -/
theorem swaption_payer_receiver_parity (A F K σ T : ℝ) :
    blackPayerSwaption A F K σ T - blackReceiverSwaption A F K σ T =
      A * (F - K) := by
  unfold blackPayerSwaption blackReceiverSwaption
  have h_d1 := Phi_add_Phi_neg (bsd1 F K 0 σ T)
  have h_d2 := Phi_add_Phi_neg (bsd2 F K 0 σ T)
  linear_combination A * F * h_d1 - A * K * h_d2

end HybridVerify
