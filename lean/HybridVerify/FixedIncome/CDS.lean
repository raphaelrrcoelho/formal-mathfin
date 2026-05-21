/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.FixedIncome.Credit

/-!
# Credit Default Swap (CDS) fair spread with recovery

A CDS exchanges a periodic premium `c` (paid while the reference entity has
not defaulted) for a contingent payment of `(1 − R)` upon default (where `R`
is the recovery rate). Under constant hazard intensity `h` and risk-free
rate `r`, both legs evaluate to a common annuity factor

  `annuity(r + h, T) := (1 − e^{−(r+h) T}) / (r + h)`,

(this is the PV of `$1` paid continuously while the reference entity survives,
discounted at `r + h`). The premium leg PV is `c · annuity`, and the
protection leg PV is `(1 − R) · h · annuity`. The fair spread that equates
the two legs is

  `c = h · (1 − R)`.

This generalises the constant-hazard credit spread in `Credit.lean`
(`creditSpread_eq_hazard`): the recovery `R = 0` case is precisely
`c = h`.

## Results

* `cdsFairSpread`: definition `h · (1 − R)`.
* `cdsFairSpread_zero_recovery`: specialises to `c = h`.
* `cds_leg_equality`: under the shared annuity factor, the fair-spread
  characterisation `c · factor = (1 − R) · h · factor ↔ c = cdsFairSpread h R`.
-/

namespace HybridVerify

open Real

/-- **Fair CDS spread under constant hazard with recovery**: `c = h · (1 − R)`. -/
noncomputable def cdsFairSpread (h R : ℝ) : ℝ := h * (1 - R)

/-- **Zero recovery specialisation**: the fair spread equals the hazard rate.
Recovers `creditSpread_eq_hazard` (the `R = 0` reduced-form case in
`Credit.lean`). -/
lemma cdsFairSpread_zero_recovery (h : ℝ) : cdsFairSpread h 0 = h := by
  unfold cdsFairSpread; ring

/-- **Leg-equality characterisation**: with `factor` the common annuity
factor `(1 − e^{−(r+h)T}) / (r + h)`, the fair spread is the unique value
making `c · factor = (1 − R) · h · factor`. -/
theorem cds_leg_equality (h R factor c : ℝ) (h_factor_ne : factor ≠ 0) :
    c * factor = (1 - R) * h * factor ↔ c = cdsFairSpread h R := by
  unfold cdsFairSpread
  constructor
  · intro heq
    have := mul_right_cancel₀ h_factor_ne heq
    linarith
  · intro hc
    rw [hc]; ring

end HybridVerify
