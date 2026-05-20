/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Forward rate from a non-flat spot-rate curve

Given a continuously-compounded spot-rate curve `T ↦ R(T)` with `R'(T)`, the
zero-coupon bond price is `P(T) = exp(−T · R(T))`, so

  `forwardRate(T) := −d/dT log P(T) = d/dT [T · R(T)] = R(T) + T · R'(T)`.

This generalizes the flat-curve case (`R(T) ≡ R₀ ⇒ forward = R₀`) covered by
`forwardRate_eq_spot_flat` in `ZCB.lean`. The non-flat case is purely the
product-rule chain rule applied to `T · R(T)`.

Result:

* `hasDerivAt_T_mul_spotRate`: derivative formula `d/dT (T·R(T)) = R(T) + T·R'(T)`.
* `forwardRate_nonFlat_eq`: closed-form forward rate from spot rate and its
  derivative.
-/

namespace HybridVerify

/-- **Forward-rate calculus identity**: `d/dT [T · R(T)] = R(T) + T · R'(T)`
when `R` is differentiable at `T`. -/
theorem hasDerivAt_T_mul_spotRate {R : ℝ → ℝ} {R'_T T : ℝ}
    (hR : HasDerivAt R R'_T T) :
    HasDerivAt (fun t => t * R t) (R T + T * R'_T) T := by
  have h_id : HasDerivAt (fun t : ℝ => t) 1 T := hasDerivAt_id _
  have h_mul := h_id.mul hR
  convert h_mul using 1
  ring

/-- **Forward rate from non-flat spot rate** (in terms of `−log P(T)` instead
of `P(T)` to avoid the chain through `exp`). For
`F(T) := -log(P(T)) = T · R(T)` we get `F'(T) = R(T) + T · R'(T)`. The
instantaneous forward rate at horizon `T` is exactly this derivative, hence
the non-flat-curve formula. -/
theorem forwardRate_nonFlat_eq {R : ℝ → ℝ} {R'_T T : ℝ}
    (hR : HasDerivAt R R'_T T) :
    HasDerivAt (fun t => t * R t) (R T + T * R'_T) T :=
  hasDerivAt_T_mul_spotRate hR

end HybridVerify
