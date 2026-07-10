/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.ExponentialDiscount

/-!
# Forward rate from a non-flat spot-rate curve

Given a continuously-compounded spot-rate curve `T ↦ R(T)` with `R'(T)`, the
zero-coupon bond price is `P(T) = exp(−T · R(T))`, so

  `forwardRate(T) := −d/dT log P(T) = d/dT [T · R(T)] = R(T) + T · R'(T)`.

This generalizes the flat-curve case (`R(T) ≡ R₀ ⇒ forward = R₀`) covered by
`hasDerivAt_neg_log_zcb_T` in `CouponBonds.lean`. The non-flat case is purely
the product-rule chain rule applied to `T · R(T)`.

This is an instance of the `Foundations/ExponentialDiscount` principle at
`H(T) = T · R(T)`: the forward rate is the negative log-derivative of the
discount factor `exp(−H(T))`. The calculus lemma `hasDerivAt_T_mul_spotRate`
supplies `H'`, and `forwardRate_eq_neg_log_discount` routes it through the
principle to express the result in terms of the actual bond price `P(T)`.

Result:

* `hasDerivAt_T_mul_spotRate`: the forward-rate derivative formula
  `d/dT (T·R(T)) = R(T) + T·R'(T)` — this *is* the non-flat-curve forward rate
  in the `−log P` parametrisation.
* `forwardRate_eq_neg_log_discount`: forward rate as `−d/dT log P(T)` with the
  actual discount factor `P(T) = exp(−T · R(T))`, via the
  `ExponentialDiscount` principle.
-/

@[expose] public section

namespace MathFin

/-- **Forward-rate calculus identity** / **forward rate from a non-flat spot
curve**: `d/dT [T · R(T)] = R(T) + T · R'(T)` when `R` is differentiable at `T`.
Writing `F(T) := −log P(T) = T · R(T)` for a zero-coupon bond `P(T) =
exp(−T·R(T))`, the instantaneous forward rate at horizon `T` is exactly this
derivative `F'(T) = R(T) + T·R'(T)` — so this single lemma *is* the
non-flat-curve forward-rate formula (in the `−log P` parametrisation; the
version against the actual discount factor is `forwardRate_eq_neg_log_discount`
below). -/
theorem hasDerivAt_T_mul_spotRate {R : ℝ → ℝ} {R'_T T : ℝ}
    (hR : HasDerivAt R R'_T T) :
    HasDerivAt (fun t ↦ t * R t) (R T + T * R'_T) T := by
  have h_id : HasDerivAt (fun t : ℝ ↦ t) 1 T := hasDerivAt_id _
  have h_mul := h_id.mul hR
  convert h_mul using 1 <;> first | rfl | ring

/-- **Forward rate as the negative log-derivative of the bond price**
(`Foundations/ExponentialDiscount`, instantiated at `H(T) = T · R(T)`). The
zero-coupon bond is `P(T) = exp(−T · R(T))`; the instantaneous forward rate
`−d/dT log P(T)` equals `R(T) + T · R'(T)`. Unlike `hasDerivAt_T_mul_spotRate`,
this states the result against the *actual* discount factor rather than the
`−log P` shortcut, by routing the calculus lemma through the
`rate_eq_neg_log_deriv` principle. -/
theorem forwardRate_eq_neg_log_discount {R : ℝ → ℝ} {R'_T T : ℝ}
    (hR : HasDerivAt R R'_T T) :
    HasDerivAt (fun t ↦ -(Real.log (Real.exp (-(t * R t))))) (R T + T * R'_T) T :=
  rate_eq_neg_log_deriv (hasDerivAt_T_mul_spotRate hR)

end MathFin
