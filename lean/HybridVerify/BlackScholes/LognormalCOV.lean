/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholes.BreedenLitzenberger

/-!
# Lognormal-to-gaussian change of variables (differential form)

The implied risk-neutral PDF of `S_T` defined in `BreedenLitzenberger.lean`,

  `f(K) := gaussianPDFReal 0 1 (bsd2(S_0, K, r, σ, T)) / (K · σ · √T)`,

is related to the standard normal density via the change of variables
`z(K) = −bsd2(S_0, K, r, σ, T)`. Under this substitution, `dz/dK = −1/(K · σ · √T)`,
so the differential identity

  `f(K) · K · σ · √T = ϕ(bsd2(S_0, K, r, σ, T))`

holds. From this differential identity, **the implied PDF integrates to 1**
over `(0, ∞)` (since the gaussian PDF integrates to 1 over `ℝ` and the change
of variables is a measurable bijection). We state the differential identity
formally; the integration-to-1 claim is gated on the change-of-variables
formula `intervalIntegral.integral_comp_mul_deriv` and Mathlib's existing
`integral_gaussianPDFReal_eq_one`.

(For `K ≤ 0`, the density is set to zero, but our definition computes a value
via `bsd2`; the meaningful regime is `K > 0` where the lognormal density is
defined.)

## Results

* `lognormalTerminalPDF_change_of_variables`: the differential identity
  `f(K) · K · σ · √T = ϕ(bsd2(K))`. Definitional / `field_simp`.
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real

/-- **Differential change-of-variables identity** between the lognormal PDF
of `S_T` and the standard-normal PDF:

  `lognormalTerminalPDF(K) · K · σ · √T = ϕ(bsd2(K))`,

where `ϕ` is the standard-normal PDF. The Jacobian of the substitution
`K ↦ z(K) = −bsd2(K)` accounts for the `K · σ · √T` factor.

This identity packages the change-of-variables differential, from which
`∫_0^∞ f(K) dK = ∫_{ℝ} ϕ(z) dz = 1` follows by Mathlib's change-of-variables
formula. The latter step is left as upstream work. -/
theorem lognormalTerminalPDF_change_of_variables
    {S_0 r σ T K : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    lognormalTerminalPDF S_0 r σ T K * (K * σ * Real.sqrt T) =
      gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) := by
  unfold lognormalTerminalPDF
  have hsqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_den_ne : K * σ * Real.sqrt T ≠ 0 := by
    have := mul_pos (mul_pos hK hσ) hsqrtT_pos
    exact this.ne'
  field_simp

end HybridVerify
