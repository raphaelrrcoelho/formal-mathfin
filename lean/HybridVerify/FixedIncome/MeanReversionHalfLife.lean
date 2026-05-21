/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.FixedIncome.Vasicek

/-!
# Mean-reversion half-life (Vasicek / Ornstein-Uhlenbeck)

For the deterministic Vasicek (or OU) trajectory

  `r(t) = θ + (r₀ − θ) · exp(−κ · t)`,

the **half-life** is the time `t₁ₐ` at which the gap from the mean `θ` is half
the initial gap:

  `r(t₁ₐ) − θ = (r₀ − θ) / 2`     ⟺     `exp(−κ · t₁ₐ) = 1/2`     ⟺     `t₁ₐ = log 2 / κ`.

The half-life is independent of `θ` and `r₀`; only the mean-reversion rate
`κ` matters.

## Results

* `meanReversionHalfLife`: `log 2 / κ`.
* `vasicekDeterministic_at_halfLife`: the closed-form trajectory at the
  half-life has closed half the gap from `θ`.
-/

namespace HybridVerify

open Real

/-- **Half-life** of mean-reverting decay at rate `κ`: the time at which the
gap from the long-run mean is half its initial value.

Independent of the initial condition `r₀` and the long-run mean `θ` — only
the rate `κ` matters. -/
noncomputable def meanReversionHalfLife (κ : ℝ) : ℝ := Real.log 2 / κ

/-- **At the half-life**, the Vasicek deterministic trajectory has closed
exactly half the gap from `θ`: `r(t₁ₐ) − θ = (r₀ − θ) / 2`. -/
theorem vasicekDeterministic_at_halfLife (r₀ θ κ : ℝ) (hκ : 0 < κ) :
    vasicekDeterministic r₀ θ κ (meanReversionHalfLife κ) - θ =
      (r₀ - θ) / 2 := by
  unfold vasicekDeterministic meanReversionHalfLife
  -- Show exp(−κ · log 2 / κ) = 1/2.
  have hκ_ne : κ ≠ 0 := hκ.ne'
  have h_inner : κ * (Real.log 2 / κ) = Real.log 2 := by field_simp
  have h_exp : Real.exp (-(κ * (Real.log 2 / κ))) = 1 / 2 := by
    rw [h_inner, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  rw [h_exp]
  ring

end HybridVerify
