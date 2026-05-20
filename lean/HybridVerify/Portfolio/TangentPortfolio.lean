/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Tangent portfolio (two-asset closed form, FOC)

With two risky assets having excess returns `r₁, r₂`, volatilities `σ₁, σ₂`,
and correlation `ρ`, the *tangent portfolio* (the Sharpe-ratio-maximizing
portfolio under the budget constraint `w₁ + w₂ = 1`) has closed-form weight

  `w₁^T = (σ₂² r₁ − ρ σ₁ σ₂ r₂) / D`,
  `D = σ₂² r₁ + σ₁² r₂ − ρ σ₁ σ₂ (r₁ + r₂)`.

The first-order condition for Sharpe maximization is

  `r₂ · (Σ·w)₁ = r₁ · (Σ·w)₂`,

i.e. the marginal variance contributions are proportional to the marginal
excess returns. We verify the closed-form `w^T` satisfies this FOC by direct
algebra.

Result:

* `tangentWeightTwo`: closed-form weight.
* `tangentTwo_satisfies_FOC`: the FOC identity at the tangent weight.
-/

namespace HybridVerify

/-- Two-asset tangent portfolio weight on asset 1.

`w₁^T = (σ₂² r₁ − ρ σ₁ σ₂ r₂) / (σ₂² r₁ + σ₁² r₂ − ρ σ₁ σ₂ (r₁ + r₂))`. -/
noncomputable def tangentWeightTwo (r₁ r₂ σ₁ σ₂ ρ : ℝ) : ℝ :=
  (σ₂^2 * r₁ - ρ * σ₁ * σ₂ * r₂) /
    (σ₂^2 * r₁ + σ₁^2 * r₂ - ρ * σ₁ * σ₂ * (r₁ + r₂))

/-- **Tangent portfolio FOC**: at the closed-form weight `w = w₁^T`,
`D · [r₂ · (w σ₁² + (1 − w) ρ σ₁ σ₂)] = D · [r₁ · (w ρ σ₁ σ₂ + (1 − w) σ₂²)]`
i.e. multiplying both sides by `D` we get a polynomial identity. Stated as
the cross-product form `r₂ · D · ((Σw)_1) = r₁ · D · ((Σw)_2)` to avoid the
division. -/
theorem tangentTwo_satisfies_FOC (r₁ r₂ σ₁ σ₂ ρ : ℝ) :
    let D := σ₂^2 * r₁ + σ₁^2 * r₂ - ρ * σ₁ * σ₂ * (r₁ + r₂)
    let w_num := σ₂^2 * r₁ - ρ * σ₁ * σ₂ * r₂  -- D · w
    let one_sub_w_num := σ₁^2 * r₂ - ρ * σ₁ * σ₂ * r₁  -- D · (1 - w)
    r₂ * (w_num * σ₁^2 + one_sub_w_num * ρ * σ₁ * σ₂) =
      r₁ * (w_num * ρ * σ₁ * σ₂ + one_sub_w_num * σ₂^2) := by
  ring

end HybridVerify
