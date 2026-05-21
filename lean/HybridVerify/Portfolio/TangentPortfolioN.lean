/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# N-asset tangent portfolio FOC (cross-product form)

For `N` risky assets indexed by `i ∈ s` (a `Finset`), with excess returns
`μ_excess i := μ i − r_f` and covariance kernel `Σ : ι → ι → ℝ`, the
**tangent portfolio** maximises the Sharpe ratio under the unit-budget
constraint. The classical closed form is `w* ∝ Σ⁻¹ · μ_excess`, equivalently

  `Σ · w* = λ · μ_excess`     for some scalar `λ ≠ 0`.

Rather than introduce matrix inverses, we capture the tangent characterisation
via the **cross-product FOC**: the marginal-variance vector `Σw` is parallel
to the excess-return vector `μ_excess`. Equivalently,

  `μ_excess(j) · (Σw)_i = μ_excess(i) · (Σw)_j`     for all `i, j ∈ s`.

This is exactly the Sharpe FOC at every cross-section, and is the natural
N-asset generalisation of `tangentTwo_satisfies_FOC` (which was the
`i = 1, j = 2` instance written out).

## Results

* `IsTangentPortfolioN`: cross-product FOC predicate.
* `isTangent_of_proportional`: if `Σw = λ · μ_excess` (any scalar `λ`), then
  `w` satisfies the FOC. The matrix-inverse characterisation
  `w = Σ⁻¹·μ_excess` (or any scalar multiple) is the special case.
-/

namespace HybridVerify

open Finset

variable {ι : Type*}

/-- **N-asset tangent portfolio cross-product FOC**: the marginal-variance
vector `(Σw)_i := ∑_k Σ_{i,k} w_k` is parallel to the excess-return vector
`μ_excess`, expressed via cross products. -/
def IsTangentPortfolioN (s : Finset ι) (μ_excess : ι → ℝ)
    (Sg : ι → ι → ℝ) (w : ι → ℝ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s,
    μ_excess j * (∑ k ∈ s, Sg i k * w k) =
      μ_excess i * (∑ k ∈ s, Sg j k * w k)

/-- **Sufficient condition for tangency**: if `Σw = λ · μ_excess` for some
scalar `λ`, then `w` is a tangent portfolio.

This captures the matrix-inverse characterisation `w ∝ Σ⁻¹ · μ_excess`
without requiring matrix-inverse machinery: any scalar multiple of `Σ⁻¹·μ`
satisfies `Σw = λ · μ`, hence the FOC. -/
theorem isTangent_of_proportional (s : Finset ι) (μ_excess : ι → ℝ)
    (Sg : ι → ι → ℝ) (w : ι → ℝ) (lam : ℝ)
    (h : ∀ i ∈ s, (∑ k ∈ s, Sg i k * w k) = lam * μ_excess i) :
    IsTangentPortfolioN s μ_excess Sg w := by
  intro i hi j hj
  rw [h i hi, h j hj]
  ring

end HybridVerify
