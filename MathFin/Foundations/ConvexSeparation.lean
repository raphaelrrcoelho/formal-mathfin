/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.ConvexDuality

/-!
# Separating-functional kernel for the finite Fundamental Theorem of Asset Pricing

A finite-dimensional subspace `V ⊆ (ι → ℝ)` disjoint from the standard simplex
admits a strictly-positive dual functional that annihilates it. This is the
geometric heart of the finite-state FTAP: when the attainable-gains subspace of a
market misses the simplex (no arbitrage), the separating hyperplane *is* the
equivalent martingale measure (a strictly-positive pricing functional).

This kernel is **derived** from the cone-separation root
`exists_pos_separating_of_cone_disjoint_simplex` (`MathFin/Foundations/ConvexDuality.lean`):
a subspace is a two-sided cone, so the root's one-sided `≤ 0` bound plus neg-closure
yields the two-sided `= 0` annihilation. It is the subspace case of the convex-duality
unification.

The underlying separation is the cone root `MathFin.exists_pos_separating_of_cone_disjoint_simplex`
(`Foundations/ConvexDuality.lean`), specialised to the two-sided subspace case.

## Main result

* `MathFin.exists_pos_dual_of_disjoint_stdSimplex`
-/

@[expose] public section

namespace MathFin


/-- **Separating-dual kernel.** A subspace `V` of the finite-dimensional space
`ι → ℝ` that meets the standard simplex only outside itself admits a
strictly-positive vector `q` whose induced functional annihilates `V`. -/
theorem exists_pos_dual_of_disjoint_stdSimplex
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : Submodule ℝ (ι → ℝ)) (hV : ∀ v ∈ V, v ∉ stdSimplex ℝ ι) :
    ∃ q : ι → ℝ, (∀ i, 0 < q i) ∧ ∀ v ∈ V, ∑ i, q i * v i = 0 := by
  classical
  -- A subspace is a two-sided cone: apply the cone-separation root to `V`, then
  -- use neg-closure to promote the one-sided `≤ 0` to the two-sided `= 0`.
  obtain ⟨q, hpos, hle⟩ :=
    exists_pos_separating_of_cone_disjoint_simplex (V : Set (ι → ℝ)) V.convex
      V.closed_of_finiteDimensional (fun x hx c _ ↦ V.smul_mem c hx)
      (by rw [Set.disjoint_left]; exact fun x hxΔ hxV ↦ hV x hxV hxΔ)
  refine ⟨q, hpos, fun v hv ↦ le_antisymm (hle v hv) ?_⟩
  have hneg := hle (-v) (V.neg_mem hv)
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at hneg
  linarith

end MathFin
