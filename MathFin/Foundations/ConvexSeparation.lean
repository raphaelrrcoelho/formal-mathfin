/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Separating-functional kernel for the finite Fundamental Theorem of Asset Pricing

A finite-dimensional subspace `V ⊆ (ι → ℝ)` disjoint from the standard simplex
admits a strictly-positive dual functional that annihilates it. This is the
geometric heart of the finite-state FTAP: when the attainable-gains subspace of a
market misses the simplex (no arbitrage), the separating hyperplane *is* the
equivalent martingale measure (a strictly-positive pricing functional).

The separation is `geometric_hahn_banach_compact_closed` (the simplex is compact
convex; `V` is closed because it is finite-dimensional). A linear functional
bounded below on a subspace vanishes on it, and its values on the simplex
vertices `Pi.single i 1` give the strictly-positive dual.

## Main result

* `MathFin.exists_pos_dual_of_disjoint_stdSimplex`
-/

@[expose] public section

namespace MathFin

open scoped BigOperators

/-- **Separating-dual kernel.** A subspace `V` of the finite-dimensional space
`ι → ℝ` that meets the standard simplex only outside itself admits a
strictly-positive vector `q` whose induced functional annihilates `V`. -/
theorem exists_pos_dual_of_disjoint_stdSimplex
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : Submodule ℝ (ι → ℝ)) (hV : ∀ v ∈ V, v ∉ stdSimplex ℝ ι) :
    ∃ q : ι → ℝ, (∀ i, 0 < q i) ∧ ∀ v ∈ V, ∑ i, q i * v i = 0 := by
  classical
  -- The standard simplex is convex and compact; `V` is convex and closed
  -- (a finite-dimensional subspace of a finite-dimensional normed space).
  have hconvΔ : Convex ℝ (stdSimplex ℝ ι) := convex_stdSimplex ℝ ι
  have hcompΔ : IsCompact (stdSimplex ℝ ι) := isCompact_stdSimplex ℝ ι
  have hconvV : Convex ℝ (V : Set (ι → ℝ)) := V.convex
  have hclosedV : IsClosed (V : Set (ι → ℝ)) := V.closed_of_finiteDimensional
  have hdisj : Disjoint (stdSimplex ℝ ι) (V : Set (ι → ℝ)) := by
    rw [Set.disjoint_left]
    exact fun x hxΔ hxV => hV x hxV hxΔ
  -- Strict separation: `f < u` on the simplex, `u < v`, `v < f` on `V`.
  obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
    geometric_hahn_banach_compact_closed hconvΔ hcompΔ hconvV hclosedV hdisj
  -- A linear functional bounded below on a subspace vanishes on it.
  have hf0 : ∀ w ∈ V, f w = 0 := by
    intro w hw
    by_contra hne
    have hmem : ((v - 1) / f w) • w ∈ V := V.smul_mem _ hw
    have hval : f (((v - 1) / f w) • w) = v - 1 := by
      rw [map_smul, smul_eq_mul]
      field_simp
    have hlt := hfv _ hmem
    rw [hval] at hlt
    linarith
  -- Hence `v < 0` (take `w = 0 ∈ V`).
  have hv_neg : v < 0 := by
    have h0 := hfv 0 V.zero_mem
    rw [map_zero] at h0
    linarith
  -- Each simplex vertex `Pi.single i 1` has `f (single i 1) < 0`.
  have hsingle_mem : ∀ i, (Pi.single i (1 : ℝ)) ∈ stdSimplex ℝ ι := by
    intro i
    refine ⟨fun j => ?_, ?_⟩
    · rw [Pi.single_apply]; split <;> norm_num
    · simp [Finset.sum_pi_single']
  have hsingle_neg : ∀ i, f (Pi.single i (1 : ℝ)) < 0 := by
    intro i
    have := hfu _ (hsingle_mem i)
    linarith
  refine ⟨fun i => - f (Pi.single i 1), fun i => by
    have := hsingle_neg i; linarith, fun w hw => ?_⟩
  -- `w = ∑ i, w i • single i 1`, so `f w = ∑ i, w i * f (single i 1) = 0`.
  have hwsum : w = ∑ i, w i • Pi.single i (1 : ℝ) := by
    funext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, mul_one]
    · intro b _ hb; rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hfw : f w = ∑ i, w i * f (Pi.single i 1) := by
    conv_lhs => rw [hwsum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have hzero : ∑ i, w i * f (Pi.single i 1) = 0 := by rw [← hfw, hf0 w hw]
  calc ∑ i, (- f (Pi.single i (1 : ℝ))) * w i
      = - ∑ i, w i * f (Pi.single i 1) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hzero, neg_zero]

end MathFin
