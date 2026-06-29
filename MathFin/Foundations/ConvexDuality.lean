/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Cone-separation root for the convex-duality unification

A closed convex **cone** `C ⊆ (ι → ℝ)` disjoint from the standard simplex admits a strictly-positive
functional `q` that is `≤ 0` on `C`. This is the geometric heart shared by the FTAP (attainable-gains
cone), the coherent-risk representation (acceptance cone), and superhedging (super-replication cone).
It generalizes `MathFin.exists_pos_dual_of_disjoint_stdSimplex` (a *subspace*, two-sided `= 0`) to a
*cone* (one-sided `≤ 0`). The separation is `geometric_hahn_banach_compact_closed`; the cone's
homogeneity upgrades the subspace's two-sided vanishing to a one-sided sign bound.

## API at this pin (Step 1 spike)
The cone is represented as `C : Set (ι → ℝ)` carrying three hypotheses — `Convex ℝ C`, `IsClosed C`,
and the homogeneity `∀ x ∈ C, ∀ c ≥ 0, c • x ∈ C`. The confirmed Mathlib constants used here are
`geometric_hahn_banach_compact_closed`, `convex_stdSimplex`, `isCompact_stdSimplex`,
`Finset.sum_pi_single'`, `Pi.single_eq_same`, `Pi.single_eq_of_ne`, `Finset.sum_eq_single`,
`Finset.sum_neg_distrib`, `map_sum`, `map_smul`, `map_zero`, and `div_nonneg_iff`. (Note:
`ConvexCone.dual` is not a constant at this pin, so we keep the explicit `Set`-with-homogeneity
representation rather than the bundled `ConvexCone`/`PointedCone` types.)

## Main result
* `MathFin.exists_pos_separating_of_cone_disjoint_simplex`
-/

@[expose] public section

namespace MathFin

open scoped BigOperators

/-- **Cone separation root.** A closed convex cone `C ⊆ (ι → ℝ)` whose only point in
the standard simplex is excluded admits a strictly-positive functional `q` that is
`≤ 0` on `C` (a separating supporting functional). This is the geometric heart shared
by the FTAP (gains cone), the coherent-risk representation (acceptance cone), and
superhedging (super-replication cone). Generalizes `exists_pos_dual_of_disjoint_stdSimplex`
(subspace ⇒ two-sided `= 0`) to a cone (one-sided `≤ 0`). -/
theorem exists_pos_separating_of_cone_disjoint_simplex
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : Set (ι → ℝ)) (hCconv : Convex ℝ C) (hCclosed : IsClosed C)
    (hCcone : ∀ ⦃x⦄, x ∈ C → ∀ ⦃c : ℝ⦄, 0 ≤ c → c • x ∈ C)
    (hdisj : Disjoint (stdSimplex ℝ ι) C) :
    ∃ q : ι → ℝ, (∀ i, 0 < q i) ∧ ∀ v ∈ C, ∑ i, q i * v i ≤ 0 := by
  classical
  rcases C.eq_empty_or_nonempty with hCempty | hCne
  · -- empty cone: q = 1, the C-bound is vacuous
    exact ⟨fun _ => 1, fun _ => one_pos, fun w hw => by
      rw [hCempty] at hw; simp at hw⟩
  -- nonempty cone ⇒ 0 ∈ C (take c = 0)
  obtain ⟨x₀, hx₀⟩ := hCne
  have h0C : (0 : ι → ℝ) ∈ C := by simpa using hCcone hx₀ (le_refl (0 : ℝ))
  have hconvΔ : Convex ℝ (stdSimplex ℝ ι) := convex_stdSimplex ℝ ι
  have hcompΔ : IsCompact (stdSimplex ℝ ι) := isCompact_stdSimplex ℝ ι
  obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
    geometric_hahn_banach_compact_closed hconvΔ hcompΔ hCconv hCclosed hdisj
  -- v < f 0 = 0
  have hv_neg : v < 0 := by have h0 := hfv 0 h0C; rwa [map_zero] at h0
  -- f ≥ 0 on C: a ray with f c < 0 is unbounded below on C, violating hfv
  have hfC_nonneg : ∀ c ∈ C, 0 ≤ f c := by
    intro c hc
    by_contra hlt
    rw [not_le] at hlt                      -- hlt : f c < 0
    have hfcne : f c ≠ 0 := ne_of_lt hlt
    have ht : 0 ≤ (v - 1) / f c := by
      rw [div_nonneg_iff]; right
      exact ⟨by linarith, le_of_lt hlt⟩     -- v-1 ≤ 0 and f c ≤ 0
    have hmem : ((v - 1) / f c) • c ∈ C := hCcone hc ht
    have hval : f (((v - 1) / f c) • c) = v - 1 := by
      rw [map_smul, smul_eq_mul]; field_simp
    have hlt2 := hfv _ hmem; rw [hval] at hlt2; linarith
  -- vertices: f(single i) < u < v < 0
  have hsingle_mem : ∀ i, (Pi.single i (1 : ℝ)) ∈ stdSimplex ℝ ι := by
    intro i; refine ⟨fun j => ?_, ?_⟩
    · rw [Pi.single_apply]; split <;> norm_num
    · simp [Finset.sum_pi_single']
  have hsingle_neg : ∀ i, f (Pi.single i (1 : ℝ)) < 0 := fun i => by
    have := hfu _ (hsingle_mem i); linarith
  refine ⟨fun i => - f (Pi.single i 1), fun i => by have := hsingle_neg i; linarith, fun w hw => ?_⟩
  have hwsum : w = ∑ i, w i • Pi.single i (1 : ℝ) := by
    funext j; rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, mul_one]
    · intro b _ hb; rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hfw : f w = ∑ i, w i * f (Pi.single i 1) := by
    conv_lhs => rw [hwsum]
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  calc ∑ i, (- f (Pi.single i (1 : ℝ))) * w i
      = - ∑ i, w i * f (Pi.single i 1) := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = - f w := by rw [← hfw]
    _ ≤ 0 := by have := hfC_nonneg w hw; linarith

end MathFin
