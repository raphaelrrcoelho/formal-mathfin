/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.ConvexDuality

/-!
# Coherent risk measures: the Artzner–Delbaen–Eber–Heath representation (finite state)

A coherent risk measure `ρ` on `ι → ℝ` (finite state space) is, by its four ADEH axioms, the supremum
of expected loss `∑ qᵢ (-Xᵢ)` over a set of representing probability measures `q`. The geometric content
is convex duality: the **acceptance cone** `{X | ρ X ≤ 0}` is a closed convex cone, and a rejected
position is separated from it by a representing density — the *same* Hahn–Banach separation that gives
the FTAP its equivalent martingale measure (here via the point-from-cone primitive
`MathFin.exists_separating_of_not_mem_cone`). This is the risk-side face of the convex-duality unification.

The representation is stated as `IsLUB` (ρ X is the least upper bound of the expected losses), which is
the precise "ρ = sup over measures" statement without the conditionally-complete-lattice `iSup` overhead.

## Main results
* `MathFin.IsCoherentRisk` — the four ADEH axioms
* `MathFin.coherentRisk_isLUB` — the representation
-/

@[expose] public section

namespace MathFin


/-- The four Artzner–Delbaen–Eber–Heath axioms of a coherent risk measure on a finite state space:
monotonicity, cash-invariance, positive homogeneity, subadditivity. -/
structure IsCoherentRisk {ι : Type*} [Fintype ι] (ρ : (ι → ℝ) → ℝ) : Prop where
  monotone : ∀ X Y : ι → ℝ, (∀ i, X i ≤ Y i) → ρ Y ≤ ρ X
  cashInvariant : ∀ (X : ι → ℝ) (m : ℝ), ρ (fun i => X i + m) = ρ X - m
  posHom : ∀ (l : ℝ), 0 ≤ l → ∀ X : ι → ℝ, ρ (l • X) = l * ρ X
  subadditive : ∀ X Y : ι → ℝ, ρ (X + Y) ≤ ρ X + ρ Y

namespace IsCoherentRisk
variable {ι : Type*} [Fintype ι] {ρ : (ι → ℝ) → ℝ}

/-- `ρ 0 = 0` (positive homogeneity at `l = 2`). -/
lemma rho_zero (hρ : IsCoherentRisk ρ) : ρ 0 = 0 := by
  have h := hρ.posHom 2 (by norm_num) 0
  rw [smul_zero] at h; linarith

/-- A coherent risk measure is convex (subadditive + positively homogeneous). -/
lemma convexOn (hρ : IsCoherentRisk ρ) : ConvexOn ℝ Set.univ ρ := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  have hsub := hρ.subadditive (a • x) (b • y)
  rw [hρ.posHom a ha, hρ.posHom b hb] at hsub
  simpa [smul_eq_mul] using hsub

/-- A finite-state coherent risk measure is continuous (a finite convex function on `ℝ^ι`). -/
lemma continuous (hρ : IsCoherentRisk ρ) : Continuous ρ := by
  rw [← continuousOn_univ]
  exact hρ.convexOn.continuousOn isOpen_univ

/-- The acceptance set `{X | ρ X ≤ 0}` is closed (ρ is continuous). -/
lemma acceptance_closed (hρ : IsCoherentRisk ρ) : IsClosed {X : ι → ℝ | ρ X ≤ 0} :=
  isClosed_le hρ.continuous continuous_const

/-- `0` is acceptable. -/
lemma zero_mem (hρ : IsCoherentRisk ρ) : (0 : ι → ℝ) ∈ {X : ι → ℝ | ρ X ≤ 0} := by
  show ρ 0 ≤ 0; rw [hρ.rho_zero]

/-- The acceptance set is a cone (positive homogeneity). -/
lemma cone (hρ : IsCoherentRisk ρ) :
    ∀ ⦃x⦄, x ∈ {X : ι → ℝ | ρ X ≤ 0} → ∀ ⦃c : ℝ⦄, 0 ≤ c → c • x ∈ {X : ι → ℝ | ρ X ≤ 0} := by
  intro x hx c hc
  show ρ (c • x) ≤ 0
  rw [hρ.posHom c hc]
  exact mul_nonpos_of_nonneg_of_nonpos hc hx

/-- The acceptance set is convex. -/
lemma convex_acceptance (hρ : IsCoherentRisk ρ) : Convex ℝ {X : ι → ℝ | ρ X ≤ 0} := by
  intro X hX Y hY a b ha hb _
  show ρ (a • X + b • Y) ≤ 0
  calc ρ (a • X + b • Y) ≤ ρ (a • X) + ρ (b • Y) := hρ.subadditive _ _
    _ = a * ρ X + b * ρ Y := by rw [hρ.posHom a ha, hρ.posHom b hb]
    _ ≤ 0 := by
        have h1 : a * ρ X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hX
        have h2 : b * ρ Y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hY
        linarith

/-- Every nonnegative position is acceptable (monotonicity). -/
lemma nonneg_mem (hρ : IsCoherentRisk ρ) {X : ι → ℝ} (hX : ∀ i, 0 ≤ X i) :
    X ∈ {X : ι → ℝ | ρ X ≤ 0} := by
  show ρ X ≤ 0
  have h := hρ.monotone 0 X (by intro i; simpa using hX i)
  rwa [hρ.rho_zero] at h

end IsCoherentRisk

/-- The representing set: probability vectors that price every acceptable position nonnegatively
(the densities separating the acceptance cone). -/
def representingSet {ι : Type*} [Fintype ι] (ρ : (ι → ℝ) → ℝ) : Set (ι → ℝ) :=
  {q | (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧ ∀ Z ∈ {Y : ι → ℝ | ρ Y ≤ 0}, 0 ≤ ∑ i, q i * Z i}

/-- **Coherent-risk representation (Artzner–Delbaen–Eber–Heath, finite state).** A coherent risk
measure `ρ` is the supremum of expected loss over its representing probability measures: `ρ X` is the
least upper bound of `{∑ qᵢ (-Xᵢ) | q ∈ representingSet ρ}`. The upper bound is cash-invariance; the
least-upper-bound is the point-from-cone separation of the rejected position `X + (ρX - ε)·1` from the
acceptance cone, normalised to a representing density. -/
theorem coherentRisk_isLUB {ι : Type*} [Fintype ι] [Nonempty ι] {ρ : (ι → ℝ) → ℝ}
    (hρ : IsCoherentRisk ρ) (X : ι → ℝ) :
    IsLUB ((fun q => ∑ i, q i * (- X i)) '' representingSet ρ) (ρ X) := by
  classical
  constructor
  · rintro y ⟨q, ⟨hq_nn, hq_sum, hq_rep⟩, rfl⟩
    show ∑ i, q i * (- X i) ≤ ρ X
    have hmem : (fun i => X i + ρ X) ∈ {Y : ι → ℝ | ρ Y ≤ 0} := by
      show ρ (fun i => X i + ρ X) ≤ 0
      rw [hρ.cashInvariant X (ρ X)]; simp
    have h0 := hq_rep _ hmem
    have hexp : ∑ i, q i * (X i + ρ X) = (∑ i, q i * X i) + ρ X := by
      rw [show (∑ i, q i * (X i + ρ X)) = ∑ i, (q i * X i + q i * ρ X) from
            Finset.sum_congr rfl fun i _ => by ring, Finset.sum_add_distrib,
          ← Finset.sum_mul, hq_sum, one_mul]
    rw [hexp] at h0
    have hneg : ∑ i, q i * (-X i) = - ∑ i, q i * X i := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hneg]; linarith
  · intro b hb
    by_contra hlt
    rw [not_le] at hlt
    set ε := ρ X - b with hε
    have hε_pos : 0 < ε := by rw [hε]; linarith
    set X' : ι → ℝ := fun i => X i + (ρ X - ε) with hX'
    have hX'_notin : X' ∉ {Y : ι → ℝ | ρ Y ≤ 0} := by
      show ¬ ρ X' ≤ 0
      rw [hX', hρ.cashInvariant X (ρ X - ε), not_le]; linarith
    obtain ⟨p, hp_le, hp_pos⟩ := exists_separating_of_not_mem_cone
      {Y : ι → ℝ | ρ Y ≤ 0} hρ.convex_acceptance hρ.acceptance_closed hρ.cone hρ.zero_mem hX'_notin
    have hp_nonpos : ∀ i, p i ≤ 0 := by
      intro i
      have hsi : (Pi.single i (1 : ℝ)) ∈ {Y : ι → ℝ | ρ Y ≤ 0} := by
        apply hρ.nonneg_mem
        intro j
        simp only [Pi.single_apply]
        split_ifs <;> norm_num
      have hle := hp_le _ hsi
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at hle
      exact hle
    have hsum_p_neg : ∑ i, p i < 0 := by
      by_contra hge
      rw [not_lt] at hge
      have hsum_zero : ∑ i, p i = 0 :=
        le_antisymm (Finset.sum_nonpos fun i _ => hp_nonpos i) hge
      have hp_zero : ∀ i, p i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonpos fun i _ => hp_nonpos i).mp hsum_zero i (Finset.mem_univ i)
      have hpX'0 : ∑ i, p i * X' i = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hp_zero i, zero_mul]
      linarith [hp_pos]
    set S := ∑ i, p i with hS
    have hS_ne : S ≠ 0 := ne_of_lt hsum_p_neg
    set q : ι → ℝ := fun i => p i / S with hq_def
    have hq_nn : ∀ i, 0 ≤ q i := fun i => by
      rw [hq_def, div_nonneg_iff]; right; exact ⟨hp_nonpos i, le_of_lt hsum_p_neg⟩
    have hq_sum : ∑ i, q i = 1 := by
      have hh : ∑ i, q i = (∑ i, p i) / S := by rw [hq_def, ← Finset.sum_div]
      rw [hh, ← hS]; exact div_self hS_ne
    have hq_rep : ∀ Z ∈ {Y : ι → ℝ | ρ Y ≤ 0}, 0 ≤ ∑ i, q i * Z i := by
      intro Z hZ
      have hpZ := hp_le Z hZ
      have heq : ∑ i, q i * Z i = (∑ i, p i * Z i) / S := by
        rw [hq_def, Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by rw [div_mul_eq_mul_div]
      rw [heq, div_nonneg_iff]; right; exact ⟨hpZ, le_of_lt hsum_p_neg⟩
    have hq_mem : q ∈ representingSet ρ := ⟨hq_nn, hq_sum, hq_rep⟩
    have hle_b : ∑ i, q i * (- X i) ≤ b := hb ⟨q, hq_mem, rfl⟩
    have hqX'_neg : ∑ i, q i * X' i < 0 := by
      have heq : ∑ i, q i * X' i = (∑ i, p i * X' i) / S := by
        rw [hq_def, Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by rw [div_mul_eq_mul_div]
      rw [heq]; exact div_neg_of_pos_of_neg hp_pos hsum_p_neg
    have hX'_exp : ∑ i, q i * X' i = (∑ i, q i * X i) + (ρ X - ε) := by
      rw [hX', show (∑ i, q i * (X i + (ρ X - ε))) = ∑ i, (q i * X i + q i * (ρ X - ε)) from
            Finset.sum_congr rfl fun i _ => by ring, Finset.sum_add_distrib,
          ← Finset.sum_mul, hq_sum, one_mul]
    have hnegX : ∑ i, q i * (-X i) = - ∑ i, q i * X i := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hnegX] at hle_b
    rw [hX'_exp] at hqX'_neg
    linarith [hle_b, hqX'_neg]

end MathFin
