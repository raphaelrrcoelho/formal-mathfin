/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.RiskMeasures.AcceptanceSet

/-!
# Worst-case loss: a concrete coherent risk measure

The most conservative coherent risk measure, `worstCase X = maxᵢ (-Xᵢ)`, is a concrete instance of
`IsCoherentRisk`. Its Artzner–Delbaen–Eber–Heath representation (from `coherentRisk_isLUB`) specialises
to the supremum of expected loss over the *entire* probability simplex — making the abstract
representation tangible: the worst case over states equals the worst case over all mixtures of states.

## Main results
* `MathFin.worstCase_isCoherent` — worst-case loss satisfies the four ADEH axioms
* `MathFin.worstCase_isLUB` — its representation is the sup over the probability simplex
-/

@[expose] public section

namespace MathFin


variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Worst-case loss: the most conservative coherent risk measure. -/
noncomputable def worstCase (X : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i ↦ - X i)

/-- Each `-Xᵢ` lower-bounds the worst-case loss `worstCase X`. -/
lemma le_worstCase (X : ι → ℝ) (i : ι) : - X i ≤ worstCase X :=
  Finset.le_sup' (fun i ↦ - X i) (Finset.mem_univ i)

/-- Any uniform upper bound on the `-Xᵢ` bounds `worstCase X` above. -/
lemma worstCase_le {X : ι → ℝ} {a : ℝ} (h : ∀ i, - X i ≤ a) : worstCase X ≤ a :=
  Finset.sup'_le Finset.univ_nonempty (fun i ↦ - X i) (fun i _ ↦ h i)

/-- Worst-case loss satisfies the four ADEH coherent-risk axioms. -/
lemma worstCase_isCoherent : IsCoherentRisk (worstCase (ι := ι)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y hXY
    exact worstCase_le (fun i ↦ le_trans (neg_le_neg (hXY i)) (le_worstCase X i))
  · intro X m
    apply le_antisymm
    · exact worstCase_le (fun i ↦ by
        show - (X i + m) ≤ worstCase X - m
        linarith [le_worstCase X i])
    · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i ↦ - X i)
      have hwx : worstCase X = - X i := hi
      have h2 : - (X i + m) ≤ worstCase (fun i ↦ X i + m) := le_worstCase (fun i ↦ X i + m) i
      rw [hwx]; linarith [h2]
  · intro l hl X
    apply le_antisymm
    · refine worstCase_le (fun i ↦ ?_)
      have hsmul : - (l • X) i = l * (- X i) := by simp [Pi.smul_apply, smul_eq_mul, mul_neg]
      rw [hsmul]
      exact mul_le_mul_of_nonneg_left (le_worstCase X i) hl
    · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i ↦ - X i)
      have hwx : worstCase X = - X i := hi
      have hsmul : - (l • X) i = l * (- X i) := by simp [Pi.smul_apply, smul_eq_mul, mul_neg]
      have h2 : - (l • X) i ≤ worstCase (l • X) := le_worstCase (l • X) i
      rw [hwx]
      rw [hsmul] at h2
      exact h2
  · intro X Y
    refine worstCase_le (fun i ↦ ?_)
    have hx := le_worstCase X i
    have hy := le_worstCase Y i
    simp only [Pi.add_apply, neg_add_rev]
    linarith

/-- The representing set of worst-case loss is the entire probability simplex. -/
lemma representingSet_worstCase :
    representingSet (worstCase (ι := ι)) = stdSimplex ℝ ι := by
  ext q
  constructor
  · rintro ⟨hnn, hsum, _⟩; exact ⟨hnn, hsum⟩
  · rintro ⟨hnn, hsum⟩
    refine ⟨hnn, hsum, fun Z hZ ↦ ?_⟩
    refine Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hnn i) ?_)
    have h1 : - Z i ≤ worstCase Z := le_worstCase Z i
    have h2 : worstCase Z ≤ 0 := hZ
    linarith

/-- **Worst-case loss is the supremum of expected loss over the entire probability simplex** —
the concrete instance of the ADEH representation. -/
theorem worstCase_isLUB (X : ι → ℝ) :
    IsLUB ((fun q ↦ ∑ i, q i * (- X i)) '' stdSimplex ℝ ι) (worstCase X) := by
  rw [← representingSet_worstCase]
  exact coherentRisk_isLUB worstCase_isCoherent X

end MathFin
