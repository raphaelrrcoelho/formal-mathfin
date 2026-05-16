/-
  HybridVerify.HittingTimeOpen
  Proposition 4.3.6 (full formal proof): For a continuous, adapted process X
  and an open set A, the hitting time `τ_A = inf{t ≥ 0 : X_t ∈ A}` is a
  stopping time w.r.t. a right-continuous filtration.

  Proof strategy: by `IsStoppingTime` constructor
  `MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous`,
  it suffices to show `{ω | τ ω < i} ∈ 𝓕 i` for every `i : ℝ`. By the
  rationals-density argument:
       `{ω | τ ω < i} = ⋃_{q ∈ ℚ ∩ [0, i)} {ω | X_q ω ∈ A}`
  Each `{ω | X_q ω ∈ A} ∈ 𝓕 q ⊆ 𝓕 i` (by adaptedness + A measurable, since
  open ⇒ measurable). A countable union of `𝓕 i`-measurable sets is
  `𝓕 i`-measurable. Done.

  No external sorry dependencies — full derivation from Mathlib primitives
  (`Real.exists_rat_btwn`, `IsOpen.preimage`, `Adapted`, and
  `isStoppingTime_of_measurableSet_lt_of_isRightContinuous`).
-/
import Mathlib

namespace HybridVerify

open MeasureTheory ProbabilityTheory

variable {Ω β : Type*} {mΩ : MeasurableSpace Ω}

/-- Key set identity: for continuous adapted X and open A, the set
    `{ω | hittingAfter X A 0 ω < i}` equals the countable union over
    nonnegative rationals `q < i` of `{ω | X (q : ℝ) ω ∈ A}`.

    The non-trivial direction uses continuity of X and openness of A to
    upgrade an arbitrary real witness to a rational witness via density. -/
private lemma hittingAfter_lt_eq_iUnion_rationals
    [TopologicalSpace β]
    {X : ℝ → Ω → β} {A : Set β}
    (hX_cont : ∀ ω, Continuous (fun t => X t ω)) (hA_open : IsOpen A)
    (i : ℝ) :
    {ω | hittingAfter X A 0 ω < (i : WithTop ℝ)}
      = ⋃ (q : ℚ) (_ : (0 : ℝ) ≤ (q : ℝ)) (_ : (q : ℝ) < i),
          {ω | X (q : ℝ) ω ∈ A} := by
  ext ω
  rw [Set.mem_setOf_eq, hittingAfter_lt_iff]
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Ico, exists_prop]
  constructor
  · rintro ⟨j, ⟨hj_nn, hj_lt⟩, hXj⟩
    -- continuity + density of rationals: find rational q ∈ [0, i) close
    -- enough to j that X_q ω ∈ A.
    have h_pre : (fun t : ℝ => X t ω) ⁻¹' A ∈ nhds j :=
      ((hX_cont ω).continuousAt).preimage_mem_nhds (hA_open.mem_nhds hXj)
    rcases lt_or_eq_of_le hj_nn with hj_pos | hj_zero
    · -- j > 0: use a 2-sided neighborhood (j - δ, j + δ) ⊆ [0, i) ∩ preimage.
      obtain ⟨δ, hδ_pos, hδ_sub⟩ : ∃ δ > 0,
          Set.Ioo (j - δ) (j + δ) ⊆ (fun t : ℝ => X t ω) ⁻¹' A := by
        have h_nhds := Metric.mem_nhds_iff.mp h_pre
        obtain ⟨ε, hε_pos, hε_sub⟩ := h_nhds
        refine ⟨ε, hε_pos, fun s hs => ?_⟩
        refine hε_sub ?_
        simp only [Metric.mem_ball, Real.dist_eq, Set.mem_Ioo] at hs ⊢
        cases hs with | intro h1 h2 => exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
      -- Shrink δ so (j - δ, j + δ) ⊆ (0, i). Halve to get strict inequalities.
      have h_min_pos : 0 < min δ (min j (i - j)) :=
        lt_min hδ_pos (lt_min hj_pos (by linarith))
      set δ' := min δ (min j (i - j)) / 2 with hδ'_def
      have hδ'_pos : 0 < δ' := half_pos h_min_pos
      have hδ'_lt_min : δ' < min δ (min j (i - j)) := half_lt_self h_min_pos
      have hδ'_le_δ : δ' ≤ δ := hδ'_lt_min.le.trans (min_le_left _ _)
      have hδ'_lt_j : δ' < j :=
        hδ'_lt_min.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hδ'_lt_i_sub_j : δ' < i - j :=
        hδ'_lt_min.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have h_sub_pre : Set.Ioo (j - δ') (j + δ') ⊆ (fun t : ℝ => X t ω) ⁻¹' A := by
        intro s hs
        refine hδ_sub ⟨?_, ?_⟩
        · linarith [hs.1, hδ'_le_δ]
        · linarith [hs.2, hδ'_le_δ]
      -- Find rational q ∈ (j - δ', j + δ').
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show j - δ' < j + δ' by linarith)
      refine ⟨q, ?_, ?_, h_sub_pre ⟨hq1, hq2⟩⟩
      · linarith [hδ'_lt_j]
      · linarith [hδ'_lt_i_sub_j]
    · -- j = 0: take q = 0 (rational), which is in [0, i) since i > 0.
      refine ⟨0, ?_, ?_, ?_⟩
      · simp
      · push_cast
        linarith
      · push_cast
        rw [show (0 : ℝ) = j from hj_zero]
        exact hXj
  · rintro ⟨q, hq_nn, hq_lt, hXq⟩
    exact ⟨(q : ℝ), ⟨hq_nn, hq_lt⟩, hXq⟩

/-- Measurability of `{ω | hittingAfter X A 0 ω < ↑i}`. -/
private lemma measurableSet_hittingAfter_lt_of_open
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {𝓕 : Filtration ℝ mΩ} {X : ℝ → Ω → β} {A : Set β}
    (hX_cont : ∀ ω, Continuous (fun t => X t ω)) (hX_adapted : Adapted 𝓕 X)
    (hA_open : IsOpen A) (i : ℝ) :
    MeasurableSet[𝓕 i] {ω | hittingAfter X A 0 ω < (i : WithTop ℝ)} := by
  rw [hittingAfter_lt_eq_iUnion_rationals hX_cont hA_open]
  refine MeasurableSet.iUnion fun q => ?_
  refine MeasurableSet.iUnion fun hq_nn => ?_
  refine MeasurableSet.iUnion fun hq_lt => ?_
  -- {ω | X q ω ∈ A} ∈ 𝓕 q ⊆ 𝓕 i (since q < i and 𝓕 is monotone, A is open ⇒ measurable).
  have h_qi : (q : ℝ) ≤ i := hq_lt.le
  have h_meas_q : MeasurableSet[𝓕 (q : ℝ)] {ω | X (q : ℝ) ω ∈ A} :=
    hX_adapted (q : ℝ) hA_open.measurableSet
  exact 𝓕.mono h_qi _ h_meas_q

/-- Proposition 4.3.6 (full formal proof). For a continuous adapted process
    `X` and an open set `A`, the hitting time `hittingAfter X A 0` is a
    stopping time w.r.t. any right-continuous filtration. -/
theorem isStoppingTime_hittingAfter_of_open
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {𝓕 : Filtration ℝ mΩ} [𝓕.IsRightContinuous]
    {X : ℝ → Ω → β} {A : Set β}
    (hX_cont : ∀ ω, Continuous (fun t => X t ω)) (hX_adapted : Adapted 𝓕 X)
    (hA_open : IsOpen A) :
    IsStoppingTime 𝓕 (hittingAfter X A 0) := by
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro i
  exact measurableSet_hittingAfter_lt_of_open hX_cont hX_adapted hA_open i

end HybridVerify
