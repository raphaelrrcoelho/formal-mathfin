/-
  HybridVerify.BrownianMartingale
  Theorem 5.1.5: Brownian motion is a martingale w.r.t. its filtration.
-/
import Mathlib
import BrownianMotion.Gaussian.BrownianMotion

namespace HybridVerify

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

structure BrownianMartingaleHyp
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ) : Prop where
  isPreBrownian : IsPreBrownian B P
  stronglyAdapted : StronglyAdapted 𝓕 B
  indep_increment_filt : ∀ ⦃s t : ℝ≥0⦄, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => B t ω - B s ω) (borel ℝ)) (𝓕 s) P

/-- For `s ≤ t : ℝ≥0`, the NNReal-valued increment-variance `max (t-s) (s-t)`
    coerces to `(t : ℝ) - (s : ℝ)` (since truncated `s - t = 0` when `s ≤ t`). -/
private lemma max_sub_eq_of_le {s t : ℝ≥0} (hst : s ≤ t) :
    ((max (t - s) (s - t) : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) := by
  have hst_zero : s - t = (0 : ℝ≥0) := tsub_eq_zero_of_le hst
  rw [hst_zero, max_eq_left (zero_le _)]
  exact NNReal.coe_sub hst

/-- Second moment of a centered real Gaussian: `∫ x, x² ∂(gaussianReal 0 v) = v`.

    Derived from Mathlib's `variance_id_gaussianReal` (variance of the identity
    under `gaussianReal m v` equals `v`) and `variance_of_integral_eq_zero`
    (when the mean is zero, variance reduces to the second moment). -/
private lemma integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x^2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h_var : variance id (gaussianReal 0 v) = (v : ℝ) := variance_id_gaussianReal
  have h_mean : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  rw [variance_of_integral_eq_zero aemeasurable_id h_mean] at h_var
  exact h_var

theorem BrownianMartingaleHyp.is_martingale
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (h : BrownianMartingaleHyp P 𝓕 B) :
    Martingale B 𝓕 P := by
  refine ⟨h.stronglyAdapted, fun s t hst => ?_⟩
  have h_int_s : Integrable (B s) P := h.isPreBrownian.integrable_eval s
  have h_int_t : Integrable (B t) P := h.isPreBrownian.integrable_eval t
  have h_int_diff : Integrable (fun ω => B t ω - B s ω) P := h_int_t.sub h_int_s
  have h_meas_t : Measurable (B t) :=
    ((h.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (B s) :=
    ((h.stronglyAdapted s).mono (𝓕.le s)).measurable
  have h_meas_diff : Measurable (fun ω => B t ω - B s ω) := h_meas_t.sub h_meas_s
  have h_int_zero : ∫ ω, (B t ω - B s ω) ∂P = 0 := by
    have hL : HasLaw (B t - B s) (gaussianReal 0 (max (t - s) (s - t))) P :=
      h.isPreBrownian.hasLaw_sub t s
    have h_eq : (fun ω => B t ω - B s ω) = (B t - B s) := by funext; rfl
    rw [h_eq, hL.integral_eq, integral_id_gaussianReal]
  -- In v4.30, `condExp_of_stronglyMeasurable` returns plain equality (stronger
  -- than `=ᵐ[P]`).
  have h_condBs : P[B s | (𝓕 s : MeasurableSpace Ω)] = B s :=
    condExp_of_stronglyMeasurable (𝓕.le s) (h.stronglyAdapted s) h_int_s
  have h_diff_meas_comap :
      Measurable[MeasurableSpace.comap (fun ω => B t ω - B s ω) (borel ℝ)]
        (fun ω => B t ω - B s ω) :=
    fun s' hs' => ⟨s', hs', rfl⟩
  have h_diff_smeas_comap :
      StronglyMeasurable[MeasurableSpace.comap (fun ω => B t ω - B s ω) (borel ℝ)]
        (fun ω => B t ω - B s ω) :=
    h_diff_meas_comap.stronglyMeasurable
  have h_le_comap :
      MeasurableSpace.comap (fun ω => B t ω - B s ω) (borel ℝ) ≤ mΩ := by
    rintro s' ⟨t', ht', rfl⟩
    exact h_meas_diff ht'
  have h_condDiff :
      P[fun ω => B t ω - B s ω | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] fun _ => (0 : ℝ) := by
    have := condExp_indep_eq h_le_comap (𝓕.le s) h_diff_smeas_comap
      (h.indep_increment_filt hst)
    rw [h_int_zero] at this
    exact this
  -- B_t =ᵐ[P] B_s + (B_t - B_s) (in fact equal pointwise; use condExp_congr_ae)
  have h_decomp_ae : (B t) =ᵐ[P] B s + (fun ω => B t ω - B s ω) :=
    Filter.Eventually.of_forall (fun ω => by
      simp only [Pi.add_apply]
      ring)
  -- condExp respects ae-equal integrands
  have step1 :
      P[B t | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] P[B s + (fun ω => B t ω - B s ω) | (𝓕 s : MeasurableSpace Ω)] :=
    condExp_congr_ae h_decomp_ae
  -- Linearity: condExp(B_s + (B_t - B_s)) = condExp(B_s) + condExp(B_t - B_s)
  have step2 :
      P[B s + (fun ω => B t ω - B s ω) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] P[B s | (𝓕 s : MeasurableSpace Ω)] +
              P[fun ω => B t ω - B s ω | (𝓕 s : MeasurableSpace Ω)] :=
    condExp_add h_int_s h_int_diff _
  -- B_s + 0 = B_s
  have step3 :
      P[B s | (𝓕 s : MeasurableSpace Ω)] +
        P[fun ω => B t ω - B s ω | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] B s := by
    filter_upwards [h_condDiff] with ω h2
    show _ + _ = B s ω
    rw [h_condBs]
    show B s ω + _ = B s ω
    rw [h2]; ring
  exact step1.trans (step2.trans step3)

/-- **Theorem 5.1.6 (square version)**: for a pre-Brownian motion `B` adapted to
    a filtration `𝓕` with future increments independent of past `𝓕`, the process
    `t ↦ (B t)² − t` is a martingale w.r.t. `𝓕`.

    Derivation:
    - Decompose `(B_t)² = (B_s)² + 2 B_s (B_t − B_s) + (B_t − B_s)²`.
    - `E[(B_s)² | 𝓕_s] = (B_s)²` (𝓕_s-measurable).
    - `E[B_s · (B_t − B_s) | 𝓕_s] = B_s · E[B_t − B_s | 𝓕_s] = B_s · 0 = 0`
      (pull-out + centered Gaussian increment + independence of past).
    - `E[(B_t − B_s)² | 𝓕_s] = E[(B_t − B_s)²] = t − s` (independence + variance
      of `gaussianReal 0 (t − s)`). -/
theorem BrownianMartingaleHyp.square_minus_time_is_martingale
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (h : BrownianMartingaleHyp P 𝓕 B) :
    Martingale (fun t ω => (B t ω) ^ 2 - (t : ℝ)) 𝓕 P := by
  refine ⟨fun u => ?_, fun s t hst => ?_⟩
  -- Adaptedness of `(B u)² − u`
  · have hB : StronglyMeasurable[𝓕 u] (B u) := h.stronglyAdapted u
    have hsq : StronglyMeasurable[𝓕 u] (fun ω => (B u ω) ^ 2) := by
      simpa [pow_two] using hB.mul hB
    exact hsq.sub stronglyMeasurable_const
  -- Conditional-expectation step
  have h_int_s : Integrable (B s) P := h.isPreBrownian.integrable_eval s
  have h_int_t : Integrable (B t) P := h.isPreBrownian.integrable_eval t
  have h_int_diff : Integrable (fun ω => B t ω - B s ω) P := h_int_t.sub h_int_s
  have h_meas_t : Measurable (B t) := ((h.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (B s) := ((h.stronglyAdapted s).mono (𝓕.le s)).measurable
  have h_meas_diff : Measurable (fun ω => B t ω - B s ω) := h_meas_t.sub h_meas_s
  -- Pi-sub form of the increment, used to align syntactic forms with HasLaw API.
  have h_eq_diff : (fun ω => B t ω - B s ω) = (B t - B s : Ω → ℝ) := by funext; rfl
  -- HasLaws (Degenne)
  have hL_diff : HasLaw (B t - B s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    h.isPreBrownian.hasLaw_sub t s
  have hL_s : HasLaw (B s) (gaussianReal 0 s) P := h.isPreBrownian.hasLaw_eval s
  -- L² membership transferred via HasLaw + memLp_id_gaussianReal.
  have h_Bs_memLp : MemLp (B s) 2 P := by
    have h_id : MemLp (id : ℝ → ℝ) 2 (Measure.map (B s) P) := by
      rw [hL_s.map_eq]; exact memLp_id_gaussianReal 2
    exact h_id.comp_of_map h_meas_s.aemeasurable
  have h_diff_memLp : MemLp (fun ω => B t ω - B s ω) 2 P := by
    rw [h_eq_diff]
    have h_id : MemLp (id : ℝ → ℝ) 2 (Measure.map (B t - B s) P) := by
      rw [hL_diff.map_eq]; exact memLp_id_gaussianReal 2
    refine h_id.comp_of_map ?_
    rw [← h_eq_diff]
    exact h_meas_diff.aemeasurable
  -- Integrability of squares and product (Hölder for `1/2 + 1/2 = 1`).
  have h_int_Bs_sq : Integrable (fun ω => (B s ω) ^ 2) P :=
    h_Bs_memLp.integrable_sq
  have h_int_diff_sq : Integrable (fun ω => (B t ω - B s ω) ^ 2) P :=
    h_diff_memLp.integrable_sq
  have h_int_cross : Integrable (fun ω => B s ω * (B t ω - B s ω)) P := by
    have := h_Bs_memLp.integrable_mul h_diff_memLp
    simpa using this
  -- Mean of increment is 0.
  have h_int_diff_zero : ∫ ω, (B t ω - B s ω) ∂P = 0 := by
    rw [h_eq_diff, hL_diff.integral_eq, integral_id_gaussianReal]
  -- Variance of increment integral: ∫ (B_t − B_s)² ∂P = t − s.
  have h_int_diff_sq_zero : ∫ ω, (B t ω - B s ω) ^ 2 ∂P = (t : ℝ) - (s : ℝ) := by
    have h_change : ∫ ω, (B t ω - B s ω) ^ 2 ∂P
        = ∫ x, x ^ 2 ∂(gaussianReal 0 (max (t - s) (s - t))) := by
      have := hL_diff.integral_comp (f := fun x : ℝ => x ^ 2)
        (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
          (gaussianReal 0 (max (t - s) (s - t))))
      simpa [Function.comp] using this
    rw [h_change, integral_sq_gaussianReal]
    exact max_sub_eq_of_le hst
  -- 𝓕_s-measurability of B_s and (B_s)².
  have h_smeas_s : StronglyMeasurable[𝓕 s] (B s) := h.stronglyAdapted s
  have h_smeas_s_sq : StronglyMeasurable[𝓕 s] (fun ω => (B s ω) ^ 2) := by
    simpa [pow_two] using h_smeas_s.mul h_smeas_s
  -- E[(B_s)² | 𝓕_s] = (B_s)².
  have h_condBs_sq :
      P[fun ω => (B s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)] = fun ω => (B s ω) ^ 2 :=
    condExp_of_stronglyMeasurable (𝓕.le s) h_smeas_s_sq h_int_Bs_sq
  -- Independence machinery (comap σ-algebra of the increment is independent of 𝓕_s).
  have h_diff_meas_comap :
      Measurable[MeasurableSpace.comap (fun ω => B t ω - B s ω) (borel ℝ)]
        (fun ω => B t ω - B s ω) :=
    fun s' hs' => ⟨s', hs', rfl⟩
  have h_diff_smeas_comap :
      StronglyMeasurable[MeasurableSpace.comap (fun ω => B t ω - B s ω) (borel ℝ)]
        (fun ω => B t ω - B s ω) :=
    h_diff_meas_comap.stronglyMeasurable
  have h_le_comap :
      MeasurableSpace.comap (fun ω => B t ω - B s ω) (borel ℝ) ≤ mΩ := by
    rintro s' ⟨t', ht', rfl⟩
    exact h_meas_diff ht'
  -- E[B_t − B_s | 𝓕_s] =ᵐ 0.
  have h_condDiff :
      P[fun ω => B t ω - B s ω | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] fun _ => (0 : ℝ) := by
    have := condExp_indep_eq h_le_comap (𝓕.le s) h_diff_smeas_comap
      (h.indep_increment_filt hst)
    rw [h_int_diff_zero] at this
    exact this
  -- E[(B_t − B_s)² | 𝓕_s] =ᵐ (t − s).
  have h_diff_sq_meas_comap :
      Measurable[MeasurableSpace.comap (fun ω => B t ω - B s ω) (borel ℝ)]
        (fun ω => (B t ω - B s ω) ^ 2) :=
    fun s' hs' => ⟨(fun x : ℝ => x ^ 2) ⁻¹' s',
      (continuous_id.pow 2).measurable hs', rfl⟩
  have h_diff_sq_smeas_comap :
      StronglyMeasurable[MeasurableSpace.comap (fun ω => B t ω - B s ω) (borel ℝ)]
        (fun ω => (B t ω - B s ω) ^ 2) :=
    h_diff_sq_meas_comap.stronglyMeasurable
  have h_condDiffSq :
      P[fun ω => (B t ω - B s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] fun _ => ((t : ℝ) - (s : ℝ)) := by
    have := condExp_indep_eq h_le_comap (𝓕.le s) h_diff_sq_smeas_comap
      (h.indep_increment_filt hst)
    rw [h_int_diff_sq_zero] at this
    exact this
  -- Pull-out: E[B_s · (B_t − B_s) | 𝓕_s] =ᵐ B_s · E[(B_t − B_s) | 𝓕_s] =ᵐ 0.
  have h_cross_eq :
      (fun ω => B s ω * (B t ω - B s ω)) = (B s) * (fun ω => B t ω - B s ω) := by
    funext ω; rfl
  have h_pullout :
      P[fun ω => B s ω * (B t ω - B s ω) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] (B s) * (P[fun ω => B t ω - B s ω | (𝓕 s : MeasurableSpace Ω)]) := by
    rw [h_cross_eq]
    exact condExp_mul_of_stronglyMeasurable_left h_smeas_s
      (by simpa [h_cross_eq] using h_int_cross) h_int_diff
  have h_cond_cross :
      P[fun ω => B s ω * (B t ω - B s ω) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] fun _ => (0 : ℝ) := by
    refine h_pullout.trans ?_
    filter_upwards [h_condDiff] with ω hω
    show (B s) ω * (P[fun ω => B t ω - B s ω | (𝓕 s : MeasurableSpace Ω)]) ω
        = (fun _ => (0 : ℝ)) ω
    rw [hω]; simp [Pi.mul_apply]
  -- Decomposition of the integrand.
  have h_decomp_ae :
      (fun ω => (B t ω) ^ 2 - (t : ℝ))
        =ᵐ[P] fun ω =>
          ((B s ω) ^ 2 + 2 * (B s ω * (B t ω - B s ω))) +
            ((B t ω - B s ω) ^ 2 - (t : ℝ)) :=
    Filter.Eventually.of_forall fun ω => by ring
  -- condExp respects ae equality.
  have step1 :
      P[fun ω => (B t ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] P[fun ω =>
          ((B s ω) ^ 2 + 2 * (B s ω * (B t ω - B s ω))) +
            ((B t ω - B s ω) ^ 2 - (t : ℝ)) | (𝓕 s : MeasurableSpace Ω)] :=
    condExp_congr_ae h_decomp_ae
  -- Linearity (outer add).
  have h_int_inner_left :
      Integrable (fun ω => (B s ω) ^ 2 + 2 * (B s ω * (B t ω - B s ω))) P :=
    h_int_Bs_sq.add (h_int_cross.const_mul 2)
  have h_int_inner_right :
      Integrable (fun ω => (B t ω - B s ω) ^ 2 - (t : ℝ)) P :=
    h_int_diff_sq.sub (integrable_const _)
  have step2 :
      P[fun ω =>
          ((B s ω) ^ 2 + 2 * (B s ω * (B t ω - B s ω))) +
            ((B t ω - B s ω) ^ 2 - (t : ℝ)) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (P[fun ω => (B s ω) ^ 2 + 2 * (B s ω * (B t ω - B s ω))
              | (𝓕 s : MeasurableSpace Ω)])
          + (P[fun ω => (B t ω - B s ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]) :=
    condExp_add h_int_inner_left h_int_inner_right _
  -- Inner add (B_s² + 2 · cross). Use `(2 : ℝ) •` explicitly so Lean infers
  -- the ℝ-smul rather than the ℕ-smul (which `condExp_smul` does not produce).
  have h_eq_smul : (fun ω => 2 * (B s ω * (B t ω - B s ω)))
                 = (2 : ℝ) • (fun ω => B s ω * (B t ω - B s ω)) := by
    funext ω; simp [Pi.smul_apply, smul_eq_mul]
  have h_int_2cross : Integrable (fun ω => 2 * (B s ω * (B t ω - B s ω))) P :=
    h_int_cross.const_mul 2
  have step3a :
      P[fun ω => (B s ω) ^ 2 + 2 * (B s ω * (B t ω - B s ω))
          | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (P[fun ω => (B s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)])
            + (P[fun ω => 2 * (B s ω * (B t ω - B s ω)) | (𝓕 s : MeasurableSpace Ω)]) :=
    condExp_add h_int_Bs_sq h_int_2cross _
  have step3b :
      P[fun ω => 2 * (B s ω * (B t ω - B s ω)) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] (2 : ℝ) • P[fun ω => B s ω * (B t ω - B s ω) | (𝓕 s : MeasurableSpace Ω)] := by
    rw [h_eq_smul]; exact condExp_smul (2 : ℝ) _ _
  rw [h_condBs_sq] at step3a
  have step3 :
      P[fun ω => (B s ω) ^ 2 + 2 * (B s ω * (B t ω - B s ω))
          | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (fun ω => (B s ω) ^ 2)
            + (2 : ℝ) • (P[fun ω => B s ω * (B t ω - B s ω) | (𝓕 s : MeasurableSpace Ω)]) := by
    filter_upwards [step3a, step3b] with ω h3a h3b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h3a h3b ⊢
    linarith
  -- Inner sub on the right.
  have step4 :
      P[fun ω => (B t ω - B s ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (P[fun ω => (B t ω - B s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)])
            - (fun _ => (t : ℝ)) := by
    have h_const_int : Integrable (fun _ : Ω => (t : ℝ)) P := integrable_const _
    have step4a :
        P[fun ω => (B t ω - B s ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]
          =ᵐ[P]
            (P[fun ω => (B t ω - B s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)])
              - P[fun _ : Ω => (t : ℝ) | (𝓕 s : MeasurableSpace Ω)] :=
      condExp_sub h_int_diff_sq h_const_int _
    have step4b :
        P[fun _ : Ω => (t : ℝ) | (𝓕 s : MeasurableSpace Ω)] = fun _ => (t : ℝ) :=
      condExp_const (𝓕.le s) (t : ℝ)
    filter_upwards [step4a] with ω h4a
    show _ = _
    rw [h4a, step4b]
  -- Combine all steps and simplify to (B_s)² − s via linear_combination.
  filter_upwards [step1, step2, step3, step4, h_cond_cross, h_condDiffSq]
    with ω hs1 hs2 hs3 hs4 hcross hdiffsq
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] at hs2 hs3 hs4
  show (P[fun ω => (B t ω) ^ 2 - (t : ℝ) | (𝓕 s : MeasurableSpace Ω)]) ω
      = (B s ω) ^ 2 - (s : ℝ)
  linear_combination hs1 + hs2 + hs3 + hs4 + 2 * hcross + hdiffsq

end HybridVerify
