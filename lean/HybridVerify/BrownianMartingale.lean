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

end HybridVerify
