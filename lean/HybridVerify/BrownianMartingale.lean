/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import BrownianMotion.Gaussian.BrownianMotion

/-!
# Martingale properties of Brownian motion

For a filtered pre-Brownian motion `X`, the following are martingales with
respect to the filtration `𝓕`:

* `X` itself (already provided as `IsPreBrownian.isMartingale` in `Gaussian/BrownianMotion.lean`)
* `t ↦ (X t)² − t`
* `t ↦ exp(α X_t − α² t / 2)` (Wald exponential), for any `α : ℝ`

## Main results

* `IsFilteredPreBrownian.squareSubTime_isMartingale`
* `IsFilteredPreBrownian.waldExponential_isMartingale`
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- For `s ≤ t : ℝ≥0`, the NNReal-valued increment-variance `max (t-s) (s-t)`
coerces to `(t : ℝ) - (s : ℝ)` (since truncated `s - t = 0` when `s ≤ t`). -/
private lemma NNReal.max_sub_eq_of_le {s t : ℝ≥0} (hst : s ≤ t) :
    ((max (t - s) (s - t) : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) := by
  have hst_zero : s - t = (0 : ℝ≥0) := tsub_eq_zero_of_le hst
  rw [hst_zero, max_eq_left (zero_le _)]
  exact NNReal.coe_sub hst

/-- MGF specialization: for `α : ℝ` and `v : ℝ≥0`,
`∫ x, exp(α x) ∂(gaussianReal 0 v) = exp(α² v / 2)`. -/
private lemma integral_exp_mul_gaussianReal_zero (α : ℝ) (v : ℝ≥0) :
    ∫ x, Real.exp (α * x) ∂(gaussianReal 0 v) = Real.exp (α ^ 2 * (v : ℝ) / 2) := by
  have h := congr_fun (mgf_id_gaussianReal (μ := 0) (v := v)) α
  show mgf id (gaussianReal 0 v) α = _
  rw [h]
  ring_nf

/-- Second moment of a centered real Gaussian: `∫ x, x² ∂(gaussianReal 0 v) = v`. -/
private lemma integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h_var : variance id (gaussianReal 0 v) = (v : ℝ) := variance_id_gaussianReal
  have h_mean : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  rw [variance_of_integral_eq_zero aemeasurable_id h_mean] at h_var
  exact h_var

/-- `exp (α · Z)` is integrable when `Z` has a Gaussian law. -/
private lemma integrable_exp_mul_of_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {Z : Ω → ℝ} (hZ_meas : Measurable Z)
    {m : ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal m v) P) (α : ℝ) :
    Integrable (fun ω ↦ Real.exp (α * Z ω)) P := by
  rw [show (fun ω ↦ Real.exp (α * Z ω)) = (fun x ↦ Real.exp (α * x)) ∘ Z from rfl]
  refine Integrable.comp_aemeasurable ?_ hZ_meas.aemeasurable
  rw [hZ.map_eq]
  exact integrable_exp_mul_gaussianReal α

namespace IsFilteredPreBrownian

variable [hX : IsFilteredPreBrownian X 𝓕 P] [IsFiniteMeasure P]

/-- Evaluation of a filtered pre-Brownian motion is measurable in the ambient
measurable space. -/
private lemma measurable_eval (t : ℝ≥0) : Measurable (X t) :=
  ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable

/-- The increment `X_t - X_s` is measurable. -/
private lemma measurable_increment (s t : ℝ≥0) :
    Measurable (fun ω ↦ X t ω - X s ω) :=
  (measurable_eval (hX := hX) t).sub (measurable_eval (hX := hX) s)

/-- Distribution of the increment `X_t - X_s`. -/
private lemma hasLaw_increment (s t : ℝ≥0) :
    HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
  hX.hasLaw_sub t s

/-- Evaluation of a filtered pre-Brownian motion belongs to `L²`. -/
private lemma memLp_eval_two (t : ℝ≥0) : MemLp (X t) 2 P :=
  (((hX.hasLaw_eval t).map_eq ▸ memLp_id_gaussianReal 2 :
    MemLp (id : ℝ → ℝ) 2 (Measure.map (X t) P))).comp_of_map
      (measurable_eval (hX := hX) t).aemeasurable

/-- Increments of a filtered pre-Brownian motion belong to `L²`. -/
private lemma memLp_increment_two (s t : ℝ≥0) :
    MemLp (fun ω ↦ X t ω - X s ω) 2 P := by
  change MemLp (X t - X s : Ω → ℝ) 2 P
  exact (((hasLaw_increment (hX := hX) s t).map_eq ▸ memLp_id_gaussianReal 2 :
    MemLp (id : ℝ → ℝ) 2 (Measure.map (X t - X s) P))).comp_of_map
      (measurable_increment (hX := hX) s t).aemeasurable

/-- Centered increment identity. -/
private lemma integral_increment_eq_zero (s t : ℝ≥0) :
    ∫ ω, (X t ω - X s ω) ∂P = 0 := by
  rw [show (fun ω ↦ X t ω - X s ω) = (X t - X s : Ω → ℝ) from rfl,
      (hasLaw_increment (hX := hX) s t).integral_eq, integral_id_gaussianReal]

/-- Second moment of an ordered Brownian increment. -/
private lemma integral_increment_sq_eq_sub {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, (X t ω - X s ω) ^ 2 ∂P = (t : ℝ) - (s : ℝ) := by
  have h_change : ∫ ω, (X t ω - X s ω) ^ 2 ∂P
      = ∫ x, x ^ 2 ∂(gaussianReal 0 (max (t - s) (s - t))) := by
    simpa [Function.comp] using
      (hasLaw_increment (hX := hX) s t).integral_comp
        (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  rw [h_change, integral_sq_gaussianReal]
  exact NNReal.max_sub_eq_of_le hst

/-- Conditional expectation of a Borel function of an ordered increment is
constant. -/
private lemma condExp_func_increment {s t : ℝ≥0} (hst : s ≤ t)
    (h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω))
    {φ : ℝ → ℝ} (hφ : Measurable φ) {c : ℝ}
    (h_int_eq : ∫ ω, φ (X t ω - X s ω) ∂P = c) :
    P[fun ω ↦ φ (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ c := by
  have h_indep : Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)) (𝓕 s) P :=
    hX.indep s t hst
  have hφ_comap :
      Measurable[MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) (borel ℝ)]
        (fun ω ↦ φ (X t ω - X s ω)) :=
    hφ.comp (Measurable.of_comap_le le_rfl)
  have := condExp_indep_eq h_meas_diff.comap_le (𝓕.le s)
    hφ_comap.stronglyMeasurable h_indep
  rwa [h_int_eq] at this

/-- Conditional expectation of an ordered Brownian increment is zero. -/
private lemma condExp_increment_eq_zero {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ X t ω - X s ω | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (0 : ℝ) :=
  condExp_func_increment hst (measurable_increment (hX := hX) s t) measurable_id
    (integral_increment_eq_zero (hX := hX) s t)

/-- Conditional second moment of an ordered Brownian increment. -/
private lemma condExp_increment_sq_eq_sub {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P]
      fun _ ↦ ((t : ℝ) - (s : ℝ)) :=
  condExp_func_increment hst (measurable_increment (hX := hX) s t)
    (measurable_id.pow_const 2) (integral_increment_sq_eq_sub (hX := hX) hst)

/-- The residual term in the martingale proof for `X_t² - t` has conditional
expectation zero. -/
private lemma condExp_squareSubTime_residual {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ 2 * (X s ω * (X t ω - X s ω))
              + ((X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ)))
        | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (0 : ℝ) := by
  have h_Bs_memLp : MemLp (X s) 2 P := memLp_eval_two (hX := hX) s
  have h_diff_memLp : MemLp (fun ω ↦ X t ω - X s ω) 2 P :=
    memLp_increment_two (hX := hX) s t
  have h_int_cross : Integrable (fun ω ↦ X s ω * (X t ω - X s ω)) P :=
    h_Bs_memLp.integrable_mul h_diff_memLp
  have h_int_2cross : Integrable (fun ω ↦ 2 * (X s ω * (X t ω - X s ω))) P :=
    h_int_cross.const_mul 2
  have h_int_diff_sq : Integrable (fun ω ↦ (X t ω - X s ω) ^ 2) P := h_diff_memLp.integrable_sq
  have h_int_diff_sq_sub :
      Integrable (fun ω ↦ (X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ))) P :=
    h_int_diff_sq.sub (integrable_const _)
  have h_int_diff : Integrable (fun ω ↦ X t ω - X s ω) P :=
    (hX.integrable_eval t).sub (hX.integrable_eval s)
  have h_ce_increment :
      P[fun ω ↦ X t ω - X s ω | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (0 : ℝ) :=
    condExp_increment_eq_zero (hX := hX) hst
  have h_smeas_s : StronglyMeasurable[𝓕 s] (X s) := hX.stronglyAdapted s
  have h_ce_cross :
      P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    refine (condExp_mul_of_stronglyMeasurable_left h_smeas_s h_int_cross h_int_diff).trans ?_
    filter_upwards [h_ce_increment] with ω hω
    show (X s) ω * _ = 0
    rw [hω]
    simp
  have h_ce_diff_sq :
      P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P]
        fun _ ↦ ((t : ℝ) - (s : ℝ)) :=
    condExp_increment_sq_eq_sub (hX := hX) hst
  have h_ce_diff_sq_sub :
      P[fun ω ↦ (X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ)) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    refine (condExp_sub h_int_diff_sq (integrable_const _) _).trans ?_
    filter_upwards [h_ce_diff_sq] with ω h
    show P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)] ω
          - P[fun _ : Ω ↦ ((t : ℝ) - (s : ℝ)) | (𝓕 s : MeasurableSpace Ω)] ω = 0
    rw [h, condExp_const (𝓕.le s)]
    simp
  refine (condExp_add h_int_2cross h_int_diff_sq_sub _).trans ?_
  have h_eq_smul : (fun ω ↦ 2 * (X s ω * (X t ω - X s ω)))
                 = (2 : ℝ) • (fun ω ↦ X s ω * (X t ω - X s ω)) := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
  have h_smul :
      P[fun ω ↦ 2 * (X s ω * (X t ω - X s ω)) | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P]
        (2 : ℝ) • P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)] := by
    rw [h_eq_smul]
    exact condExp_smul (2 : ℝ) _ _
  filter_upwards [h_smul, h_ce_cross, h_ce_diff_sq_sub] with ω hsm hcr hds
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  linarith

/-- For a filtered pre-Brownian motion `X`, `t ↦ (X t)² - t` is a martingale
with respect to `𝓕`. -/
theorem squareSubTime_isMartingale :
    Martingale (fun t ω ↦ (X t ω) ^ 2 - (t : ℝ)) 𝓕 P := by
  refine ⟨fun u ↦ ?_, fun s t hst ↦ ?_⟩
  -- Adaptedness.
  · have hB : StronglyMeasurable[𝓕 u] (X u) := hX.stronglyAdapted u
    have hsq : StronglyMeasurable[𝓕 u] (fun ω ↦ (X u ω) ^ 2) := by
      simpa [pow_two] using hB.mul hB
    exact hsq.sub stronglyMeasurable_const
  have h_Bs_memLp : MemLp (X s) 2 P := memLp_eval_two (hX := hX) s
  have h_diff_memLp : MemLp (fun ω ↦ X t ω - X s ω) 2 P :=
    memLp_increment_two (hX := hX) s t
  have h_smeas_s : StronglyMeasurable[𝓕 s] (X s) := hX.stronglyAdapted s
  have h_smeas_Bs_sq_sub : StronglyMeasurable[𝓕 s] (fun ω ↦ (X s ω) ^ 2 - (s : ℝ)) := by
    have hsq : StronglyMeasurable[𝓕 s] (fun ω ↦ (X s ω) ^ 2) := by
      simpa [pow_two] using h_smeas_s.mul h_smeas_s
    exact hsq.sub stronglyMeasurable_const
  have h_int_Bs_sq_sub : Integrable (fun ω ↦ (X s ω) ^ 2 - (s : ℝ)) P :=
    h_Bs_memLp.integrable_sq.sub (integrable_const _)
  have h_condBs_sq_sub :
      P[fun ω ↦ (X s ω) ^ 2 - (s : ℝ) | (𝓕 s : MeasurableSpace Ω)]
        = fun ω ↦ (X s ω) ^ 2 - (s : ℝ) :=
    condExp_of_stronglyMeasurable (𝓕.le s) h_smeas_Bs_sq_sub h_int_Bs_sq_sub
  have h_int_residual : Integrable (fun ω ↦
      2 * (X s ω * (X t ω - X s ω)) + ((X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ)))) P :=
    ((h_Bs_memLp.integrable_mul h_diff_memLp).const_mul 2).add
      (h_diff_memLp.integrable_sq.sub (integrable_const _))
  have h_decomp_ae :
      (fun ω ↦ (X t ω) ^ 2 - (t : ℝ)) =ᵐ[P] fun ω ↦
        ((X s ω) ^ 2 - (s : ℝ)) +
          (2 * (X s ω * (X t ω - X s ω))
            + ((X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ)))) :=
    Filter.Eventually.of_forall fun ω ↦ by ring
  refine (condExp_congr_ae h_decomp_ae).trans ?_
  refine (condExp_add h_int_Bs_sq_sub h_int_residual _).trans ?_
  filter_upwards [condExp_squareSubTime_residual (hX := hX) hst] with ω hω
  show P[fun ω ↦ (X s ω) ^ 2 - (s : ℝ) | (𝓕 s : MeasurableSpace Ω)] ω + _ = _
  rw [h_condBs_sq_sub, hω]
  simp

/-- For a filtered pre-Brownian motion `X` and `α : ℝ`,
`t ↦ exp(α X_t - α² t / 2)` is a martingale with respect to `𝓕`. -/
theorem waldExponential_isMartingale (α : ℝ) :
    Martingale (fun t ω ↦ Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2)) 𝓕 P := by
  refine ⟨fun u ↦ ?_, fun s t hst ↦ ?_⟩
  -- Adaptedness.
  · refine Real.continuous_exp.comp_stronglyMeasurable ?_
    exact ((hX.stronglyAdapted u).const_mul α).sub stronglyMeasurable_const
  -- Conditional-expectation step.
  have h_meas_t : Measurable (X t) := measurable_eval (hX := hX) t
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω) :=
    measurable_increment (hX := hX) s t
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hasLaw_increment (hX := hX) s t
  have h_int_exp_diff : Integrable (fun ω ↦ Real.exp (α * (X t ω - X s ω))) P :=
    integrable_exp_mul_of_hasLaw h_meas_diff hL_diff α
  set Ms : Ω → ℝ := fun ω ↦ Real.exp (α * X s ω - α ^ 2 * (s : ℝ) / 2)
  set Dst : Ω → ℝ := fun ω ↦
    Real.exp (α * (X t ω - X s ω) - α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2)
  have hMs_meas : StronglyMeasurable[𝓕 s] Ms :=
    Real.continuous_exp.comp_stronglyMeasurable
      (((hX.stronglyAdapted s).const_mul α).sub stronglyMeasurable_const)
  have h_decomp : ∀ ω, Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2) = Ms ω * Dst ω := by
    intro ω
    show _ = Real.exp _ * Real.exp _
    rw [← Real.exp_add]
    congr 1
    ring
  have hDst_factor : Dst = fun ω ↦ Real.exp (-(α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2))
                              * Real.exp (α * (X t ω - X s ω)) := by
    funext ω
    show Real.exp _ = _
    rw [← Real.exp_add]
    congr 1
    ring
  have h_int_Dst : Integrable Dst P := by
    rw [hDst_factor]
    exact h_int_exp_diff.const_mul _
  -- Mean of `D_{st}` is 1.
  have h_int_Dst_eq_one : ∫ ω, Dst ω ∂P = 1 := by
    have h_mgf : ∫ ω, Real.exp (α * (X t ω - X s ω)) ∂P
        = Real.exp (α ^ 2 * ((max (t - s) (s - t) : ℝ≥0) : ℝ) / 2) := by
      have h := hL_diff.integral_comp
        (f := fun x : ℝ ↦ Real.exp (α * x)) (by fun_prop)
      simpa [integral_exp_mul_gaussianReal_zero] using h
    rw [hDst_factor, integral_const_mul, h_mgf, NNReal.max_sub_eq_of_le hst,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  -- `E[D_{st} | 𝓕_s] =ᵐ 1` (the increment is independent of `𝓕 s`).
  have h_condDst : P[Dst | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (1 : ℝ) :=
    condExp_func_increment hst h_meas_diff
      (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).sub continuous_const)).measurable
      h_int_Dst_eq_one
  have h_int_MsDst : Integrable (fun ω ↦ Ms ω * Dst ω) P := by
    rw [← funext h_decomp]
    have h_eq : (fun ω ↦ Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2))
              = fun ω ↦ Real.exp (-(α ^ 2 * (t : ℝ) / 2)) * Real.exp (α * X t ω) := by
      funext ω
      show Real.exp _ = _
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h_eq]
    exact (integrable_exp_mul_of_hasLaw h_meas_t (hX.hasLaw_eval t) α).const_mul _
  refine (condExp_congr_ae (Filter.Eventually.of_forall h_decomp)).trans ?_
  refine (condExp_mul_of_stronglyMeasurable_left hMs_meas h_int_MsDst h_int_Dst).trans ?_
  filter_upwards [h_condDst] with ω hω
  show (Ms * P[Dst | (𝓕 s : MeasurableSpace Ω)]) ω = Ms ω
  simp only [Pi.mul_apply, hω, mul_one]

end IsFilteredPreBrownian

end ProbabilityTheory

/-! ## Hitting time of an open set is a stopping time

For a continuous adapted process `X` and an open set `A`, the hitting time
`τ_A = inf {t ≥ 0 : X_t ∈ A}` is a stopping time with respect to any right-continuous
filtration. The proof reduces `{ω | τ ω < i}` to a countable union of
`{ω | X_q ω ∈ A}` for nonnegative rationals `q < i` (continuity of `X(·, ω)`
upgrades any real witness to a rational witness via `Real.exists_rat_btwn`),
then applies `isStoppingTime_of_measurableSet_lt_of_isRightContinuous`.

The result is generic — applies to any adapted continuous process — but lives
here because the canonical application is to Brownian motion paths.
Corresponds to Saporito Proposition 4.3.6. -/

namespace HybridVerify

open MeasureTheory ProbabilityTheory

variable {Ω β : Type*} {mΩ : MeasurableSpace Ω}

/-- Key set identity: for continuous adapted `X` and open `A`, the set
`{ω | hittingAfter X A 0 ω < i}` equals the countable union over nonnegative
rationals `q < i` of `{ω | X (q : ℝ) ω ∈ A}`. -/
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
    have h_pre : (fun t : ℝ => X t ω) ⁻¹' A ∈ nhds j :=
      ((hX_cont ω).continuousAt).preimage_mem_nhds (hA_open.mem_nhds hXj)
    rcases lt_or_eq_of_le hj_nn with hj_pos | hj_zero
    · obtain ⟨δ, hδ_pos, hδ_sub⟩ : ∃ δ > 0,
          Set.Ioo (j - δ) (j + δ) ⊆ (fun t : ℝ => X t ω) ⁻¹' A := by
        have h_nhds := Metric.mem_nhds_iff.mp h_pre
        obtain ⟨ε, hε_pos, hε_sub⟩ := h_nhds
        refine ⟨ε, hε_pos, fun s hs => ?_⟩
        refine hε_sub ?_
        simp only [Metric.mem_ball, Real.dist_eq, Set.mem_Ioo] at hs ⊢
        cases hs with | intro h1 h2 => exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
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
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show j - δ' < j + δ' by linarith)
      refine ⟨q, ?_, ?_, h_sub_pre ⟨hq1, hq2⟩⟩
      · linarith [hδ'_lt_j]
      · linarith [hδ'_lt_i_sub_j]
    · refine ⟨0, ?_, ?_, ?_⟩
      · simp
      · push_cast
        linarith
      · push_cast
        rw [show (0 : ℝ) = j from hj_zero]
        exact hXj
  · rintro ⟨q, hq_nn, hq_lt, hXq⟩
    exact ⟨(q : ℝ), ⟨hq_nn, hq_lt⟩, hXq⟩

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
  exact 𝓕.mono hq_lt.le _ (hX_adapted (q : ℝ) hA_open.measurableSet)

/-- For a continuous adapted process `X` and an open set `A`, the hitting time
`hittingAfter X A 0` is a stopping time with respect to any right-continuous
filtration. -/
theorem isStoppingTime_hittingAfter_of_open
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {𝓕 : Filtration ℝ mΩ} [𝓕.IsRightContinuous]
    {X : ℝ → Ω → β} {A : Set β}
    (hX_cont : ∀ ω, Continuous (fun t => X t ω)) (hX_adapted : Adapted 𝓕 X)
    (hA_open : IsOpen A) :
    IsStoppingTime 𝓕 (hittingAfter X A 0) :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun i =>
    measurableSet_hittingAfter_lt_of_open hX_cont hX_adapted hA_open i

end HybridVerify
