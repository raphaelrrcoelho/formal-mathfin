/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import BrownianMotion.Auxiliary.HasLaw
public import BrownianMotion.Auxiliary.Martingale
public import BrownianMotion.Gaussian.BrownianMotion

/-!
# Martingale properties of pre-Brownian motion

For a filtered pre-Brownian motion `X`, the following are martingales w.r.t. the filtration `𝓕`:

* `X` itself (already provided as `IsPreBrownian.isMartingale` in `Gaussian/BrownianMotion.lean`)
* `t ↦ (X t)² − t`
* `t ↦ exp(α X_t − α² t / 2)` (Wald exponential), for any `α : ℝ`

## Main results

* `IsFilteredPreBrownian.squareSubTime_isMartingale`
* `IsFilteredPreBrownian.waldExponential_isMartingale`

## Proof structure

The conditional-expectation step of `squareSubTime_isMartingale` rests on three
private conditional-expectation identities, each derived from
`condExp_func_increment` (the "increment is independent of the past, so functions
of it have constant conditional expectation" pattern):

* `condExp_increment_zero`: `E[X_t − X_s | 𝓕_s] =ᵐ 0`
* `condExp_increment_sq`:   `E[(X_t − X_s)² | 𝓕_s] =ᵐ t − s`
* `condExp_cross_zero`:     `E[X_s · (X_t − X_s) | 𝓕_s] =ᵐ 0`

The main proof then applies these to the algebraic decomposition
`X_t² − t = (X_s² − s) + 2 X_s (X_t − X_s) + ((X_t − X_s)² − (t − s))`.
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

/-- `Real.exp (α · X) ∘ Z` is integrable when `Z` has a Gaussian law.
Shared helper for `waldExponential_isMartingale` (used 3× there). -/
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

/-- For a Borel-measurable `φ : ℝ → ℝ` with `∫ φ (X_t ω − X_s ω) ∂P = c`, the
conditional expectation of `φ ∘ (X_t − X_s)` given `𝓕 s` is a.e. the constant
`c`. Captures the "increment is independent of the past, so functions of it
behave like deterministic constants under conditional expectation" pattern. -/
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

/-- Increment `X_t − X_s` is centered: `E[X_t − X_s | 𝓕_s] =ᵐ 0`.

Follows from `condExp_func_increment` with `φ = id` (the centered Gaussian increment
integrates to zero). -/
private lemma condExp_increment_zero {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ X t ω - X s ω | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (0 : ℝ) := by
  have h_meas_t : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (X s) := ((hX.stronglyAdapted s).mono (𝓕.le s)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω) := h_meas_t.sub h_meas_s
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hX.hasLaw_sub t s
  have h_int_zero : ∫ ω, (X t ω - X s ω) ∂P = 0 := by
    rw [show (fun ω ↦ X t ω - X s ω) = (X t - X s : Ω → ℝ) from rfl,
        hL_diff.integral_eq, integral_id_gaussianReal]
  exact condExp_func_increment hst h_meas_diff measurable_id h_int_zero

/-- Conditional second moment of the increment equals the time difference:
`E[(X_t − X_s)² | 𝓕_s] =ᵐ t − s`.

Follows from `condExp_func_increment` with `φ = (·)²` (the variance of the centered
Gaussian increment is `t − s`). -/
private lemma condExp_increment_sq {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P]
      fun _ ↦ ((t : ℝ) - (s : ℝ)) := by
  have h_meas_t : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (X s) := ((hX.stronglyAdapted s).mono (𝓕.le s)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω) := h_meas_t.sub h_meas_s
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hX.hasLaw_sub t s
  have h_int_sq : ∫ ω, (X t ω - X s ω) ^ 2 ∂P = (t : ℝ) - (s : ℝ) := by
    have h_change : ∫ ω, (X t ω - X s ω) ^ 2 ∂P
        = ∫ x, x ^ 2 ∂(gaussianReal 0 (max (t - s) (s - t))) := by
      simpa [Function.comp] using hL_diff.integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    rw [h_change, integral_sq_gaussianReal]
    exact NNReal.max_sub_eq_of_le hst
  exact condExp_func_increment hst h_meas_diff (measurable_id.pow_const 2) h_int_sq

/-- Conditional expectation of the cross term `X_s · (X_t − X_s)` given `𝓕_s` is zero.

Combines pull-out (`X_s` is `𝓕_s`-measurable) with `condExp_increment_zero`. -/
private lemma condExp_cross_zero {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P]
      fun _ ↦ (0 : ℝ) := by
  -- Measurabilities, HasLaws, integrabilities.
  have h_meas_t : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (X s) := ((hX.stronglyAdapted s).mono (𝓕.le s)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω) := h_meas_t.sub h_meas_s
  have hL_s : HasLaw (X s) (gaussianReal 0 s) P := hX.hasLaw_eval s
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hX.hasLaw_sub t s
  have h_int_diff : Integrable (fun ω ↦ X t ω - X s ω) P :=
    (hX.integrable_eval t).sub (hX.integrable_eval s)
  -- L² for both factors so the cross term is integrable.
  have h_Bs_memLp : MemLp (X s) 2 P :=
    ((hL_s.map_eq ▸ memLp_id_gaussianReal 2 :
      MemLp (id : ℝ → ℝ) 2 (Measure.map (X s) P))).comp_of_map h_meas_s.aemeasurable
  have h_diff_memLp : MemLp (fun ω ↦ X t ω - X s ω) 2 P :=
    ((hL_diff.map_eq ▸ memLp_id_gaussianReal 2 :
      MemLp (id : ℝ → ℝ) 2 (Measure.map (X t - X s) P))).comp_of_map h_meas_diff.aemeasurable
  have h_int_cross : Integrable (fun ω ↦ X s ω * (X t ω - X s ω)) P :=
    h_Bs_memLp.integrable_mul h_diff_memLp
  -- Pull-out: E[X_s · diff | 𝓕_s] =ᵐ X_s · E[diff | 𝓕_s] =ᵐ X_s · 0 = 0.
  have h_smeas_s : StronglyMeasurable[𝓕 s] (X s) := hX.stronglyAdapted s
  have h_pullout :
      P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] (X s) * (P[fun ω ↦ X t ω - X s ω | (𝓕 s : MeasurableSpace Ω)]) :=
    condExp_mul_of_stronglyMeasurable_left h_smeas_s h_int_cross h_int_diff
  refine h_pullout.trans ?_
  filter_upwards [condExp_increment_zero (hX := hX) hst] with ω hω
  show (X s) ω * (P[fun ω ↦ X t ω - X s ω | (𝓕 s : MeasurableSpace Ω)]) ω = (0 : ℝ)
  rw [hω]; simp

/-- For a filtered pre-Brownian motion `X`, the process `t ↦ (X t)² − t` is a martingale
w.r.t. `𝓕`.

Decomposition: `X_t² − t = (X_s² − s) + 2 X_s (X_t − X_s) + ((X_t − X_s)² − (t − s))`.
The three private lemmas `condExp_increment_sq`, `condExp_cross_zero` handle the
non-`𝓕_s`-measurable summands; `(X_s)² − s` survives conditioning by adaptedness. -/
theorem squareSubTime_isMartingale :
    Martingale (fun t ω ↦ (X t ω) ^ 2 - (t : ℝ)) 𝓕 P := by
  refine ⟨fun u ↦ ?_, fun s t hst ↦ ?_⟩
  -- Adaptedness of `(X u)² − u`.
  · have hB : StronglyMeasurable[𝓕 u] (X u) := hX.stronglyAdapted u
    have hsq : StronglyMeasurable[𝓕 u] (fun ω ↦ (X u ω) ^ 2) := by
      simpa [pow_two] using hB.mul hB
    exact hsq.sub stronglyMeasurable_const
  -- Conditional-expectation step.
  -- Setup integrabilities (needed for `condExp_add`).
  have h_meas_t : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (X s) := ((hX.stronglyAdapted s).mono (𝓕.le s)).measurable
  have hL_s : HasLaw (X s) (gaussianReal 0 s) P := hX.hasLaw_eval s
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hX.hasLaw_sub t s
  have h_Bs_memLp : MemLp (X s) 2 P :=
    ((hL_s.map_eq ▸ memLp_id_gaussianReal 2 :
      MemLp (id : ℝ → ℝ) 2 (Measure.map (X s) P))).comp_of_map h_meas_s.aemeasurable
  have h_diff_memLp : MemLp (fun ω ↦ X t ω - X s ω) 2 P :=
    ((hL_diff.map_eq ▸ memLp_id_gaussianReal 2 :
      MemLp (id : ℝ → ℝ) 2 (Measure.map (X t - X s) P))).comp_of_map
      (h_meas_t.sub h_meas_s).aemeasurable
  have h_int_Bs_sq : Integrable (fun ω ↦ (X s ω) ^ 2) P := h_Bs_memLp.integrable_sq
  have h_int_diff_sq : Integrable (fun ω ↦ (X t ω - X s ω) ^ 2) P := h_diff_memLp.integrable_sq
  have h_int_cross : Integrable (fun ω ↦ X s ω * (X t ω - X s ω)) P :=
    h_Bs_memLp.integrable_mul h_diff_memLp
  have h_int_Bs_sq_sub : Integrable (fun ω ↦ (X s ω) ^ 2 - (s : ℝ)) P :=
    h_int_Bs_sq.sub (integrable_const _)
  have h_int_2cross : Integrable (fun ω ↦ 2 * (X s ω * (X t ω - X s ω))) P :=
    h_int_cross.const_mul 2
  have h_int_diff_sq_sub : Integrable
      (fun ω ↦ (X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ))) P :=
    h_int_diff_sq.sub (integrable_const _)
  -- `(X_s)² − s` is `𝓕_s`-measurable, so its conditional expectation is itself.
  have h_smeas_s : StronglyMeasurable[𝓕 s] (X s) := hX.stronglyAdapted s
  have h_smeas_Bs_sq_sub : StronglyMeasurable[𝓕 s] (fun ω ↦ (X s ω) ^ 2 - (s : ℝ)) := by
    have hsq : StronglyMeasurable[𝓕 s] (fun ω ↦ (X s ω) ^ 2) := by
      simpa [pow_two] using h_smeas_s.mul h_smeas_s
    exact hsq.sub stronglyMeasurable_const
  have h_condBs_sq_sub :
      P[fun ω ↦ (X s ω) ^ 2 - (s : ℝ) | (𝓕 s : MeasurableSpace Ω)]
        = fun ω ↦ (X s ω) ^ 2 - (s : ℝ) :=
    condExp_of_stronglyMeasurable (𝓕.le s) h_smeas_Bs_sq_sub h_int_Bs_sq_sub
  -- AE decomposition of the integrand.
  have h_decomp_ae :
      (fun ω ↦ (X t ω) ^ 2 - (t : ℝ)) =ᵐ[P] fun ω ↦
        ((X s ω) ^ 2 - (s : ℝ)) +
          (2 * (X s ω * (X t ω - X s ω))) +
          ((X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ))) :=
    Filter.Eventually.of_forall fun ω ↦ by ring
  -- Outer linearity: split the three-summand sum into pieces.
  refine (condExp_congr_ae h_decomp_ae).trans ?_
  have step_outer :
      P[fun ω ↦ ((X s ω) ^ 2 - (s : ℝ)) + (2 * (X s ω * (X t ω - X s ω))) +
          ((X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ))) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (P[fun ω ↦ ((X s ω) ^ 2 - (s : ℝ)) + (2 * (X s ω * (X t ω - X s ω)))
              | (𝓕 s : MeasurableSpace Ω)])
          + (P[fun ω ↦ (X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ))
              | (𝓕 s : MeasurableSpace Ω)]) :=
    condExp_add (h_int_Bs_sq_sub.add h_int_2cross) h_int_diff_sq_sub _
  have step_inner :
      P[fun ω ↦ ((X s ω) ^ 2 - (s : ℝ)) + (2 * (X s ω * (X t ω - X s ω)))
          | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P]
          (fun ω ↦ (X s ω) ^ 2 - (s : ℝ)) +
            (P[fun ω ↦ 2 * (X s ω * (X t ω - X s ω)) | (𝓕 s : MeasurableSpace Ω)]) := by
    refine (condExp_add h_int_Bs_sq_sub h_int_2cross _).trans ?_
    rw [h_condBs_sq_sub]
  -- `condExp_smul` for the `2 ·` factor.
  have h_eq_smul : (fun ω ↦ 2 * (X s ω * (X t ω - X s ω)))
                 = (2 : ℝ) • (fun ω ↦ X s ω * (X t ω - X s ω)) := by
    funext ω; simp only [Pi.smul_apply, smul_eq_mul]
  have step_smul :
      P[fun ω ↦ 2 * (X s ω * (X t ω - X s ω)) | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] (2 : ℝ) • P[fun ω ↦ X s ω * (X t ω - X s ω) | (𝓕 s : MeasurableSpace Ω)] := by
    rw [h_eq_smul]; exact condExp_smul (2 : ℝ) _ _
  -- Bridge from `condExp_increment_sq` to the centered residual:
  -- `E[(X_t − X_s)² − (t − s) | 𝓕_s] =ᵐ 0`.
  have step_diff_sq_residual :
      P[fun ω ↦ (X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ)) | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P]
        fun _ ↦ (0 : ℝ) := by
    have h_sub :
        P[fun ω ↦ (X t ω - X s ω) ^ 2 - ((t : ℝ) - (s : ℝ)) | (𝓕 s : MeasurableSpace Ω)]
          =ᵐ[P] P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)]
            - (fun _ ↦ ((t : ℝ) - (s : ℝ))) := by
      refine (condExp_sub h_int_diff_sq (integrable_const _) _).trans ?_
      rw [condExp_const (𝓕.le s)]
    refine h_sub.trans ?_
    filter_upwards [condExp_increment_sq (hX := hX) hst] with ω h
    show P[fun ω ↦ (X t ω - X s ω) ^ 2 | (𝓕 s : MeasurableSpace Ω)] ω
          - ((t : ℝ) - (s : ℝ)) = 0
    rw [h]; ring
  -- Combine via linear_combination on the per-ω conditional-expectation identities.
  filter_upwards [step_outer, step_inner, step_smul,
    step_diff_sq_residual, condExp_cross_zero (hX := hX) hst]
    with ω h_outer h_inner h_smul h_diff_sq_zero h_cross
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h_outer h_inner h_smul
  linear_combination h_outer + h_inner + h_smul + 2 * h_cross + h_diff_sq_zero

/-- **Wald exponential martingale.** For a filtered pre-Brownian motion `X` and `α : ℝ`,
the process `t ↦ exp(α X_t − α² t / 2)` is a martingale w.r.t. `𝓕`.

Decomposition: `α X_t − α²t/2 = (α X_s − α²s/2) + (α (X_t − X_s) − α²(t−s)/2)`. Setting
`M_s := exp(α X_s − α²s/2)` (which is `𝓕_s`-measurable) and
`D_{st} := exp(α (X_t − X_s) − α²(t−s)/2)` (which is independent of `𝓕_s`),
pointwise `M_t = M_s · D_{st}` and `E[D_{st}] = 1` (Gaussian MGF at `α`). Pull-out yields
`E[M_t | 𝓕_s] = M_s · E[D_{st} | 𝓕_s] = M_s`. -/
theorem waldExponential_isMartingale (α : ℝ) :
    Martingale (fun t ω ↦ Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2)) 𝓕 P := by
  refine ⟨fun u ↦ ?_, fun s t hst ↦ ?_⟩
  -- Adaptedness.
  · have hB : StronglyMeasurable[𝓕 u] (X u) := hX.stronglyAdapted u
    have hinner : StronglyMeasurable[𝓕 u]
        (fun ω ↦ α * X u ω - α ^ 2 * (u : ℝ) / 2) :=
      (hB.const_mul α).sub stronglyMeasurable_const
    exact Real.continuous_exp.comp_stronglyMeasurable hinner
  -- Conditional-expectation step.
  have h_meas_t : Measurable (X t) := ((hX.stronglyAdapted t).mono (𝓕.le t)).measurable
  have h_meas_s : Measurable (X s) := ((hX.stronglyAdapted s).mono (𝓕.le s)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X s ω) := h_meas_t.sub h_meas_s
  have hL_diff : HasLaw (X t - X s) (gaussianReal 0 (max (t - s) (s - t))) P :=
    hX.hasLaw_sub t s
  -- Integrability of `exp(α (X_t − X_s))`.
  have h_int_exp_diff : Integrable (fun ω ↦ Real.exp (α * (X t ω - X s ω))) P :=
    integrable_exp_mul_of_hasLaw h_meas_diff hL_diff α
  -- Mean of `exp(α (X_t − X_s))` (Gaussian MGF at `α`).
  have h_int_exp_diff_eq :
      ∫ ω, Real.exp (α * (X t ω - X s ω)) ∂P
        = Real.exp (α ^ 2 * ((max (t - s) (s - t) : ℝ≥0) : ℝ) / 2) := by
    have hf : AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (α * x))
                (gaussianReal 0 (max (t - s) (s - t))) := by fun_prop
    have h := hL_diff.integral_comp hf
    have h_lhs : ((fun x ↦ Real.exp (α * x)) ∘ (X t - X s))
               = (fun ω ↦ Real.exp (α * (X t ω - X s ω))) := rfl
    rw [h_lhs, integral_exp_mul_gaussianReal_zero] at h
    exact h
  -- Define `M_s` (𝓕_s-measurable factor) and the increment exponential `D_{st}`.
  set Ms : Ω → ℝ := fun ω ↦ Real.exp (α * X s ω - α ^ 2 * (s : ℝ) / 2)
  set Dst : Ω → ℝ := fun ω ↦
    Real.exp (α * (X t ω - X s ω) - α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2)
  have hMs_meas : StronglyMeasurable[𝓕 s] Ms := by
    have hB_s : StronglyMeasurable[𝓕 s] (X s) := hX.stronglyAdapted s
    have hinner_s : StronglyMeasurable[𝓕 s] (fun ω ↦ α * X s ω - α ^ 2 * (s : ℝ) / 2) :=
      (hB_s.const_mul α).sub stronglyMeasurable_const
    exact Real.continuous_exp.comp_stronglyMeasurable hinner_s
  -- Pointwise: `exp(α X_t − α²t/2) = M_s · D_{st}`.
  have h_decomp : ∀ ω, Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2) = Ms ω * Dst ω := by
    intro ω
    show _ = Real.exp _ * Real.exp _
    rw [← Real.exp_add]
    congr 1
    ring
  -- Factor `D_{st} = exp(-α²(t−s)/2) · exp(α(X_t−X_s))`.
  have hDst_factor : Dst = (fun ω ↦ Real.exp (-(α ^ 2 * ((t : ℝ) - (s : ℝ)) / 2))
                                 * Real.exp (α * (X t ω - X s ω))) := by
    funext ω
    show Real.exp _ = _ * Real.exp _
    rw [← Real.exp_add]; congr 1; ring
  -- Integrability of `D_{st}`.
  have h_int_Dst : Integrable Dst P := hDst_factor ▸ h_int_exp_diff.const_mul _
  -- Mean of `D_{st}` is 1.
  have h_int_Dst_eq_one : ∫ ω, Dst ω ∂P = 1 := by
    rw [hDst_factor, integral_const_mul, h_int_exp_diff_eq, NNReal.max_sub_eq_of_le hst,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  -- `E[D_{st} | 𝓕_s] =ᵐ 1` (the increment is independent of `𝓕 s`).
  have h_condDst : P[Dst | (𝓕 s : MeasurableSpace Ω)] =ᵐ[P] fun _ ↦ (1 : ℝ) :=
    condExp_func_increment hst h_meas_diff
      (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).sub continuous_const)).measurable
      h_int_Dst_eq_one
  -- Pull-out: `E[M_s · D_{st} | 𝓕_s] =ᵐ M_s · E[D_{st} | 𝓕_s] =ᵐ M_s · 1 = M_s`.
  have h_int_Ms : Integrable Ms P := by
    have hMs_factor : Ms = (fun ω ↦ Real.exp (-(α ^ 2 * (s : ℝ) / 2))
                                * Real.exp (α * X s ω)) := by
      funext ω
      show Real.exp _ = _ * Real.exp _
      rw [← Real.exp_add]; congr 1; ring
    rw [hMs_factor]
    exact (integrable_exp_mul_of_hasLaw h_meas_s (hX.hasLaw_eval s) α).const_mul _
  have h_int_MsDst : Integrable (fun ω ↦ Ms ω * Dst ω) P := by
    rw [← funext h_decomp]
    have h_eq : (fun ω ↦ Real.exp (α * X t ω - α ^ 2 * (t : ℝ) / 2))
              = (fun ω ↦ Real.exp (-(α ^ 2 * (t : ℝ) / 2)) * Real.exp (α * X t ω)) := by
      funext ω
      show Real.exp _ = _ * Real.exp _
      rw [← Real.exp_add]; congr 1; ring
    rw [h_eq]
    exact (integrable_exp_mul_of_hasLaw h_meas_t (hX.hasLaw_eval t) α).const_mul _
  have h_pullout :
      P[fun ω ↦ Ms ω * Dst ω | (𝓕 s : MeasurableSpace Ω)]
        =ᵐ[P] Ms * (P[Dst | (𝓕 s : MeasurableSpace Ω)]) :=
    condExp_mul_of_stronglyMeasurable_left hMs_meas h_int_MsDst h_int_Dst
  have h_decomp_ae :
      (fun u ↦ Real.exp (α * X t u - α ^ 2 * (t : ℝ) / 2)) =ᵐ[P] fun ω ↦ Ms ω * Dst ω :=
    Filter.Eventually.of_forall h_decomp
  refine (condExp_congr_ae h_decomp_ae).trans ?_
  refine h_pullout.trans ?_
  filter_upwards [h_condDst] with ω hω
  show (Ms * P[Dst | (𝓕 s : MeasurableSpace Ω)]) ω = Ms ω
  simp only [Pi.mul_apply, hω, mul_one]

end IsFilteredPreBrownian

end ProbabilityTheory
