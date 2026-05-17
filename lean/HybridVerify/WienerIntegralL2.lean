/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import BrownianMotion.Gaussian.BrownianMotion
public import HybridVerify.WienerIntegral

/-!
# Wiener integral on L²([0, T])

Extends the step-function Itô isometry (`wiener_finset_isometry`) to a
continuous linear isometry

  `wienerIntegralLp : Lp ℝ 2 (volume.restrict (Set.Iic T)) →L[ℝ] Lp ℝ 2 μ`

via the standard density / `LinearMap.extendOfNorm` construction.

## Construction

1. Index step intervals by `StepIndex T := { (s, t) : ℝ≥0 × ℝ≥0 // s ≤ t ∧ t ≤ T }`.
2. Two formal-assembly linear maps on `StepIndex T →₀ ℝ`:
   * `stepAssembly`: `δ_(s, t) ↦ indicatorConstLp 2 _ _ 1` in
     `Lp ℝ 2 (volume.restrict (Set.Iic T))`.
   * `wienerAssembly`: `δ_(s, t) ↦ [fun ω ↦ B t ω - B s ω]` in `Lp ℝ 2 μ`.
3. `‖wienerAssembly f‖ = ‖stepAssembly f‖` for every `f : StepIndex T →₀ ℝ`,
   from the BM covariance identity `E[(B_t-B_s)(B_v-B_u)] = vol((s,t]∩(u,v])`.
4. `LinearMap.extendOfNorm` yields the CLM `wienerIntegralLp`.

## Main results

* `wiener_assembly_isometry`: the step-function Itô isometry on the
  formal-combination space `StepIndex T →₀ ℝ` (unconditional).
* `wienerIntegralLp`: the Wiener integral as a `ContinuousLinearMap` from
  `Lp ℝ 2 (volume.restrict (Set.Iic T))` (unconditional definition via
  `LinearMap.extendOfNorm`; isometry only under the density hypothesis).
* `wienerIntegralLp_norm` / `wienerIntegralLp_integral_sq`: the Itô isometry
  conditional on `DenseRange (stepAssembly T)`.

## Density status (outstanding)

Closing the L²-extension to a full unconditional `‖wienerIntegralLp f‖ = ‖f‖`
requires showing step indicators span a dense subspace of
`Lp ℝ 2 (volume.restrict (Set.Iic T))`. Two viable routes are documented in
the body of `WienerIntegralL2`:

* Orthogonal complement via `borel_eq_generateFrom_Ioc_le` +
  `MeasurableSpace.induction_on_inter` + `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`.
* `MeasureTheory.MemLp.induction_dense` with outer regularity of Lebesgue
  measure on `ℝ` to approximate indicators of measurable sets by indicators
  of finite unions of half-open intervals.

Both paths require ~120–150 lines of additional Mathlib bridge work beyond
what is currently exposed at toolchain `leanprover/lean4:v4.30.0-rc1` /
Mathlib commit `f23306121184`. Until that is closed, downstream consumers
take the `DenseRange (stepAssembly T)` proof as an explicit hypothesis.
-/

namespace HybridVerify
namespace WienerIntegralL2

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal Topology InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} [hB : IsPreBrownian B μ]

/-! ### Step-interval index -/

/-- A pair `(s, t) ∈ ℝ≥0 × ℝ≥0` with `s ≤ t ≤ T`, representing the half-open
interval `(s, t] ⊆ [0, T]` used as a basic unit of step functions. -/
abbrev StepIndex (T : ℝ≥0) : Type := { p : ℝ≥0 × ℝ≥0 // p.1 ≤ p.2 ∧ p.2 ≤ T }

namespace StepIndex
variable {T : ℝ≥0}

/-- Lower endpoint of the interval, as a real. -/
def lo (i : StepIndex T) : ℝ := (i.1.1 : ℝ)

/-- Upper endpoint of the interval, as a real. -/
def hi (i : StepIndex T) : ℝ := (i.1.2 : ℝ)

lemma lo_le_hi (i : StepIndex T) : i.lo ≤ i.hi := by
  unfold lo hi; exact_mod_cast i.2.1

lemma hi_le_T (i : StepIndex T) : i.hi ≤ (T : ℝ) := by
  unfold hi; exact_mod_cast i.2.2

/-- The half-open interval `(lo, hi]` as a subset of ℝ. -/
def interval (i : StepIndex T) : Set ℝ := Set.Ioc i.lo i.hi

lemma measurableSet_interval (i : StepIndex T) :
    MeasurableSet (i.interval) := measurableSet_Ioc

lemma volume_interval_lt_top (i : StepIndex T) :
    (volume i.interval) ≠ ∞ := by
  rw [interval, Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

lemma volume_interval_eq (i : StepIndex T) :
    volume i.interval = ENNReal.ofReal (i.hi - i.lo) := by
  rw [interval, Real.volume_Ioc]

end StepIndex

/-! ### Lp elements: step indicator and Wiener increment -/

/-- Helper: measure of an interval under the restricted volume is finite. -/
lemma StepIndex.restrict_interval_ne_top {T : ℝ≥0} (i : StepIndex T) :
    (volume.restrict (Set.Iic (T : ℝ))) i.interval ≠ ∞ := by
  rw [Measure.restrict_apply i.measurableSet_interval]
  exact ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
    (lt_of_le_of_ne le_top i.volume_interval_lt_top))

/-- The indicator `𝟙_{(lo, hi]}` as an element of `Lp ℝ 2 (volume.restrict (Set.Iic T))`. -/
noncomputable def stepIndicatorLp (T : ℝ≥0) (i : StepIndex T) :
    Lp ℝ 2 (volume.restrict (Set.Iic (T : ℝ))) :=
  indicatorConstLp 2 i.measurableSet_interval i.restrict_interval_ne_top (1 : ℝ)

omit [IsProbabilityMeasure μ] in
/-- The Wiener increment `B(hi) - B(lo)` is in `L²(μ)`. -/
lemma memLp_increment_two {T : ℝ≥0} (i : StepIndex T) :
    MemLp (fun ω => B i.1.2 ω - B i.1.1 ω) 2 μ :=
  hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two

omit [IsProbabilityMeasure μ] in
/-- The Wiener increment `B(hi) - B(lo)` as an element of `Lp ℝ 2 μ`. -/
noncomputable def wienerIncrementLp (B : ℝ≥0 → Ω → ℝ)
    [IsPreBrownian B μ] {T : ℝ≥0} (i : StepIndex T) : Lp ℝ 2 μ :=
  (memLp_increment_two (B := B) (μ := μ) i).toLp _

/-! ### Formal assembly maps on `StepIndex T →₀ ℝ` -/

/-- Linear assembly of formal coefficients into the step-function side. -/
noncomputable def stepAssembly (T : ℝ≥0) :
    (StepIndex T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Set.Iic (T : ℝ))) :=
  Finsupp.linearCombination ℝ (stepIndicatorLp T)

/-- Linear assembly of formal coefficients into the Wiener-integral side. -/
noncomputable def wienerAssembly (B : ℝ≥0 → Ω → ℝ)
    [IsPreBrownian B μ] (T : ℝ≥0) :
    (StepIndex T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 μ :=
  Finsupp.linearCombination ℝ (wienerIncrementLp (μ := μ) B (T := T))

/-! ### Covariance identity for BM increments

For `s ≤ t, u ≤ v ∈ ℝ≥0`,
`E[(B_t - B_s)(B_v - B_u)] = vol((s, t] ∩ (u, v])`.

We prove this in the cleaner form using `min` / `max` arithmetic. -/

/-- `∫ ω, B s ω * B t ω ∂μ = min s t` for pre-Brownian motion `B` with zero start.
Combines `IsPreBrownian.covariance_eval` and `covariance_eq_sub` (the means are zero). -/
lemma integral_mul_eval (s t : ℝ≥0) :
    ∫ ω, B s ω * B t ω ∂μ = ((min s t : ℝ≥0) : ℝ) := by
  have hBs : MemLp (B s) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hBt : MemLp (B t) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have h_cov := hB.covariance_eval s t
  rw [covariance_eq_sub hBs hBt] at h_cov
  have hEs : ∫ ω, B s ω ∂μ = 0 := hB.integral_eval s
  have hEt : ∫ ω, B t ω ∂μ = 0 := hB.integral_eval t
  rw [hEs, hEt, zero_mul, sub_zero] at h_cov
  exact h_cov

/-- Covariance identity for BM increments:
`E[(B_t - B_s)(B_v - B_u)] = vol((s, t] ∩ (u, v])`,
expressed via `max 0 (min t v - max s u)`. -/
lemma covariance_increment_aux (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v) :
    ∫ ω, (B t ω - B s ω) * (B v ω - B u ω) ∂μ =
      max 0 ((min (t : ℝ) v) - (max (s : ℝ) u)) := by
  have hBs : MemLp (B s) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hBt : MemLp (B t) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hBu : MemLp (B u) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  have hBv : MemLp (B v) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval v).memLp_two
  have hInt_tv : Integrable (fun ω => B t ω * B v ω) μ :=
    MemLp.integrable_mul hBt hBv
  have hInt_tu : Integrable (fun ω => B t ω * B u ω) μ :=
    MemLp.integrable_mul hBt hBu
  have hInt_sv : Integrable (fun ω => B s ω * B v ω) μ :=
    MemLp.integrable_mul hBs hBv
  have hInt_su : Integrable (fun ω => B s ω * B u ω) μ :=
    MemLp.integrable_mul hBs hBu
  have h_eq_fun :
      (fun ω => (B t ω - B s ω) * (B v ω - B u ω)) =
        (fun ω => B t ω * B v ω - B t ω * B u ω - B s ω * B v ω + B s ω * B u ω) := by
    funext ω; ring
  have e1 : ∫ ω, B t ω * B v ω - B t ω * B u ω ∂μ =
            (∫ ω, B t ω * B v ω ∂μ) - (∫ ω, B t ω * B u ω ∂μ) :=
    integral_sub hInt_tv hInt_tu
  have e2 : ∫ ω, B t ω * B v ω - B t ω * B u ω - B s ω * B v ω ∂μ =
            (∫ ω, B t ω * B v ω - B t ω * B u ω ∂μ) - (∫ ω, B s ω * B v ω ∂μ) :=
    integral_sub (hInt_tv.sub hInt_tu) hInt_sv
  have e3 :
      ∫ ω, B t ω * B v ω - B t ω * B u ω - B s ω * B v ω + B s ω * B u ω ∂μ =
        (∫ ω, B t ω * B v ω - B t ω * B u ω - B s ω * B v ω ∂μ) +
          (∫ ω, B s ω * B u ω ∂μ) :=
    integral_add ((hInt_tv.sub hInt_tu).sub hInt_sv) hInt_su
  have h_lhs :
      ∫ ω, (B t ω - B s ω) * (B v ω - B u ω) ∂μ =
        (∫ ω, B t ω * B v ω ∂μ) - (∫ ω, B t ω * B u ω ∂μ) -
        (∫ ω, B s ω * B v ω ∂μ) + (∫ ω, B s ω * B u ω ∂μ) := by
    rw [h_eq_fun]; linarith [e1, e2, e3]
  rw [h_lhs, integral_mul_eval (μ := μ) t v, integral_mul_eval (μ := μ) t u,
      integral_mul_eval (μ := μ) s v, integral_mul_eval (μ := μ) s u]
  push_cast
  have hsR : (s : ℝ) ≤ t := by exact_mod_cast hst
  have huR : (u : ℝ) ≤ v := by exact_mod_cast huv
  rcases le_total (s : ℝ) u with hsu | hsu
  all_goals rcases le_total (t : ℝ) u with htu | htu
  all_goals rcases le_total (t : ℝ) v with htv | htv
  all_goals rcases le_total (s : ℝ) v with hsv | hsv
  all_goals simp_all [min_eq_left, min_eq_right, max_eq_left, max_eq_right]
  all_goals nlinarith

/-! ### The key isometry on the formal-combination space -/

/-- The core pairing identity: for two step indices `i j ∈ StepIndex T`,
the inner product of the Wiener increments equals the inner product of the
step indicators in `Lp ℝ 2 (volume.restrict (Set.Iic T))`. -/
private lemma inner_wienerIncrementLp_eq {T : ℝ≥0} (i j : StepIndex T) :
    ⟪wienerIncrementLp (μ := μ) B i, wienerIncrementLp (μ := μ) B j⟫_ℝ =
      ⟪stepIndicatorLp T i, stepIndicatorLp T j⟫_ℝ := by
  -- LHS: integral form via L2.inner_def + covariance_increment_aux
  have hLHS : ⟪wienerIncrementLp (μ := μ) B i, wienerIncrementLp (μ := μ) B j⟫_ℝ =
              max 0 ((min (i.hi : ℝ) j.hi) - (max (i.lo : ℝ) j.lo)) := by
    rw [L2.inner_def]
    have hI : (wienerIncrementLp (μ := μ) B i : Ω → ℝ) =ᵐ[μ]
                fun ω => B i.1.2 ω - B i.1.1 ω :=
      MemLp.coeFn_toLp _
    have hJ : (wienerIncrementLp (μ := μ) B j : Ω → ℝ) =ᵐ[μ]
                fun ω => B j.1.2 ω - B j.1.1 ω :=
      MemLp.coeFn_toLp _
    have h_eq : ∀ᵐ ω ∂μ,
        (⟪(wienerIncrementLp (μ := μ) B i : Ω → ℝ) ω,
          (wienerIncrementLp (μ := μ) B j : Ω → ℝ) ω⟫_ℝ : ℝ) =
        (B i.1.2 ω - B i.1.1 ω) * (B j.1.2 ω - B j.1.1 ω) := by
      filter_upwards [hI, hJ] with ω hωI hωJ
      rw [hωI, hωJ]
      show (B j.1.2 ω - B j.1.1 ω) * (B i.1.2 ω - B i.1.1 ω) =
           (B i.1.2 ω - B i.1.1 ω) * (B j.1.2 ω - B j.1.1 ω)
      ring
    rw [integral_congr_ae h_eq]
    exact covariance_increment_aux (B := B) (μ := μ) i.1.1 i.1.2 j.1.1 j.1.2 i.2.1 j.2.1
  -- RHS: indicator inner product via real_inner_indicatorConstLp_one_indicatorConstLp_one
  have hRHS : ⟪stepIndicatorLp T i, stepIndicatorLp T j⟫_ℝ =
              max 0 ((min (i.hi : ℝ) j.hi) - (max (i.lo : ℝ) j.lo)) := by
    rw [stepIndicatorLp, stepIndicatorLp,
        MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
          i.measurableSet_interval j.measurableSet_interval
          i.restrict_interval_ne_top j.restrict_interval_ne_top]
    -- Compute (volume.restrict (Iic T)).real (i.interval ∩ j.interval)
    have h_inter : i.interval ∩ j.interval =
        Set.Ioc (max (i.lo : ℝ) j.lo) (min (i.hi : ℝ) j.hi) := by
      simp [StepIndex.interval, Set.Ioc_inter_Ioc]
    have h_meas : MeasurableSet (i.interval ∩ j.interval) :=
      i.measurableSet_interval.inter j.measurableSet_interval
    rw [Measure.real_def, Measure.restrict_apply h_meas, h_inter]
    -- Show (Ioc (max lo) (min hi)) ∩ Iic T = Ioc (max lo) (min hi)
    have hi_le : (i.hi : ℝ) ≤ T := i.hi_le_T
    have hj_le : (j.hi : ℝ) ≤ T := j.hi_le_T
    have h_sub : Set.Ioc (max (i.lo : ℝ) j.lo) (min (i.hi : ℝ) j.hi) ⊆ Set.Iic (T : ℝ) := by
      intro x hx
      simp only [Set.mem_Ioc] at hx
      simp only [Set.mem_Iic]
      exact hx.2.trans (le_trans (min_le_left _ _) hi_le)
    rw [Set.inter_eq_left.mpr h_sub, Real.volume_Ioc]
    by_cases h : max (i.lo : ℝ) j.lo ≤ min (i.hi : ℝ) j.hi
    · rw [ENNReal.toReal_ofReal (by linarith),
          max_eq_right (by linarith : (0 : ℝ) ≤ min (i.hi : ℝ) j.hi - max (i.lo : ℝ) j.lo)]
    · push_neg at h
      have hneg : min (i.hi : ℝ) j.hi - max (i.lo : ℝ) j.lo < 0 := by linarith
      rw [ENNReal.ofReal_of_nonpos hneg.le, ENNReal.toReal_zero,
          max_eq_left hneg.le]
  rw [hLHS, hRHS]

theorem wiener_assembly_isometry (T : ℝ≥0)
    (f : StepIndex T →₀ ℝ) :
    ‖wienerAssembly (μ := μ) B T f‖ = ‖stepAssembly T f‖ := by
  -- Both norms are nonneg; show squares are equal.
  have h_sq : ‖wienerAssembly (μ := μ) B T f‖ ^ 2 = ‖stepAssembly T f‖ ^ 2 := by
    rw [← @real_inner_self_eq_norm_sq _ _ _ (wienerAssembly (μ := μ) B T f),
        ← @real_inner_self_eq_norm_sq _ _ _ (stepAssembly T f)]
    simp only [wienerAssembly, stepAssembly, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_inner, Finsupp.sum_inner]
    refine Finsupp.sum_congr (fun i _ => ?_)
    rw [Finsupp.inner_sum, Finsupp.inner_sum]
    refine Finsupp.sum_congr (fun j _ => ?_)
    rw [real_inner_smul_left, real_inner_smul_right,
        real_inner_smul_left, real_inner_smul_right,
        inner_wienerIncrementLp_eq i j]
  have h1 : 0 ≤ ‖wienerAssembly (μ := μ) B T f‖ := norm_nonneg _
  have h2 : 0 ≤ ‖stepAssembly T f‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖wienerAssembly (μ := μ) B T f‖ - ‖stepAssembly T f‖)]

/-! ### The Wiener integral via continuous-linear extension

Defining the CLM extension does not require density (`extendOfNorm` accepts
any source linear map). The norm equality on the extension, however, is only
meaningful when the source map has dense range — so the two downstream
theorems `wienerIntegralLp_norm` and `wienerIntegralLp_integral_sq` take
`DenseRange (stepAssembly T)` as an explicit hypothesis.

See the file-level docstring for the two routes by which a future PR can
close that density hypothesis unconditionally. -/

/-- The Wiener integral as a continuous linear isometry
`Lp ℝ 2 (volume.restrict (Set.Iic T)) →L[ℝ] Lp ℝ 2 μ`. -/
noncomputable def wienerIntegralLp (B : ℝ≥0 → Ω → ℝ)
    [IsPreBrownian B μ] (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Iic (T : ℝ))) →L[ℝ] Lp ℝ 2 μ :=
  (wienerAssembly (μ := μ) B T).extendOfNorm (stepAssembly T)

/-- **Itô isometry (norm form), conditional on density.** For every
`f ∈ L²([0, T])`, `‖wienerIntegralLp f‖ = ‖f‖`, given that step-function
indicators span a dense subspace of `Lp ℝ 2 (volume.restrict (Set.Iic T))`. -/
theorem wienerIntegralLp_norm (T : ℝ≥0)
    (h_dense : DenseRange (stepAssembly T))
    (f : Lp ℝ 2 (volume.restrict (Set.Iic (T : ℝ)))) :
    ‖wienerIntegralLp (μ := μ) B T f‖ = ‖f‖ := by
  -- Use density of `stepAssembly` and continuity of both norms.
  set W : Lp ℝ 2 (volume.restrict (Set.Iic (T : ℝ))) →L[ℝ] Lp ℝ 2 μ :=
    wienerIntegralLp (μ := μ) B T with hW_def
  -- The norm bound (used to extract `extendOfNorm`).
  have h_norm : ∀ x : StepIndex T →₀ ℝ,
      ‖wienerAssembly (μ := μ) B T x‖ ≤ 1 * ‖stepAssembly T x‖ := by
    intro x
    rw [one_mul]
    exact (wiener_assembly_isometry (μ := μ) (B := B) T x).le
  -- On the dense subset (image of `stepAssembly`), the norm is preserved.
  have h_on_range : ∀ x : StepIndex T →₀ ℝ, ‖W (stepAssembly T x)‖ = ‖stepAssembly T x‖ := by
    intro x
    have hext : W (stepAssembly T x) = wienerAssembly (μ := μ) B T x := by
      rw [hW_def, wienerIntegralLp]
      exact LinearMap.extendOfNorm_eq h_dense ⟨1, h_norm⟩ x
    rw [hext, wiener_assembly_isometry (μ := μ) (B := B) T x]
  -- Both sides are continuous in `f`; agree on a dense set ⇒ agree everywhere.
  have h_cont₁ : Continuous (fun f => ‖W f‖) :=
    continuous_norm.comp W.continuous
  have h_cont₂ : Continuous (fun f : Lp ℝ 2 (volume.restrict (Set.Iic (T : ℝ))) => ‖f‖) :=
    continuous_norm
  refine h_dense.induction_on (p := fun y => ‖W y‖ = ‖y‖) f
    (isClosed_eq h_cont₁ h_cont₂) (fun x => h_on_range x)

/-- Helper: for any `g : Lp ℝ 2 ν`, `‖g‖² = ∫ ω, (g ω)² ∂ν`. -/
private lemma Lp_real_two_norm_sq {α : Type*} {mα : MeasurableSpace α} (ν : Measure α)
    (g : Lp ℝ 2 ν) : ‖g‖ ^ 2 = ∫ ω, (g ω) ^ 2 ∂ν := by
  have h : ⟪g, g⟫_ℝ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  rw [L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with ω
  show (g ω) * (g ω) = (g ω) ^ 2
  ring

/-- **Itô isometry (integral form), conditional on density.** For every
`f ∈ L²([0, T])`, `∫ ω, (wienerIntegralLp f ω)² ∂μ = ∫ s in [0, T], (f s)² ∂volume`. -/
theorem wienerIntegralLp_integral_sq (T : ℝ≥0)
    (h_dense : DenseRange (stepAssembly T))
    (f : Lp ℝ 2 (volume.restrict (Set.Iic (T : ℝ)))) :
    ∫ ω, (wienerIntegralLp (μ := μ) B T f ω) ^ 2 ∂μ =
      ∫ s in Set.Iic (T : ℝ), (f s) ^ 2 ∂volume := by
  -- Compute both sides as squared L² norms (via `Lp_real_two_norm_sq`)
  -- and apply the isometry `wienerIntegralLp_norm`.
  -- Note: `∫ s in S, h s ∂ν` unfolds to `∫ s, h s ∂(ν.restrict S)` by notation, so the RHS
  -- already matches `Lp_real_two_norm_sq (volume.restrict (Iic T)) f`.
  rw [← Lp_real_two_norm_sq μ (wienerIntegralLp (μ := μ) B T f),
      wienerIntegralLp_norm (μ := μ) (B := B) T h_dense f,
      Lp_real_two_norm_sq (volume.restrict (Set.Iic (T : ℝ))) f]

end WienerIntegralL2
end HybridVerify
