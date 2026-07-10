/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import BrownianMotion.Gaussian.BrownianMotion
public import MathFin.Foundations.WienerIntegral

/-!
# Wiener integral on L²([0, T])

Builds the continuous linear isometry

  `wienerIntegralLp : Lp ℝ 2 (volume.restrict (Set.Ioc 0 T)) →L[ℝ] Lp ℝ 2 μ`

from the formal-combination assembly isometry (`assembly_isometry`) via the
standard density / `LinearMap.extendOfNorm` construction.

## Construction

1. Index step intervals by `StepIndex T := { (s, t) : ℝ≥0 × ℝ≥0 // s ≤ t ∧ t ≤ T }`.
2. Two linear maps out of the finitely supported coefficient space
   `StepIndex T →₀ ℝ`:
   * `stepAssembly`: `δ_(s, t) ↦ indicatorConstLp 2 _ _ 1` in
     `Lp ℝ 2 (volume.restrict (Set.Ioc 0 T))`.
   * `wienerAssembly`: `δ_(s, t) ↦ [fun ω ↦ B t ω - B s ω]` in `Lp ℝ 2 μ`.
3. `‖wienerAssembly f‖ = ‖stepAssembly f‖` for every `f : StepIndex T →₀ ℝ`,
   from the BM covariance identity `E[(B_t-B_s)(B_v-B_u)] = vol((s,t]∩(u,v])`.
4. Density of step indicators in `Lp` via orthogonal complement +
   π-system induction over `borel_eq_generateFrom_Ioc_le` +
   `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`.
5. `LinearMap.extendOfNorm` yields the CLM `wienerIntegralLp`, an isometry.

## Main results

* `wiener_assembly_isometry`: the step-function Itô isometry on
  `StepIndex T →₀ ℝ`.
* `stepAssembly_denseRange`: step indicators span a dense subspace of
  `Lp ℝ 2 (volume.restrict (Set.Ioc 0 T))`.
* `wienerIntegralLp`: the Wiener integral as a `ContinuousLinearMap` from
  `Lp ℝ 2 (volume.restrict (Set.Ioc 0 T))` to `Lp ℝ 2 μ`, via
  `LinearMap.extendOfNorm`.
* `wienerIntegralLp_norm`: the Itô isometry `‖wienerIntegralLp f‖ = ‖f‖`.
* `wienerIntegralLp_integral_sq`: the Itô isometry in integral form,
  `∫ ω, (I f ω)² ∂μ = ∫ s in (0, T], (f s)² ∂volume`.
-/

@[expose] public section

namespace MathFin
namespace WienerIntegralL2

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal Topology InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

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

/-- The right endpoint `hi i` of a `StepIndex` is `≤ T`. -/
lemma hi_le_T (i : StepIndex T) : i.hi ≤ (T : ℝ) := by
  unfold hi
  exact_mod_cast i.2.2

/-- The half-open interval `(lo, hi]` as a subset of ℝ. -/
def interval (i : StepIndex T) : Set ℝ := Set.Ioc i.lo i.hi

/-- The `StepIndex` interval `(lo, hi]` is measurable. -/
lemma measurableSet_interval (i : StepIndex T) :
    MeasurableSet (i.interval) := measurableSet_Ioc

/-- The interval represented by a `StepIndex T` is contained in `(0, T]`. -/
lemma interval_subset_Ioc_zero_T (i : StepIndex T) :
    i.interval ⊆ Set.Ioc (0 : ℝ) (T : ℝ) := by
  rintro x ⟨hx_lo, hx_hi⟩
  exact ⟨lt_of_le_of_lt (i.1.1 : ℝ≥0).coe_nonneg hx_lo,
    hx_hi.trans i.hi_le_T⟩

/-- The `StepIndex` interval has finite Lebesgue measure. -/
lemma volume_interval_lt_top (i : StepIndex T) :
    (volume i.interval) ≠ ∞ := by
  rw [interval, Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

end StepIndex

/-! ### Lp elements: step indicator and Wiener increment -/

/-- Helper: measure of an interval under the restricted volume is finite. -/
lemma StepIndex.restrict_interval_ne_top {T : ℝ≥0} (i : StepIndex T) :
    (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) i.interval ≠ ∞ := by
  rw [Measure.restrict_apply i.measurableSet_interval,
      Set.inter_eq_left.mpr i.interval_subset_Ioc_zero_T]
  exact i.volume_interval_lt_top

/-- The indicator `𝟙_{(lo, hi]}` as an element of `Lp ℝ 2 (volume.restrict (Set.Ioc 0 T))`. -/
noncomputable def stepIndicatorLp (T : ℝ≥0) (i : StepIndex T) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  indicatorConstLp 2 i.measurableSet_interval i.restrict_interval_ne_top (1 : ℝ)

/-- The Wiener increment `B(hi) - B(lo)` is in `L²(μ)`. -/
lemma memLp_increment_two (hB : IsPreBrownianReal B μ) {T : ℝ≥0} (i : StepIndex T) :
    MemLp (fun ω ↦ B i.1.2 ω - B i.1.1 ω) 2 μ :=
  hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two

/-- The Wiener increment `B(hi) - B(lo)` as an element of `Lp ℝ 2 μ`. -/
noncomputable def wienerIncrementLp (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B μ) {T : ℝ≥0} (i : StepIndex T) : Lp ℝ 2 μ :=
  (memLp_increment_two hB i).toLp _

variable [IsProbabilityMeasure μ]

/-! ### Assembly maps on finitely supported coefficients -/

/-- Linear map from finitely supported coefficients to step functions. -/
noncomputable def stepAssembly (T : ℝ≥0) :
    (StepIndex T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  Finsupp.linearCombination ℝ (stepIndicatorLp T)

/-- Linear map from finitely supported coefficients to Wiener increments. -/
noncomputable def wienerAssembly (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B μ) (T : ℝ≥0) :
    (StepIndex T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 μ :=
  Finsupp.linearCombination ℝ (wienerIncrementLp B hB (T := T))

/-! ### Covariance identity for BM increments

For `s ≤ t, u ≤ v ∈ ℝ≥0`,
`E[(B_t - B_s)(B_v - B_u)] = vol((s, t] ∩ (u, v])`.

The right hand side is written as `max 0 (min t v - max s u)`. -/

/-- `∫ ω, B s ω * B t ω ∂μ = min s t` for pre-Brownian motion `B` with zero start,
using `IsPreBrownianReal.covariance_eval` and `covariance_eq_sub` (the means are zero). -/
lemma integral_mul_eval (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) :
    ∫ ω, B s ω * B t ω ∂μ = ((min s t : ℝ≥0) : ℝ) := by
  have hBs : MemLp (B s) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hBt : MemLp (B t) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have h_cov := hB.covariance_eval s t
  rw [covariance_eq_sub hBs hBt] at h_cov
  have hEs : ∫ ω, B s ω ∂μ = 0 := hB.integral_eval s
  have hEt : ∫ ω, B t ω ∂μ = 0 := hB.integral_eval t
  rw [hEs, hEt, zero_mul, sub_zero] at h_cov
  exact h_cov

/-- Endpoint arithmetic for the covariance of two ordered Brownian increments. -/
private lemma covariance_increment_arithmetic
    (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v) :
    ((min t v : ℝ≥0) : ℝ) - ((min t u : ℝ≥0) : ℝ) -
      ((min s v : ℝ≥0) : ℝ) + ((min s u : ℝ≥0) : ℝ) =
        max 0 ((min (t : ℝ) v) - (max (s : ℝ) u)) := by
  push_cast
  have hsR : (s : ℝ) ≤ t := by exact_mod_cast hst
  have huR : (u : ℝ) ≤ v := by exact_mod_cast huv
  rcases le_total (s : ℝ) u with hsu | hsu
  all_goals rcases le_total (t : ℝ) u with htu | htu
  all_goals rcases le_total (t : ℝ) v with htv | htv
  all_goals rcases le_total (s : ℝ) v with hsv | hsv
  all_goals simp_all
  all_goals nlinarith

/-- Covariance identity for BM increments:
`E[(B_t - B_s)(B_v - B_u)] = vol((s, t] ∩ (u, v])`,
expressed via `max 0 (min t v - max s u)`. -/
lemma covariance_increment_aux (hB : IsPreBrownianReal B μ)
    (s t u v : ℝ≥0) (hst : s ≤ t) (huv : u ≤ v) :
    ∫ ω, (B t ω - B s ω) * (B v ω - B u ω) ∂μ =
      max 0 ((min (t : ℝ) v) - (max (s : ℝ) u)) := by
  have hBs : MemLp (B s) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hBt : MemLp (B t) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hBu : MemLp (B u) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  have hBv : MemLp (B v) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval v).memLp_two
  have hInt_tv : Integrable (fun ω ↦ B t ω * B v ω) μ :=
    MemLp.integrable_mul hBt hBv
  have hInt_tu : Integrable (fun ω ↦ B t ω * B u ω) μ :=
    MemLp.integrable_mul hBt hBu
  have hInt_sv : Integrable (fun ω ↦ B s ω * B v ω) μ :=
    MemLp.integrable_mul hBs hBv
  have hInt_su : Integrable (fun ω ↦ B s ω * B u ω) μ :=
    MemLp.integrable_mul hBs hBu
  have h_eq_fun :
      (fun ω ↦ (B t ω - B s ω) * (B v ω - B u ω)) =
        (fun ω ↦ B t ω * B v ω - B t ω * B u ω - B s ω * B v ω + B s ω * B u ω) := by
    funext ω
    ring
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
    rw [h_eq_fun]
    linarith [e1, e2, e3]
  rw [h_lhs, integral_mul_eval hB t v, integral_mul_eval hB t u,
      integral_mul_eval hB s v, integral_mul_eval hB s u]
  exact covariance_increment_arithmetic s t u v hst huv

/-! ### The key isometry on finitely supported coefficients -/

/-- The core pairing identity: for two step indices `i j ∈ StepIndex T`,
the inner product of the Wiener increments equals the inner product of the
step indicators in `Lp ℝ 2 (volume.restrict (Set.Ioc 0 T))`. -/
private lemma inner_wienerIncrementLp_eq (hB : IsPreBrownianReal B μ)
    {T : ℝ≥0} (i j : StepIndex T) :
    ⟪wienerIncrementLp B hB i, wienerIncrementLp B hB j⟫_ℝ =
      ⟪stepIndicatorLp T i, stepIndicatorLp T j⟫_ℝ := by
  -- LHS: L2.inner_def reduces ⟪·, ·⟫ to ∫ ⟪f, g⟫_ℝ ∂μ; for real values
  -- ⟪x, y⟫_ℝ = y * x (Mathlib star-product convention), so we commute via ring.
  have hLHS : ⟪wienerIncrementLp B hB i, wienerIncrementLp B hB j⟫_ℝ =
              max 0 ((min (i.hi : ℝ) j.hi) - (max (i.lo : ℝ) j.lo)) := by
    rw [L2.inner_def]
    have h_eq : ∀ᵐ ω ∂μ,
        (⟪(wienerIncrementLp B hB i : Ω → ℝ) ω,
          (wienerIncrementLp B hB j : Ω → ℝ) ω⟫_ℝ : ℝ) =
        (B i.1.2 ω - B i.1.1 ω) * (B j.1.2 ω - B j.1.1 ω) := by
      filter_upwards [MemLp.coeFn_toLp (memLp_increment_two hB i),
                       MemLp.coeFn_toLp (memLp_increment_two hB j)]
        with ω hωI hωJ
      rw [show (wienerIncrementLp B hB i : Ω → ℝ) ω = B i.1.2 ω - B i.1.1 ω from hωI,
          show (wienerIncrementLp B hB j : Ω → ℝ) ω = B j.1.2 ω - B j.1.1 ω from hωJ]
      show (B j.1.2 ω - B j.1.1 ω) * (B i.1.2 ω - B i.1.1 ω) = _
      ring
    rw [integral_congr_ae h_eq]
    exact covariance_increment_aux hB i.1.1 i.1.2 j.1.1 j.1.2 i.2.1 j.2.1
  -- RHS: indicator inner product = volume of intersection = max 0 (min hi - max lo).
  have hRHS : ⟪stepIndicatorLp T i, stepIndicatorLp T j⟫_ℝ =
              max 0 ((min (i.hi : ℝ) j.hi) - (max (i.lo : ℝ) j.lo)) := by
    rw [stepIndicatorLp, stepIndicatorLp,
        MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
          i.measurableSet_interval j.measurableSet_interval
          i.restrict_interval_ne_top j.restrict_interval_ne_top]
    have h_inter : i.interval ∩ j.interval =
        Set.Ioc (max (i.lo : ℝ) j.lo) (min (i.hi : ℝ) j.hi) := by
      simp [StepIndex.interval, Set.Ioc_inter_Ioc]
    have h_sub :
        Set.Ioc (max (i.lo : ℝ) j.lo) (min (i.hi : ℝ) j.hi) ⊆ Set.Ioc (0 : ℝ) (T : ℝ) := by
      rw [← h_inter]
      exact fun x hx ↦ i.interval_subset_Ioc_zero_T hx.1
    rw [Measure.real_def,
        Measure.restrict_apply (i.measurableSet_interval.inter j.measurableSet_interval),
        h_inter, Set.inter_eq_left.mpr h_sub, Real.volume_Ioc,
        ENNReal.toReal_ofReal', max_comm]
  rw [hLHS, hRHS]

theorem wiener_assembly_isometry (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (f : StepIndex T →₀ ℝ) :
    ‖wienerAssembly B hB T f‖ = ‖stepAssembly T f‖ := by
  -- Squares of both norms equal a common double-sum over `f.support × f.support`.
  have h_sq : ‖wienerAssembly B hB T f‖ ^ 2 = ‖stepAssembly T f‖ ^ 2 := by
    rw [← @real_inner_self_eq_norm_sq _ _ _ (wienerAssembly B hB T f),
        ← @real_inner_self_eq_norm_sq _ _ _ (stepAssembly T f)]
    simp only [wienerAssembly, stepAssembly, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_inner, Finsupp.sum_inner]
    refine Finsupp.sum_congr (fun i _ ↦ ?_)
    rw [Finsupp.inner_sum, Finsupp.inner_sum]
    refine Finsupp.sum_congr (fun j _ ↦ ?_)
    rw [real_inner_smul_left, real_inner_smul_right,
        real_inner_smul_left, real_inner_smul_right,
        inner_wienerIncrementLp_eq hB i j]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h_sq

/-! ### Density of step indicators in `Lp ℝ 2 (volume.restrict (Ioc 0 T))`

Orthogonal-complement route: take `g` orthogonal to every step indicator;
deduce `∫ x in Ioc a b, g x ∂ν = 0` for every `a ≤ b` (truncating endpoints to
`[0, T]` reduces to the orthogonality hypothesis); extend by π-system induction
(`{Ioc a b | a ≤ b}` is a π-system generating `Borel ℝ`) to all measurable sets;
apply `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero` to conclude `g = 0`. Hence
the orthogonal complement is `⊥`, so the closure of the range is `⊤`. -/

/-- For `g : Lp ℝ 2 (volume.restrict (Ioc 0 T))` orthogonal to every step
indicator, the set-integral of `g` over any half-open interval `Ioc a b`
(arbitrary `a ≤ b ∈ ℝ`) vanishes. -/
private lemma setIntegral_Ioc_eq_zero_of_orthogonal {T : ℝ≥0}
    (g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
    (h_orth : ∀ i : StepIndex T, ⟪stepIndicatorLp T i, g⟫_ℝ = 0)
    (a b : ℝ) :
    ∫ x in Set.Ioc a b, g x ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) = 0 := by
  -- Push the restrict through: `∫ x in s, g x ∂(volume.restrict S) = ∫ x in s ∩ S, g x ∂volume`.
  rw [show (∫ x in Set.Ioc a b, (g : ℝ → ℝ) x ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
        = ∫ x in Set.Ioc (max a 0) (min b (T : ℝ)), (g : ℝ → ℝ) x ∂volume by
      show ∫ x, _ ∂((volume.restrict _).restrict _) = ∫ x, _ ∂(volume.restrict _)
      rw [Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioc]]
  by_cases hab' : max a 0 ≤ min b (T : ℝ)
  · -- Build a StepIndex matching `(max a 0, min b T]` and apply orthogonality.
    have ha'_nn : (0 : ℝ) ≤ max a 0 := le_max_right _ _
    have hb'_T : min b (T : ℝ) ≤ (T : ℝ) := min_le_right _ _
    have hb'_nn : (0 : ℝ) ≤ min b (T : ℝ) := le_trans ha'_nn hab'
    let i : StepIndex T :=
      ⟨(⟨max a 0, ha'_nn⟩, ⟨min b (T : ℝ), hb'_nn⟩), hab', by exact_mod_cast hb'_T⟩
    -- The orthogonal inner product evaluates to `∫ x in (max a 0, min b T], g x ∂volume`:
    -- after `inner_indicatorConstLp_one` it's `∫ in i.interval over ν`, and since
    -- `i.interval ⊆ Ioc 0 T`, the restrict collapses.
    have h_inner_to_int :
        ⟪stepIndicatorLp T i, g⟫_ℝ =
          ∫ x in Set.Ioc (max a 0) (min b (T : ℝ)), g x ∂volume := by
      have h_indicator_inner :
          ⟪stepIndicatorLp T i, g⟫_ℝ =
            ∫ x in i.interval, g x ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
        rw [stepIndicatorLp]
        exact MeasureTheory.L2.inner_indicatorConstLp_one (𝕜 := ℝ)
          i.measurableSet_interval i.restrict_interval_ne_top g
      rw [h_indicator_inner]
      show ∫ x, _ ∂((volume.restrict _).restrict i.interval) = _
      rw [Measure.restrict_restrict i.measurableSet_interval]
      show ∫ x in i.interval ∩ Set.Ioc (0 : ℝ) (T : ℝ), g x ∂volume = _
      rw [show i.interval ∩ Set.Ioc (0 : ℝ) (T : ℝ) = Set.Ioc (max a 0) (min b (T : ℝ)) by
            show Set.Ioc (max a 0) (min b (T : ℝ)) ∩ Set.Ioc (0 : ℝ) (T : ℝ) = _
            rw [Set.Ioc_inter_Ioc, max_eq_left ha'_nn, min_eq_left hb'_T]]
    rw [← h_inner_to_int]
    exact h_orth i
  · push Not at hab'
    rw [Set.Ioc_eq_empty (lt_asymm hab'), setIntegral_empty]

/-- For `g : Lp ℝ 2 (volume.restrict (Ioc 0 T))` orthogonal to every step
indicator, the set-integral of `g` over any measurable set vanishes.
Proved by π-system induction (`borel_eq_generateFrom_Ioc_le`) over the base
case `setIntegral_Ioc_eq_zero_of_orthogonal`. -/
private lemma setIntegral_eq_zero_of_orthogonal {T : ℝ≥0}
    (g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
    (h_orth : ∀ i : StepIndex T, ⟪stepIndicatorLp T i, g⟫_ℝ = 0)
    (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) = 0 := by
  -- ν is a finite measure (volume of (0, T] = T < ∞).
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hg_int : Integrable g (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
    (Lp.memLp g).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  -- Apply π-system induction over `Borel ℝ = generateFrom {Ioc a b | a ≤ b}`.
  refine MeasurableSpace.induction_on_inter (C := fun s _ ↦
    ∫ x in s, g x ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) = 0)
    (h_eq := borel_eq_generateFrom_Ioc_le ℝ) (h_inter := ?_)
    (empty := ?_) (basic := ?_) (compl := ?_) (iUnion := ?_) s hs
  · -- π-system: intersection of two `Ioc a b` (nonempty) is again such.
    rintro u ⟨a₁, b₁, _, rfl⟩ v ⟨a₂, b₂, _, rfl⟩ huv
    rw [Set.Ioc_inter_Ioc] at huv
    exact ⟨max a₁ a₂, min b₁ b₂, (Set.nonempty_Ioc.mp huv).le, (Set.Ioc_inter_Ioc ..).symm⟩
  · exact setIntegral_empty
  · -- Base case `Ioc a b`.
    rintro _ ⟨a, b, _, rfl⟩
    exact setIntegral_Ioc_eq_zero_of_orthogonal g h_orth a b
  · -- Complement: ∫ univ = 0 (by base case `a = 0, b = T`), so ∫ tᶜ = -∫ t = 0.
    intro t ht hPt
    have h_full :
        ∫ x, g x ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) = 0 := by
      have h_ioc := setIntegral_Ioc_eq_zero_of_orthogonal g h_orth 0 (T : ℝ)
      rwa [show (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).restrict
              (Set.Ioc (0 : ℝ) (T : ℝ)) = volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)) by
            rw [Measure.restrict_restrict measurableSet_Ioc, Set.inter_self]] at h_ioc
    linarith [integral_add_compl ht hg_int, hPt, h_full]
  · -- Disjoint union: countable additivity.
    intro f hf hf_meas hf_zero
    rw [integral_iUnion hf_meas hf hg_int.integrableOn]
    simp [hf_zero]

/-- The map `stepAssembly T` has dense range in
`Lp ℝ 2 (volume.restrict (Set.Ioc 0 T))`. The proof identifies the orthogonal
complement with `⊥` using `setIntegral_eq_zero_of_orthogonal` and
`Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`. -/
theorem stepAssembly_denseRange (T : ℝ≥0) :
    DenseRange (stepAssembly T) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc];
        exact ENNReal.ofReal_lt_top⟩
  -- Suffices: `(LinearMap.range (stepAssembly T))ᗮ = ⊥` (every `g` orthogonal to range is 0).
  suffices h_orth_eq_bot : (LinearMap.range (stepAssembly T))ᗮ = ⊥ by
    rw [denseRange_iff_closure_range, ← LinearMap.coe_range (stepAssembly T),
        ← Submodule.topologicalClosure_coe,
        Submodule.topologicalClosure_eq_top_iff.mpr h_orth_eq_bot, Submodule.top_coe]
  rw [Submodule.eq_bot_iff]
  intro g h_mem
  rw [Submodule.mem_orthogonal] at h_mem
  have h_orth : ∀ i : StepIndex T, ⟪stepIndicatorLp T i, g⟫_ℝ = 0 := fun i ↦
    h_mem _ ⟨Finsupp.single i 1, by simp [stepAssembly, Finsupp.linearCombination_single]⟩
  exact (Lp.eq_zero_iff_ae_eq_zero (f := g)).mpr <|
    Lp.ae_eq_zero_of_forall_setIntegral_eq_zero g (by norm_num) (by simp)
      (fun _ _ _ ↦ ((Lp.memLp g).integrable one_le_two).integrableOn)
      (fun s hs _ ↦ setIntegral_eq_zero_of_orthogonal g h_orth s hs)

/-- The Wiener integral as a continuous linear isometry
`Lp ℝ 2 (volume.restrict (Set.Ioc 0 T)) →L[ℝ] Lp ℝ 2 μ`. -/
noncomputable def wienerIntegralLp (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B μ) (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) →L[ℝ] Lp ℝ 2 μ :=
  (wienerAssembly B hB T).extendOfNorm (stepAssembly T)

/-- Itô isometry, norm form. For every `f ∈ L²([0, T])`,
`‖wienerIntegralLp f‖ = ‖f‖`. -/
theorem wienerIntegralLp_norm (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    ‖wienerIntegralLp B hB T f‖ = ‖f‖ := by
  rw [wienerIntegralLp]
  exact LinearMap.norm_extendOfNorm_eq_of_isometry
    (stepAssembly_denseRange T) (wiener_assembly_isometry hB T) f

/-- Helper: for any `g : Lp ℝ 2 ν`, `‖g‖² = ∫ ω, (g ω)² ∂ν`. (Public so the
Gaussian-law companion `Foundations/WienerIntegralGaussian.lean` reuses it on
both the Ω-side and the time-side measures.) -/
lemma Lp_real_two_norm_sq {α : Type*} {mα : MeasurableSpace α} (ν : Measure α)
    (g : Lp ℝ 2 ν) : ‖g‖ ^ 2 = ∫ ω, (g ω) ^ 2 ∂ν := by
  have h : ⟪g, g⟫_ℝ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  rw [L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with ω
  show (g ω) * (g ω) = (g ω) ^ 2
  ring

/-- Itô isometry, integral form. For every `f ∈ L²([0, T])`,
`∫ ω, (wienerIntegralLp f ω)² ∂μ = ∫ s in (0, T], (f s)² ∂volume`. -/
theorem wienerIntegralLp_integral_sq (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    ∫ ω, (wienerIntegralLp B hB T f ω) ^ 2 ∂μ =
      ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), (f s) ^ 2 ∂volume := by
  rw [← Lp_real_two_norm_sq μ (wienerIntegralLp B hB T f),
      wienerIntegralLp_norm hB T f,
      Lp_real_two_norm_sq (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) f]

end WienerIntegralL2
end MathFin
