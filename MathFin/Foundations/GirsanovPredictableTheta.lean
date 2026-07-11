/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.SimpleProcessPartition
public import MathFin.Foundations.GirsanovSimpleDoleansMoments
public import MathFin.Foundations.GirsanovAdaptedTheta
public import MathFin.Foundations.DriftProcessPredictable
public import MathFin.Foundations.DriftProcessModification

/-! # Bounded **predictable**-θ Girsanov — `B^θ` is a `Q`-Brownian motion (Rung 1)

Generalizes the continuous-adapted Girsanov theorem (`GirsanovAdaptedTheta.Btheta_isQBrownianMotion_adapted`)
to a bounded **predictable** market price of risk `θ` — the honest domain of the Itô `L²` integral,
with no continuity assumed. The route (Route B) is the density-approximation front half over the
spine-free architecture:

* approximate `θ̂ ∈ Lp 2 (trimMeasure_T T)` by clamped, marshalled simple processes `Ṽⁿ`
  (`SimpleProcessPartition`), each in single-partition `(sⁿ, cⁿ)` form so the simple exponential
  martingale identity `isExpQMartingale_BthetaSimple` applies per `n`;
* the three functionals of the integrand converge as `Ṽⁿ → θ̂` in `E`: the stochastic integral
  `∑cᵢΔB → ∫θdB` (`SimpleProcessPartition`, Itô isometry), the drift `∑cᵢΔτ_u → ∫₀ᵘθds`, and the
  quadratic variation `∑cᵢ²Δτ_T → ∫₀ᵀθ²ds` (both here, via the drift-modification tower);
* the uniform `L⁴`/`L²` moment bounds (`GirsanovSimpleDoleansMoments`) feed the a.e.-subsequence
  set-integral engine, exactly as in the continuous case, and `isQBrownianMotion_of_expMartingale`
  reads off the `Q`-Brownian properties.

The limit drift is the genuinely-`𝓕`-adapted `driftContinuousMod θ̂` (a.e. equal to the honest
integral `∫₀ᵘθds`), so no fresh predictable-progressive-measurability lemma is needed.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology NNReal
open scoped NNReal ENNReal
open ItoIntegralL2 ItoIntegralProcess ItoIntegralCLM ItoIsometryAdapted ItoIntegralBrownian
open ItoIntegralRiemannBridge SimpleDoleansMoments ItoIntegralProcessContinuousModification

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

/-- **Bridge: the marshalled simple drift is the honest step-process drift.** The `simpleDrift`
produced by `isExpQMartingale_BthetaSimple` on the marshalled partition `(marshalPart, clampM∘marshalMult)`
equals the elementary `driftSimpleProcess` of the clamped step process `marshalStepSP` — both are the
Lebesgue integral `∫₀ᵘ ⇑(marshalStepSP)(s,ω) ds` of the same step function. This routes the drift term
into the drift-modification tower (`driftContinuousMod` and its honest-integral bridge). -/
lemma simpleDrift_marshalStepSP_eq (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) (N : ℕ) (u : ℝ≥0) (ω : Ω) :
    simpleDrift (marshalPart hBmeas T V) (fun i ω ↦ clampM C (marshalMult hBmeas T V i ω)) N u ω
      = driftSimpleProcess hBmeas (marshalStepSP hBmeas T V hle hC N).val u ω := by
  haveI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) u)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  rw [driftSimpleProcess_eq_setIntegral]
  have htoReal : ∀ i : ℕ, marshalPart hBmeas T V i ≤ marshalPart hBmeas T V (i + 1) →
      (timeMeasure (Set.Ioc (0 : ℝ≥0) u ∩
          Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1)))).toReal
        = NNReal.toReal (min (marshalPart hBmeas T V (i + 1)) u)
          - NNReal.toReal (min (marshalPart hBmeas T V i) u) := by
    intro i hi12
    rw [Set.inter_comm, timeMeasure_Ioc_inter, NNReal.coe_zero,
      max_eq_left (marshalPart hBmeas T V i).coe_nonneg, NNReal.coe_min, NNReal.coe_min]
    by_cases hiu : marshalPart hBmeas T V i ≤ u
    · rw [ENNReal.toReal_ofReal (by
            have : (marshalPart hBmeas T V i : ℝ) ≤ min (marshalPart hBmeas T V (i + 1) : ℝ) u :=
              le_min (by exact_mod_cast hi12) (by exact_mod_cast hiu)
            linarith),
        min_eq_left (by exact_mod_cast hiu : (marshalPart hBmeas T V i : ℝ) ≤ u)]
    · rw [not_le] at hiu
      have h1 : (u : ℝ) ≤ marshalPart hBmeas T V i := le_of_lt (by exact_mod_cast hiu)
      have h2 : (u : ℝ) ≤ marshalPart hBmeas T V (i + 1) := h1.trans (by exact_mod_cast hi12)
      rw [min_eq_right h2, min_eq_right h1, sub_self,
        ENNReal.ofReal_eq_zero.mpr (by linarith), ENNReal.toReal_zero]
  have hV_eq : Set.EqOn (fun s ↦ ⇑(marshalStepSP hBmeas T V hle hC N).val s ω)
      (fun s ↦ ∑ i ∈ Finset.range N,
        (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ ↦ clampM C (marshalMult hBmeas T V i ω)) s) (Set.Ioc (0 : ℝ≥0) u) :=
    fun s _ ↦ uncurry_marshalStepSP hBmeas T V hle hC N s ω
  have hint : ∀ i ∈ Finset.range N,
      Integrable (fun s ↦ (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
        (fun _ ↦ clampM C (marshalMult hBmeas T V i ω)) s)
        (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) u)) :=
    fun i _ ↦ (integrable_const _).indicator measurableSet_Ioc
  rw [setIntegral_congr_fun measurableSet_Ioc hV_eq, integral_finsetSum _ hint, simpleDrift]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul, measureReal_def,
    htoReal i (marshalPart_mono hBmeas T V hle (Nat.le_succ i)), mul_comm]

/-- **Bridge: the marshalled quadratic variation is the honest `∫₀ᵀ(step)²`.** The discrete quadratic
variation `∑ cᵢ²·Δτ` (the drift half of the marshalled Doléans exponent) equals the time-integral of
the *squared* clamped step process. On `(0,T]` the cells partition, so `(⇑(marshalStepSP))² =
∑ᵢ 𝟙_{cellᵢ}·cᵢ²` (the squared cell-constancy), and integrating the disjoint indicators recovers the
discrete sum. This routes the quadratic variation, like the drift, into the `L²`-slice machinery. -/
lemma simpleQuadVar_marshalStepSP_eq (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hmpN : marshalPart hBmeas T V N = T) (ω : Ω) :
    simpleQuadVar (marshalPart hBmeas T V)
        (fun i ω ↦ clampM C (marshalMult hBmeas T V i ω)) N T ω
      = ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(marshalStepSP hBmeas T V hle hC N).val s ω) ^ 2 ∂timeMeasure := by
  haveI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have htoReal : ∀ i : ℕ, marshalPart hBmeas T V i ≤ marshalPart hBmeas T V (i + 1) →
      (timeMeasure (Set.Ioc (0 : ℝ≥0) T ∩
          Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1)))).toReal
        = NNReal.toReal (min (marshalPart hBmeas T V (i + 1)) T)
          - NNReal.toReal (min (marshalPart hBmeas T V i) T) := by
    intro i hi12
    rw [Set.inter_comm, timeMeasure_Ioc_inter, NNReal.coe_zero,
      max_eq_left (marshalPart hBmeas T V i).coe_nonneg, NNReal.coe_min, NNReal.coe_min]
    by_cases hiT : marshalPart hBmeas T V i ≤ T
    · rw [ENNReal.toReal_ofReal (by
            have : (marshalPart hBmeas T V i : ℝ) ≤ min (marshalPart hBmeas T V (i + 1) : ℝ) T :=
              le_min (by exact_mod_cast hi12) (by exact_mod_cast hiT)
            linarith),
        min_eq_left (by exact_mod_cast hiT : (marshalPart hBmeas T V i : ℝ) ≤ T)]
    · rw [not_le] at hiT
      have h1 : (T : ℝ) ≤ marshalPart hBmeas T V i := le_of_lt (by exact_mod_cast hiT)
      have h2 : (T : ℝ) ≤ marshalPart hBmeas T V (i + 1) := h1.trans (by exact_mod_cast hi12)
      rw [min_eq_right h2, min_eq_right h1, sub_self,
        ENNReal.ofReal_eq_zero.mpr (by linarith), ENNReal.toReal_zero]
  have hsq_eq : Set.EqOn (fun s ↦ (⇑(marshalStepSP hBmeas T V hle hC N).val s ω) ^ 2)
      (fun s ↦ ∑ i ∈ Finset.range N,
        (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ ↦ (clampM C (marshalMult hBmeas T V i ω)) ^ 2) s) (Set.Ioc (0 : ℝ≥0) T) := by
    intro s hs
    dsimp only
    have hlhs : (⇑(marshalStepSP hBmeas T V hle hC N).val s ω) ^ 2 = (clampM C (⇑V s ω)) ^ 2 := by
      rw [show ⇑(marshalStepSP hBmeas T V hle hC N).val s ω
          = Function.uncurry ⇑(marshalStepSP hBmeas T V hle hC N).val (s, ω) from rfl,
        uncurry_marshalStepSP_eq_clamp hBmeas T V hle hC hmpN hs.1 hs.2 ω]
    rw [hlhs]
    have hstep : ∀ i ∈ Finset.range N,
        (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
            (fun _ ↦ (clampM C (marshalMult hBmeas T V i ω)) ^ 2) s
        = (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
            (fun _ ↦ (clampM C (⇑V s ω)) ^ 2) s := by
      intro i _
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hmem : s ∈ Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))
      · rw [if_pos hmem, if_pos hmem, marshalMult_eq_uncurry hBmeas T V hle hmem.1 hmem.2 ω]
      · rw [if_neg hmem, if_neg hmem]
    have hconst : ∀ i,
        (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
            (fun _ ↦ (clampM C (⇑V s ω)) ^ 2) s
        = (clampM C (⇑V s ω)) ^ 2 *
            (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
              (fun _ ↦ (1 : ℝ)) s := by
      intro i
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hmem : s ∈ Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))
      · rw [if_pos hmem, if_pos hmem, mul_one]
      · rw [if_neg hmem, if_neg hmem, mul_zero]
    rw [Finset.sum_congr rfl hstep]
    simp_rw [hconst]
    rw [← Finset.mul_sum, sum_cell_indicator_eq_one hBmeas T V hle hmpN hs.1 hs.2, mul_one]
  have hint : ∀ i ∈ Finset.range N,
      Integrable (fun s ↦ (Set.Ioc (marshalPart hBmeas T V i)
          (marshalPart hBmeas T V (i + 1))).indicator
        (fun _ ↦ (clampM C (marshalMult hBmeas T V i ω)) ^ 2) s)
        (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
    fun i _ ↦ (integrable_const _).indicator measurableSet_Ioc
  rw [setIntegral_congr_fun measurableSet_Ioc hsq_eq, integral_finsetSum _ hint, simpleQuadVar]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul, measureReal_def,
    htoReal i (marshalPart_mono hBmeas T V hle (Nat.le_succ i)), mul_comm]

section Convergence

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- **Slice-energy domination ⟹ convergence in measure.** If `dist(fₙ ω, g ω) ≤ K·√(Dₙ ω)` a.e. for
a nonnegative, integrable `Dₙ` whose `μ`-mean vanishes, then `fₙ → g` in measure. The single
convergence principle behind both the marshalled drift and the marshalled quadratic variation: each is
an `∫₀ᵗ`-functional of the integrand controlled — via interval Cauchy–Schwarz — by the common
`L²`-slice energy `Dₙ = ∫₀ᵀ(⇑Ṽⁿ − ⇑θ̂)²`, and `∫_μ Dₙ = ‖simpleAssembly_T Ṽⁿ − θ̂‖² → 0`. -/
lemma tendstoInMeasure_of_ae_dist_le_sqrt {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {D : ℕ → Ω → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hDnn : ∀ n, 0 ≤ᵐ[μ] D n) (hDint : ∀ n, Integrable (D n) μ)
    (hD0 : Tendsto (fun n ↦ ∫ ω, D n ω ∂μ) atTop (𝓝 0))
    (hdom : ∀ n, ∀ᵐ ω ∂μ, dist (f n ω) (g ω) ≤ K * Real.sqrt (D n ω)) :
    TendstoInMeasure μ f atTop g := by
  have hDmeasure : TendstoInMeasure μ D atTop (fun _ ↦ (0 : ℝ)) := by
    have hDeLp : Tendsto (fun n ↦ eLpNorm (D n - fun _ ↦ (0 : ℝ)) 1 μ) atTop (𝓝 0) := by
      have hrw : ∀ n, eLpNorm (D n - fun _ ↦ (0 : ℝ)) 1 μ = ENNReal.ofReal (∫ ω, D n ω ∂μ) := by
        intro n
        have hsub : (D n - fun _ ↦ (0 : ℝ)) = D n := by funext ω; simp
        have hlint : (∫⁻ ω, ‖D n ω‖ₑ ∂μ) = ∫⁻ ω, ENNReal.ofReal (D n ω) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hDnn n] with ω hω
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hω]
        rw [hsub, eLpNorm_one_eq_lintegral_enorm, hlint,
          ← ofReal_integral_eq_lintegral_ofReal (hDint n) (hDnn n)]
      rw [tendsto_congr hrw, ← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp hD0
    exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun n ↦ (hDint n).aestronglyMeasurable)
      aestronglyMeasurable_const hDeLp
  intro ε hε
  rcases eq_or_ne ε ⊤ with hεtop | hεtop
  · -- `ε = ⊤`: the difference has finite `edist`, so every level set is empty
    subst hεtop
    have hz : ∀ n, μ {ω | (⊤ : ℝ≥0∞) ≤ edist (f n ω) (g ω)} = 0 := by
      intro n
      have hset : {ω | (⊤ : ℝ≥0∞) ≤ edist (f n ω) (g ω)} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, top_le_iff]
        exact edist_ne_top _ _
      rw [hset]; exact measure_empty
    exact tendsto_const_nhds.congr fun n ↦ (hz n).symm
  · set r : ℝ := ε.toReal
    have hrpos : 0 < r := ENNReal.toReal_pos hε.ne' hεtop
    have hεr : ε = ENNReal.ofReal r := (ENNReal.ofReal_toReal hεtop).symm
    rcases eq_or_lt_of_le hK with hK0 | hKpos
    · -- `K = 0`: `dist ≤ 0` a.e., so `fₙ =ᵐ g`
      have hz : ∀ n, μ {ω | ε ≤ edist (f n ω) (g ω)} = 0 := by
        intro n
        refine le_antisymm ((measure_mono_ae ?_).trans_eq measure_empty) zero_le
        filter_upwards [hdom n] with ω hω hεle
        have hεle2 : ε ≤ edist (f n ω) (g ω) := hεle
        rw [hεr, edist_dist] at hεle2
        have hrd : r ≤ dist (f n ω) (g ω) := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hεle2
        exact absurd (hrd.trans (hω.trans_eq (by rw [← hK0, zero_mul]))) (not_le.mpr hrpos)
      exact tendsto_const_nhds.congr fun n ↦ (hz n).symm
    · -- `K > 0`: `r ≤ dist ≤ K√(Dₙ)` forces `Dₙ ≥ (r/K)²`, whose measure vanishes
      have hε'pos : (0 : ℝ≥0∞) < ENNReal.ofReal ((r / K) ^ 2) := ENNReal.ofReal_pos.mpr (by positivity)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hDmeasure (ENNReal.ofReal ((r / K) ^ 2)) hε'pos) (fun _ ↦ zero_le)
        (fun n ↦ measure_mono_ae ?_)
      filter_upwards [hdom n, hDnn n] with ω hω hωnn hεle
      have hεle2 : ε ≤ edist (f n ω) (g ω) := hεle
      rw [hεr, edist_dist] at hεle2
      have hrd : r ≤ dist (f n ω) (g ω) := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hεle2
      have hrK : r / K ≤ Real.sqrt (D n ω) := by
        rw [div_le_iff₀ hKpos, mul_comm]; exact hrd.trans hω
      have hsq : (r / K) ^ 2 ≤ D n ω := by
        have hss := Real.sq_sqrt hωnn
        nlinarith [Real.sqrt_nonneg (D n ω), hrK, div_nonneg hrpos.le hKpos.le, hss]
      show ENNReal.ofReal ((r / K) ^ 2) ≤ edist (D n ω) 0
      rw [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg hωnn]
      exact ENNReal.ofReal_le_ofReal hsq

/-- **Jensen for the square root** on a probability measure: `∫√D ≤ √(∫D)`, from finite-measure
Cauchy–Schwarz `(∫√D)² ≤ μ(univ)·∫(√D)² = ∫D`. -/
lemma integral_sqrt_le_sqrt_integral {D : Ω → ℝ} (hDnn : 0 ≤ᵐ[μ] D) (hDint : Integrable D μ) :
    ∫ ω, Real.sqrt (D ω) ∂μ ≤ Real.sqrt (∫ ω, D ω ∂μ) := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ Real.sqrt (D ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hDint.1
  have hsqeq : (fun ω ↦ (Real.sqrt (D ω)) ^ 2) =ᵐ[μ] D := by
    filter_upwards [hDnn] with ω hω; rw [Real.sq_sqrt hω]
  have hmem : MemLp (fun ω ↦ Real.sqrt (D ω)) 2 μ :=
    (memLp_two_iff_integrable_sq hmeas).mpr (hDint.congr hsqeq.symm)
  have hcs := sq_integral_le_measureReal_mul (ν := μ) hmem
  rw [measure_univ, ENNReal.toReal_one, one_mul, integral_congr_ae hsqeq] at hcs
  rw [← Real.sqrt_sq (integral_nonneg fun ω ↦ Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hcs

omit [IsProbabilityMeasure μ] in
/-- **`L¹` domination ⟹ convergence in measure.** If `dist(fₙ ω, g ω) ≤ hₙ ω` a.e. for an integrable
`hₙ` whose `μ`-mean vanishes, then `fₙ → g` in measure: the difference converges in `L¹(μ)`, whence in
measure. The `L¹`-form companion of `tendstoInMeasure_of_ae_dist_le_sqrt`, for a two-term dominator. -/
lemma tendstoInMeasure_of_ae_dist_le_of_tendsto_integral {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {h : ℕ → Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hhint : ∀ n, Integrable (h n) μ)
    (hdom : ∀ n, ∀ᵐ ω ∂μ, dist (f n ω) (g ω) ≤ h n ω)
    (hh0 : Tendsto (fun n ↦ ∫ ω, h n ω ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop g := by
  refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hf hg ?_
  have hbnd : ∀ n, eLpNorm (f n - g) 1 μ ≤ ENNReal.ofReal (∫ ω, h n ω ∂μ) := by
    intro n
    have hnn : 0 ≤ᵐ[μ] h n := by filter_upwards [hdom n] with ω hω; exact dist_nonneg.trans hω
    rw [eLpNorm_one_eq_lintegral_enorm]
    calc ∫⁻ ω, ‖(f n - g) ω‖ₑ ∂μ
        = ∫⁻ ω, ENNReal.ofReal (dist (f n ω) (g ω)) ∂μ := by
          refine lintegral_congr fun ω ↦ ?_
          rw [Pi.sub_apply, Real.enorm_eq_ofReal_abs, Real.dist_eq]
      _ ≤ ∫⁻ ω, ENNReal.ofReal (h n ω) ∂μ :=
          lintegral_mono_ae (by filter_upwards [hdom n] with ω hω; exact ENNReal.ofReal_le_ofReal hω)
      _ = ENNReal.ofReal (∫ ω, h n ω ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal (hhint n) hnn).symm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hbnd
  rw [← ENNReal.ofReal_zero]
  exact (ENNReal.continuous_ofReal.tendsto 0).comp hh0

/-- **The marshalled drifts converge in measure to the limit drift.** For a raw approximating
sequence `V n → θ̂` in the integrand `L²`, the elementary drifts `driftSimpleProcess (Ṽⁿ) u` of the
clamped marshalled approximants converge in `μ`-measure to the genuinely-`𝓕`-adapted limit drift
`driftContinuousMod θ̂ u` (a.e. the honest `∫₀ᵘθds`). The pathwise interval Cauchy–Schwarz
`|∫₀ᵘ(⇑Ṽⁿ − ⇑θ̂)|² ≤ u·∫₀ᵀ(⇑Ṽⁿ − ⇑θ̂)²` dominates the drift difference by `√(u·Dₙ)`, and the ω-slice
energy `Dₙ = ∫₀ᵀ(⇑Ṽⁿ − ⇑θ̂)²` decays in `L¹(μ)` (`= ‖simpleAssembly_T Ṽⁿ − θ̂‖² → 0`), hence in
measure. -/
lemma tendstoInMeasure_marshalDrift (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n ↦ simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd)))
    {u : ℝ≥0} (huT : u ≤ T) :
    TendstoInMeasure μ (fun n ↦ driftSimpleProcess hBmeas
        (marshalStepSP hBmeas T (V n).val (V n).property hC
          ((marshalEndpoints hBmeas T (V n).val).card - 1)).val u) atTop
      (driftContinuousMod T hBmeas (processToLpPredictable (μ := μ) T hBmeas hpred hbdd) u) := by
  set θhat := processToLpPredictable (μ := μ) T hBmeas hpred hbdd with hθhat
  set W : ℕ → TBoundedSP T hBmeas := fun n ↦ marshalStepSP hBmeas T (V n).val (V n).property hC
    ((marshalEndpoints hBmeas T (V n).val).card - 1) with hW
  haveI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) u)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  -- ω-slice energy `Dₙ` and its `L¹(μ)` decay
  set D : ℕ → Ω → ℝ := fun n ω ↦
    ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(W n).val s ω - ⇑θhat (s, ω)) ^ 2 ∂timeMeasure with hDdef
  have hDnn : ∀ n, 0 ≤ᵐ[μ] D n := fun n ↦ ae_of_all _ fun ω ↦ integral_nonneg fun s ↦ sq_nonneg _
  have hDint : ∀ n, Integrable (D n) μ :=
    fun n ↦ (drift_slice_sq_integrable T hBmeas θhat (W n)).integral_prod_right
  have hD0 : Tendsto (fun n ↦ ∫ ω, D n ω ∂μ) atTop (𝓝 0) := by
    have heq : ∀ n, (∫ ω, D n ω ∂μ) = ‖simpleAssembly_T (μ := μ) T hBmeas (W n) - θhat‖ ^ 2 :=
      fun n ↦ drift_slice_energy_eq T hBmeas θhat (W n)
    simp_rw [heq]
    have h0 : Tendsto (fun n ↦ ‖simpleAssembly_T (μ := μ) T hBmeas (W n) - θhat‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp
        (tendsto_simpleAssembly_marshalStepSP T hBmeas hpred hC hbdd V hV)
    simpa using h0.pow 2
  -- `θ̂` sliced is `L²` a.e.
  have hg_prod : MemLp (⇑θhat) 2 ((timeMeasure_T T).prod μ) :=
    ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim (natFiltration hBmeas).predictable_le_prod
      (Lp.aestronglyMeasurable θhat),
     by rw [← eLpNorm_trim_ae (natFiltration hBmeas).predictable_le_prod (Lp.aestronglyMeasurable θhat)]
        exact (Lp.memLp θhat).2⟩
  have hg_slice : ∀ᵐ ω ∂μ, MemLp (fun s ↦ ⇑θhat (s, ω)) 2 (timeMeasure_T T) := by
    filter_upwards [hg_prod.1.prodMk_right, hg_prod.integrable_sq.prod_left_ae] with ω hω1 hω2
    exact (memLp_two_iff_integrable_sq hω1).mpr hω2
  -- the honest limit-drift is a.e. the slice integral `∫₀ᵘ⇑θ̂ ds`
  have hlim_eq : ∀ᵐ ω ∂μ, driftContinuousMod T hBmeas θhat u ω
      = ∫ s in Set.Ioc (0 : ℝ≥0) u, ⇑θhat (s, ω) ∂timeMeasure :=
    driftContinuousMod_eq_setIntegral T hBmeas θhat huT
  -- pathwise domination of the drift difference by `√(u·Dₙ)`
  have hdom : ∀ n, ∀ᵐ ω ∂μ,
      dist (driftSimpleProcess hBmeas (W n).val u ω) (driftContinuousMod T hBmeas θhat u ω)
        ≤ Real.sqrt ((u : ℝ) * D n ω) := by
    intro n
    filter_upwards [hg_slice, hlim_eq] with ω hωg hωlim
    have hVt : MemLp (fun s ↦ ⇑(W n).val s ω) 2 (timeMeasure.restrict (Set.Ioc 0 u)) :=
      (memLp_slice T hBmeas (W n).val ω).mono_measure
        (Measure.restrict_mono (Set.Ioc_subset_Ioc_right huT) le_rfl)
    have hgt : MemLp (fun s ↦ ⇑θhat (s, ω)) 2 (timeMeasure.restrict (Set.Ioc 0 u)) :=
      hωg.mono_measure (Measure.restrict_mono (Set.Ioc_subset_Ioc_right huT) le_rfl)
    have hfT : MemLp (fun s ↦ ⇑(W n).val s ω - ⇑θhat (s, ω)) 2
        (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) := (memLp_slice T hBmeas (W n).val ω).sub hωg
    rw [Real.dist_eq, hωlim, driftSimpleProcess_eq_setIntegral, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    rw [← integral_sub (hVt.integrable (by norm_num)) (hgt.integrable (by norm_num))]
    calc (∫ s in Set.Ioc (0 : ℝ≥0) u, (⇑(W n).val s ω - ⇑θhat (s, ω)) ∂timeMeasure) ^ 2
        ≤ (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) u)).real Set.univ
            * ∫ s in Set.Ioc (0 : ℝ≥0) u, (⇑(W n).val s ω - ⇑θhat (s, ω)) ^ 2 ∂timeMeasure :=
          sq_integral_le_measureReal_mul (hVt.sub hgt)
      _ ≤ (u : ℝ) * D n ω := by
          rw [measureReal_def, Measure.restrict_apply_univ, timeMeasure_Ioc,
            ENNReal.toReal_ofReal (by rw [NNReal.coe_zero, sub_zero]; exact u.coe_nonneg),
            NNReal.coe_zero, sub_zero]
          exact mul_le_mul_of_nonneg_left
            (setIntegral_mono_set hfT.integrable_sq (ae_of_all _ fun s ↦ sq_nonneg _)
              (Set.Ioc_subset_Ioc_right huT).eventuallyLE) u.coe_nonneg
  refine tendstoInMeasure_of_ae_dist_le_sqrt (Real.sqrt_nonneg (u : ℝ)) hDnn hDint hD0 (fun n ↦ ?_)
  filter_upwards [hdom n] with ω hω
  rwa [Real.sqrt_mul u.coe_nonneg] at hω

/-- **The marshalled quadratic variations converge in measure to `∫₀ᵀθ² ds`.** For a raw
approximating sequence `V n → θ̂`, the discrete quadratic variations `∑ cᵢ²·Δτ` of the clamped
marshalled approximants (the drift half of the marshalled Doléans exponent) converge in `μ`-measure to
`∫₀ᵀ(⇑θ̂)² ds`. Writing `Q − L = 2∫step·(step − θ̂) − Dₙ` and using the deterministic bound `|step| ≤ C`
on `(0,T]`, `|Q − L| ≤ 2C√T·√(Dₙ) + Dₙ` (finite-measure `L¹ ≤ L²`), which vanishes in `L¹(μ)` since
`∫Dₙ = ‖simpleAssembly_T Ṽⁿ − θ̂‖² → 0` and `∫√Dₙ ≤ √(∫Dₙ)`. -/
lemma tendstoInMeasure_marshalQuadVar (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n ↦ simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) :
    TendstoInMeasure μ
      (fun n ↦ simpleQuadVar (marshalPart hBmeas T (V n).val)
        (fun i ω ↦ clampM C (marshalMult hBmeas T (V n).val i ω))
        ((marshalEndpoints hBmeas T (V n).val).card - 1) T)
      atTop
      (fun ω ↦ ∫ s in Set.Ioc (0 : ℝ≥0) T,
        (⇑(processToLpPredictable (μ := μ) T hBmeas hpred hbdd) (s, ω)) ^ 2 ∂timeMeasure) := by
  set θhat := processToLpPredictable (μ := μ) T hBmeas hpred hbdd with hθhat
  set W : ℕ → TBoundedSP T hBmeas := fun n ↦ marshalStepSP hBmeas T (V n).val (V n).property hC
    ((marshalEndpoints hBmeas T (V n).val).card - 1) with hW
  haveI hfin : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  set D : ℕ → Ω → ℝ := fun n ω ↦
    ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(W n).val s ω - ⇑θhat (s, ω)) ^ 2 ∂timeMeasure with hDdef
  have hDnn : ∀ n, 0 ≤ᵐ[μ] D n := fun n ↦ ae_of_all _ fun ω ↦ integral_nonneg fun s ↦ sq_nonneg _
  have hDint : ∀ n, Integrable (D n) μ :=
    fun n ↦ (drift_slice_sq_integrable T hBmeas θhat (W n)).integral_prod_right
  have hD0 : Tendsto (fun n ↦ ∫ ω, D n ω ∂μ) atTop (𝓝 0) := by
    have heq : ∀ n, (∫ ω, D n ω ∂μ) = ‖simpleAssembly_T (μ := μ) T hBmeas (W n) - θhat‖ ^ 2 :=
      fun n ↦ drift_slice_energy_eq T hBmeas θhat (W n)
    simp_rw [heq]
    have h0 : Tendsto (fun n ↦ ‖simpleAssembly_T (μ := μ) T hBmeas (W n) - θhat‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp
        (tendsto_simpleAssembly_marshalStepSP T hBmeas hpred hC hbdd V hV)
    simpa using h0.pow 2
  have hg_prod : MemLp (⇑θhat) 2 ((timeMeasure_T T).prod μ) :=
    ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim (natFiltration hBmeas).predictable_le_prod
      (Lp.aestronglyMeasurable θhat),
     by rw [← eLpNorm_trim_ae (natFiltration hBmeas).predictable_le_prod (Lp.aestronglyMeasurable θhat)]
        exact (Lp.memLp θhat).2⟩
  have hg_slice : ∀ᵐ ω ∂μ, MemLp (fun s ↦ ⇑θhat (s, ω)) 2 (timeMeasure_T T) := by
    filter_upwards [hg_prod.1.prodMk_right, hg_prod.integrable_sq.prod_left_ae] with ω hω1 hω2
    exact (memLp_two_iff_integrable_sq hω1).mpr hω2
  have hQmeas : ∀ n, AEStronglyMeasurable
      (fun ω ↦ simpleQuadVar (marshalPart hBmeas T (V n).val)
        (fun i ω ↦ clampM C (marshalMult hBmeas T (V n).val i ω))
        ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω) μ := by
    intro n
    refine Measurable.aestronglyMeasurable ?_
    unfold SimpleDoleansMoments.simpleQuadVar
    refine Finset.measurable_sum _ fun i _ ↦ ?_
    exact (((measurable_clampM_comp hBmeas
      (stronglyMeasurable_marshalMult hBmeas T (V n).val i).measurable).pow_const 2).mul_const _).mono
      ((natFiltration hBmeas).le _) le_rfl
  have hLmeas : AEStronglyMeasurable
      (fun ω ↦ ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑θhat (s, ω)) ^ 2 ∂timeMeasure) μ :=
    hg_prod.integrable_sq.swap.aestronglyMeasurable.integral_prod_right'
  -- the pointwise `|Q − L| ≤ 2C√T·√Dₙ + Dₙ` domination
  have hdom : ∀ n, ∀ᵐ ω ∂μ,
      dist (simpleQuadVar (marshalPart hBmeas T (V n).val)
          (fun i ω ↦ clampM C (marshalMult hBmeas T (V n).val i ω))
          ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω)
        (∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑θhat (s, ω)) ^ 2 ∂timeMeasure)
        ≤ 2 * C * Real.sqrt (T : ℝ) * Real.sqrt (D n ω) + D n ω := by
    intro n
    filter_upwards [hg_slice] with ω hωg
    have hmpN : marshalPart hBmeas T (V n).val ((marshalEndpoints hBmeas T (V n).val).card - 1) = T :=
      marshalPart_card_sub_one hBmeas T (V n).val (V n).property
    have hQeq : simpleQuadVar (marshalPart hBmeas T (V n).val)
        (fun i ω ↦ clampM C (marshalMult hBmeas T (V n).val i ω))
        ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω
        = ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(W n).val s ω) ^ 2 ∂timeMeasure :=
      simpleQuadVar_marshalStepSP_eq hBmeas T (V n).val (V n).property hC hmpN ω
    have hVt : MemLp (fun s ↦ ⇑(W n).val s ω) 2 (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
      memLp_slice T hBmeas (W n).val ω
    have hgt : MemLp (fun s ↦ ⇑θhat (s, ω)) 2 (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) := hωg
    have hstepbnd : ∀ s ∈ Set.Ioc (0 : ℝ≥0) T, |⇑(W n).val s ω| ≤ C := by
      intro s hs
      rw [show ⇑(W n).val s ω = Function.uncurry ⇑(W n).val (s, ω) from rfl,
        uncurry_marshalStepSP_eq_clamp hBmeas T (V n).val (V n).property hC hmpN hs.1 hs.2 ω]
      exact clampM_abs_le hC _
    -- decompose `∫(step² − θ̂²) = 2∫step·(step − θ̂) − ∫(step − θ̂)²`
    rw [Real.dist_eq, hQeq]
    have hdecomp : (∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(W n).val s ω) ^ 2 ∂timeMeasure)
        - ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑θhat (s, ω)) ^ 2 ∂timeMeasure
        = 2 * (∫ s in Set.Ioc (0 : ℝ≥0) T,
              ⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)) ∂timeMeasure) - D n ω := by
      have h1 : (∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(W n).val s ω) ^ 2 ∂timeMeasure)
          - ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑θhat (s, ω)) ^ 2 ∂timeMeasure
          = ∫ s in Set.Ioc (0 : ℝ≥0) T,
              (2 * (⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)))
                - (⇑(W n).val s ω - ⇑θhat (s, ω)) ^ 2) ∂timeMeasure := by
        rw [← integral_sub hVt.integrable_sq hgt.integrable_sq]
        exact integral_congr_ae (ae_of_all _ fun s ↦ by ring)
      have h2 : (∫ s in Set.Ioc (0 : ℝ≥0) T,
              (2 * (⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)))
                - (⇑(W n).val s ω - ⇑θhat (s, ω)) ^ 2) ∂timeMeasure)
          = 2 * (∫ s in Set.Ioc (0 : ℝ≥0) T,
              ⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)) ∂timeMeasure)
            - ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(W n).val s ω - ⇑θhat (s, ω)) ^ 2 ∂timeMeasure := by
        rw [integral_sub (f := fun s ↦ 2 * (⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω))))
            (g := fun s ↦ (⇑(W n).val s ω - ⇑θhat (s, ω)) ^ 2)
            ((((hVt.sub hgt).mul hVt).integrable le_rfl).const_mul 2) (hVt.sub hgt).integrable_sq,
          integral_const_mul]
      rw [h1, h2, hDdef]
    rw [hdecomp]
    have hCS : |∫ s in Set.Ioc (0 : ℝ≥0) T,
        ⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)) ∂timeMeasure|
        ≤ C * Real.sqrt (T : ℝ) * Real.sqrt (D n ω) := by
      have habs : |∫ s in Set.Ioc (0 : ℝ≥0) T,
          ⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)) ∂timeMeasure|
          ≤ ∫ s in Set.Ioc (0 : ℝ≥0) T,
            C * |⇑(W n).val s ω - ⇑θhat (s, ω)| ∂timeMeasure := by
        refine (abs_integral_le_integral_abs).trans ?_
        refine setIntegral_mono_on (((hVt.sub hgt).mul hVt).integrable le_rfl).abs
          (((hVt.sub hgt).integrable one_le_two).abs.const_mul C) measurableSet_Ioc
          (fun s hs ↦ ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hstepbnd s hs) (abs_nonneg _)
      have hL1L2 : ∫ s in Set.Ioc (0 : ℝ≥0) T, |⇑(W n).val s ω - ⇑θhat (s, ω)| ∂timeMeasure
          ≤ Real.sqrt (T : ℝ) * Real.sqrt (D n ω) := by
        rw [← Real.sqrt_mul T.coe_nonneg (D n ω),
          ← Real.sqrt_sq (integral_nonneg fun s ↦ abs_nonneg _)]
        refine Real.sqrt_le_sqrt ?_
        have hcs := sq_integral_le_measureReal_mul (ν := timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T))
          (hVt.sub hgt).abs
        rw [Measure.restrict_apply_univ, timeMeasure_Ioc,
          ENNReal.toReal_ofReal (by rw [NNReal.coe_zero, sub_zero]; exact T.coe_nonneg),
          NNReal.coe_zero, sub_zero] at hcs
        refine hcs.trans_eq ?_
        rw [hDdef]
        refine congrArg (fun z ↦ (T : ℝ) * z) (integral_congr_ae (ae_of_all _ fun s ↦ ?_))
        simp only [Pi.abs_apply, Pi.sub_apply, sq_abs]
      calc |∫ s in Set.Ioc (0 : ℝ≥0) T,
              ⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)) ∂timeMeasure|
          ≤ ∫ s in Set.Ioc (0 : ℝ≥0) T, C * |⇑(W n).val s ω - ⇑θhat (s, ω)| ∂timeMeasure := habs
        _ = C * ∫ s in Set.Ioc (0 : ℝ≥0) T, |⇑(W n).val s ω - ⇑θhat (s, ω)| ∂timeMeasure :=
            integral_const_mul _ _
        _ ≤ C * (Real.sqrt (T : ℝ) * Real.sqrt (D n ω)) := mul_le_mul_of_nonneg_left hL1L2 hC
        _ = C * Real.sqrt (T : ℝ) * Real.sqrt (D n ω) := by ring
    have hDeq : |D n ω| = D n ω := abs_of_nonneg (integral_nonneg fun s ↦ sq_nonneg _)
    calc |2 * (∫ s in Set.Ioc (0 : ℝ≥0) T,
            ⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)) ∂timeMeasure) - D n ω|
        ≤ 2 * |∫ s in Set.Ioc (0 : ℝ≥0) T,
            ⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)) ∂timeMeasure| + D n ω := by
          refine (abs_sub _ _).trans (le_of_eq ?_); rw [abs_mul, abs_two, hDeq]
      _ ≤ 2 * (C * Real.sqrt (T : ℝ) * Real.sqrt (D n ω)) + D n ω := by gcongr
      _ = 2 * C * Real.sqrt (T : ℝ) * Real.sqrt (D n ω) + D n ω := by ring
  have hsqrtint : ∀ n, Integrable (fun ω ↦ Real.sqrt (D n ω)) μ := by
    intro n
    have hpt : ∀ ω, 0 ≤ D n ω := fun ω ↦ integral_nonneg fun s ↦ sq_nonneg _
    refine Integrable.mono' ((hDint n).add (integrable_const (1 : ℝ)))
      (Real.continuous_sqrt.comp_aestronglyMeasurable (hDint n).1) (ae_of_all _ fun ω ↦ ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [sq_nonneg (Real.sqrt (D n ω) - 1), Real.sq_sqrt (hpt ω), Real.sqrt_nonneg (D n ω),
      hpt ω]
  refine tendstoInMeasure_of_ae_dist_le_of_tendsto_integral hQmeas hLmeas
    (fun n ↦ ((hsqrtint n).const_mul (2 * C * Real.sqrt (T : ℝ))).add (hDint n)) hdom ?_
  have hbnd : ∀ n, (∫ ω, (2 * C * Real.sqrt (T : ℝ) * Real.sqrt (D n ω) + D n ω) ∂μ)
      ≤ 2 * C * Real.sqrt (T : ℝ) * Real.sqrt (∫ ω, D n ω ∂μ) + ∫ ω, D n ω ∂μ := by
    intro n
    have hcf : (0 : ℝ) ≤ 2 * C * Real.sqrt (T : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hC) (Real.sqrt_nonneg _)
    rw [integral_add ((hsqrtint n).const_mul _) (hDint n), integral_const_mul]
    gcongr
    exact integral_sqrt_le_sqrt_integral (hDnn n) (hDint n)
  have hg0 : Tendsto (fun n ↦ 2 * C * Real.sqrt (T : ℝ) * Real.sqrt (∫ ω, D n ω ∂μ)
      + ∫ ω, D n ω ∂μ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ Real.sqrt (∫ ω, D n ω ∂μ)) atTop (𝓝 0) := by
      rw [← Real.sqrt_zero]; exact (Real.continuous_sqrt.tendsto 0).comp hD0
    simpa using (h1.const_mul (2 * C * Real.sqrt (T : ℝ))).add hD0
  refine squeeze_zero (fun n ↦ integral_nonneg fun ω ↦ ?_) hbnd hg0
  exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)) (integral_nonneg fun s ↦ sq_nonneg _)

omit [IsProbabilityMeasure μ] in
/-- **Common a.e.-subsequence from two convergences in measure.** Given `f → F` and `g → G` in
measure and any subsequence `ns`, a single further subsequence `ms` makes *both* `f (ns (ms ·)) → F`
and `g (ns (ms ·)) → G` a.e.: extract an a.e.-subsequence for `f` along `ns`, then a further one for
`g` along `ns ∘ ms₁`; `f`'s a.e. limit survives restriction to the second subsequence. This is the
diagonal that lets the predictable Doléans limit read `Zⁿ = exp(−stochⁿ − ½quadⁿ)` at the common
a.e. limit. -/
lemma exists_subseq_tendsto_ae₂ {f g : ℕ → Ω → ℝ} {F G : Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop F) (hg : TendstoInMeasure μ g atTop G)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      (∀ᵐ ω ∂μ, Tendsto (fun k ↦ f (ns (ms k)) ω) atTop (𝓝 (F ω)))
      ∧ (∀ᵐ ω ∂μ, Tendsto (fun k ↦ g (ns (ms k)) ω) atTop (𝓝 (G ω))) := by
  obtain ⟨a, ha, hfa⟩ := (show TendstoInMeasure μ (fun k ↦ f (ns k)) atTop F from
    fun ε hε ↦ (hf ε hε).comp hns).exists_seq_tendsto_ae
  obtain ⟨b, hb, hgb⟩ := (show TendstoInMeasure μ (fun k ↦ g (ns (a k))) atTop G from
    fun ε hε ↦ (hg ε hε).comp (hns.comp ha.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨a ∘ b, ha.comp hb, ?_, hgb⟩
  filter_upwards [hfa] with ω hω
  exact hω.comp hb.tendsto_atTop

end Convergence

/-! ## The predictable-θ assembly: limit objects and the `Q`-Brownian conclusion -/

section Assembly

variable {μ : Measure Ω} [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ)

/-- The predictable Itô integral `∫₀ᵀ θ dB` as a genuine function — a chosen `Lp`-representative of the
CLM value `itoIntegralCLM_T θ̂`. Predictable analogue of `itoIntCont`. -/
noncomputable def itoIntPred (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) :
    Ω → ℝ :=
  ⇑(itoIntegralCLM_T hB T hBmeas (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))

/-- The predictable limit Doléans density `Z_T = exp(−∫₀ᵀθdB − ½∫₀ᵀθ̂²ds)` — the `contDoleansExp` of
the predictable Itô integral and the sliced `L²` integrand realization `θ̂`. -/
noncomputable def ZTpred (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) :
    Ω → ℝ :=
  contDoleansExp (itoIntPred hB T hBmeas hpred hbdd)
    (fun s ω ↦ ⇑(processToLpPredictable (μ := μ) T hBmeas hpred hbdd) (s, ω)) T

/-- The predictable drift-corrected process `B^θ_u = B_u + driftContinuousMod θ̂ u` — `driftContinuousMod`
is the genuinely-`𝓕`-adapted modification of the honest drift `∫₀ᵘθ ds`. -/
noncomputable def BthetaPred (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C)
    (u : ℝ≥0) (ω : Ω) : ℝ :=
  B u ω + driftContinuousMod T hBmeas (processToLpPredictable (μ := μ) T hBmeas hpred hbdd) u ω

omit hB in
/-- **Bridge: the marshalled stochastic sum is the elementary Itô sum of the step process.** With all
marshalled partition points `≤ T`, the clamps `min(sⱼ,T)` in `simpleStochSum` drop, so it equals
`itoSimple (marshalStepSP)` (`∑ clampM·ΔB`). This routes the stochastic exponent into the marshalled
Itô convergence `tendstoInMeasure_marshalStochSum`. -/
lemma simpleStochSum_marshalStepSP_eq (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hmpN : marshalPart hBmeas T V N = T) (ω : Ω) :
    simpleStochSum (X := B) (marshalPart hBmeas T V)
        (fun i ω ↦ clampM C (marshalMult hBmeas T V i ω)) N T ω
      = itoSimple hBmeas (marshalStepSP hBmeas T V hle hC N).val ω := by
  rw [itoSimple_marshalStepSP, simpleStochSum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hmono := marshalPart_mono hBmeas T V hle
  rw [min_eq_left (le_trans (hmono (Finset.mem_range.mp hi)) hmpN.le),
    min_eq_left (le_trans (hmono (le_of_lt (Finset.mem_range.mp hi))) hmpN.le)]

/-- **The approximant densities converge a.e. along subsequences to `Z_T`.** For every subsequence
`ns`, a further subsequence `ms` has `Zⁿ_T → Z_T` a.e.: `exists_subseq_tendsto_ae₂` fuses the stochastic
exponent's convergence (`tendstoInMeasure_marshalStochSum`, bridged to `simpleStochSum`) with the
quadratic variation's (`tendstoInMeasure_marshalQuadVar`), and `exp(−· − ½·)` (`simpleDoleansExp_neg_eq`)
is pushed to the common a.e. limit. Predictable analogue of `tendsto_Zn_ae_subseq`. -/
lemma tendsto_ZTpred_ae_subseq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n ↦ simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd)))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ ω ∂μ, Tendsto (fun k ↦
        simpleDoleansExp (X := B) (marshalPart hBmeas T (V (ns (ms k))).val)
          (fun i ω ↦ -(clampM C (marshalMult hBmeas T (V (ns (ms k))).val i ω)))
          ((marshalEndpoints hBmeas T (V (ns (ms k))).val).card - 1) T ω) atTop
      (𝓝 (ZTpred hB T hBmeas hpred hbdd ω)) := by
  set θhat := processToLpPredictable (μ := μ) T hBmeas hpred hbdd with hθhat
  set N : ℕ → ℕ := fun n ↦ (marshalEndpoints hBmeas T (V n).val).card - 1
  have hmpN : ∀ n, marshalPart hBmeas T (V n).val (N n) = T :=
    fun n ↦ marshalPart_card_sub_one hBmeas T (V n).val (V n).property
  -- stochastic exponent → `∫θdB` in measure (bridged from `itoSimple`)
  have hstoch : TendstoInMeasure μ (fun n ↦ simpleStochSum (X := B)
      (marshalPart hBmeas T (V n).val)
      (fun i ω ↦ clampM C (marshalMult hBmeas T (V n).val i ω)) (N n) T) atTop
      (⇑(itoIntegralCLM_T hB T hBmeas θhat)) := by
    refine tendstoInMeasure_congr_left (fun n ↦ ?_)
      (tendstoInMeasure_marshalStochSum hB T hBmeas hpred hC hbdd V hV)
    exact ae_of_all _ fun ω ↦
      (simpleStochSum_marshalStepSP_eq hBmeas T (V n).val (V n).property hC (hmpN n) ω).symm
  -- quadratic variation → `∫θ̂²` in measure
  have hquad : TendstoInMeasure μ (fun n ↦ simpleQuadVar (marshalPart hBmeas T (V n).val)
      (fun i ω ↦ clampM C (marshalMult hBmeas T (V n).val i ω)) (N n) T) atTop
      (fun ω ↦ ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑θhat (s, ω)) ^ 2 ∂timeMeasure) :=
    tendstoInMeasure_marshalQuadVar T hBmeas hpred hC hbdd V hV
  obtain ⟨ms, hms, hstochae, hquadae⟩ := exists_subseq_tendsto_ae₂ hstoch hquad ns hns
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hstochae, hquadae] with ω hωs hωq
  have hZeq : ZTpred hB T hBmeas hpred hbdd ω
      = Real.exp (-(⇑(itoIntegralCLM_T hB T hBmeas θhat) ω)
        - 2⁻¹ * ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑θhat (s, ω)) ^ 2 ∂timeMeasure) := by
    simp only [ZTpred, contDoleansExp, itoIntPred, ← hθhat]
  rw [hZeq]
  refine ((Real.continuous_exp.tendsto _).comp ((hωs.neg).sub (hωq.const_mul (2⁻¹ : ℝ)))).congr
    (fun k ↦ ?_)
  simp only [Function.comp_def]
  exact (SimpleDoleansMoments.simpleDoleansExp_neg_eq (X := B)
    (marshalPart hBmeas T (V (ns (ms k))).val)
    (fun i ω ↦ clampM C (marshalMult hBmeas T (V (ns (ms k))).val i ω))
    (N (ns (ms k))) T ω).symm

/-! ### The clamped-multiplier side conditions and the limit-density `L²`/`L¹`/mean facts -/

omit hB in
/-- The clamped marshalled multiplier `clampM C ∘ (marshalMult V)ᵢ` is `𝓕_{sᵢ}`-adapted (`clampM C`
continuous, `marshalMult` adapted) — the `hc` side condition of the simple-Doléans moment bounds. -/
lemma stronglyMeasurable_clampM_marshalMult (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) {C : ℝ}
    (V : TBoundedSP T hBmeas) (i : ℕ) :
    StronglyMeasurable[(natFiltration hBmeas (marshalPart hBmeas T V.val i) : MeasurableSpace Ω)]
      (fun ω ↦ clampM C (marshalMult hBmeas T V.val i ω)) :=
  (show Continuous (clampM C) by unfold clampM; fun_prop).comp_stronglyMeasurable
    (stronglyMeasurable_marshalMult hBmeas T V.val i)

omit hB in
/-- `|clampM C ∘ (marshalMult V)ᵢ| ≤ C`, the `hc_bdd` side condition. -/
lemma clampM_marshalMult_abs_le {C : ℝ} (hC : 0 ≤ C) (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : TBoundedSP T hBmeas) (i : ℕ) (ω : Ω) :
    |clampM C (marshalMult hBmeas T V.val i ω)| ≤ C := clampM_abs_le hC _

include hB in
/-- **The predictable limit density is in `L²`.** Fatou (`memLp_two_of_subseq_ae_of_sq_bound`) on the
approximant densities: each `Zⁿ ∈ L²` (`memLp_simpleDoleans_two`), `∫(Zⁿ)² ≤ exp(C²T)`
(`sq_integral_simpleDoleans_le`), and `Zⁿ → Z_T` a.e. along a subsequence (`tendsto_ZTpred_ae_subseq`). -/
lemma memLp_ZTpred_two (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n ↦ simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) :
    MemLp (ZTpred hB T hBmeas hpred hbdd) 2 μ := by
  haveI hFB : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  refine memLp_two_of_subseq_ae_of_sq_bound (f := fun n ω ↦
      simpleDoleansExp (X := B) (marshalPart hBmeas T (V n).val)
        (fun i ω ↦ -(clampM C (marshalMult hBmeas T (V n).val i ω)))
        ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω)
    (fun n ↦ SimpleDoleansMoments.memLp_simpleDoleans_two (X := B) (P := μ)
      (𝓕 := natFiltration hBmeas) (marshalPart_mono hBmeas T (V n).val (V n).property)
      (marshalPart_zero hBmeas T (V n).val (V n).property)
      (stronglyMeasurable_clampM_marshalMult hBmeas T (V n)) (clampM_marshalMult_abs_le hC hBmeas T (V n))
      _ (marshalPart_card_sub_one hBmeas T (V n).val (V n).property).ge)
    (fun n ↦ SimpleDoleansMoments.measurable_simpleDoleans (X := B) (P := μ)
      (𝓕 := natFiltration hBmeas) (marshalPart_mono hBmeas T (V n).val (V n).property)
      (stronglyMeasurable_clampM_marshalMult hBmeas T (V n)) (clampM_marshalMult_abs_le hC hBmeas T (V n)) _ T)
    (M := Real.exp (C ^ 2 * (T : ℝ)))
    (fun n ↦ SimpleDoleansMoments.sq_integral_simpleDoleans_le (X := B) (P := μ)
      (𝓕 := natFiltration hBmeas) (marshalPart_mono hBmeas T (V n).val (V n).property)
      (marshalPart_zero hBmeas T (V n).val (V n).property)
      (stronglyMeasurable_clampM_marshalMult hBmeas T (V n)) (clampM_marshalMult_abs_le hC hBmeas T (V n))
      _ (marshalPart_card_sub_one hBmeas T (V n).val (V n).property).ge) ?_
  obtain ⟨ms, _, hae⟩ := tendsto_ZTpred_ae_subseq hB T hBmeas hpred hC hbdd V hV id tendsto_id
  simp only [id_eq] at hae
  exact ⟨ms, hae⟩

include hB in
/-- **The predictable limit density is in `L¹`** (`L² ⊆ L¹` on the probability measure). -/
lemma memLp_ZTpred_one (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n ↦ simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) :
    MemLp (ZTpred hB T hBmeas hpred hbdd) 1 μ :=
  (memLp_ZTpred_two hB hBmeas T hpred hC hbdd V hV).mono_exponent (by norm_num)

include hB in
/-- **The mixed-time product converges to `g = D_u·Z_T` a.e. along a subsequence (the engine's `hsub`).**
Refine the density a.e.-subsequence (`tendsto_ZTpred_ae_subseq`) by the marshalled drift's convergence
in measure (`tendstoInMeasure_marshalDrift`, bridged to `simpleDrift`): a further subsequence makes the
drift converge a.e. too, then `exp(a·(B + drift) − ½a²·)·Zⁿ` converges to `exp(a·B^θ − ½a²·)·Z_T` a.e. -/
lemma tendsto_fnPred_ae_subseq (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n ↦ simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd)))
    (a : ℝ) {u : ℝ≥0} (huT : u ≤ T) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, ∀ᵐ ω ∂μ, Tendsto (fun k ↦
        Real.exp (a * (B u ω + simpleDrift (marshalPart hBmeas T (V (ns (ms k))).val)
          (fun i ω ↦ clampM C (marshalMult hBmeas T (V (ns (ms k))).val i ω))
          ((marshalEndpoints hBmeas T (V (ns (ms k))).val).card - 1) u ω) - a ^ 2 * (u : ℝ) / 2)
        * simpleDoleansExp (X := B) (marshalPart hBmeas T (V (ns (ms k))).val)
          (fun i ω ↦ -(clampM C (marshalMult hBmeas T (V (ns (ms k))).val i ω)))
          ((marshalEndpoints hBmeas T (V (ns (ms k))).val).card - 1) T ω) atTop
      (𝓝 (Real.exp (a * BthetaPred (μ := μ) T hBmeas hpred hbdd u ω - a ^ 2 * (u : ℝ) / 2)
        * ZTpred hB T hBmeas hpred hbdd ω)) := by
  obtain ⟨ms', hms', hZae⟩ := tendsto_ZTpred_ae_subseq hB T hBmeas hpred hC hbdd V hV ns hns
  have hdrift : TendstoInMeasure μ (fun n ↦ simpleDrift (marshalPart hBmeas T (V n).val)
      (fun i ω ↦ clampM C (marshalMult hBmeas T (V n).val i ω))
      ((marshalEndpoints hBmeas T (V n).val).card - 1) u) atTop
      (driftContinuousMod T hBmeas (processToLpPredictable (μ := μ) T hBmeas hpred hbdd) u) := by
    refine tendstoInMeasure_congr_left (fun n ↦ ?_)
      (tendstoInMeasure_marshalDrift T hBmeas hpred hC hbdd V hV huT)
    exact ae_of_all _ fun ω ↦ (simpleDrift_marshalStepSP_eq hBmeas T (V n).val (V n).property hC
      ((marshalEndpoints hBmeas T (V n).val).card - 1) u ω).symm
  obtain ⟨b, hb, hDae⟩ := (show TendstoInMeasure μ (fun k ↦
      simpleDrift (marshalPart hBmeas T (V (ns (ms' k))).val)
        (fun i ω ↦ clampM C (marshalMult hBmeas T (V (ns (ms' k))).val i ω))
        ((marshalEndpoints hBmeas T (V (ns (ms' k))).val).card - 1) u) atTop
      (driftContinuousMod T hBmeas (processToLpPredictable (μ := μ) T hBmeas hpred hbdd) u) from
    fun ε hε ↦ (hdrift ε hε).comp (hns.comp hms'.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨fun k ↦ ms' (b k), ?_⟩
  filter_upwards [hZae, hDae] with ω hZω hDω
  have hZ := hZω.comp hb.tendsto_atTop
  have hD : Tendsto (fun k ↦ Real.exp (a * (B u ω
      + simpleDrift (marshalPart hBmeas T (V (ns (ms' (b k)))).val)
        (fun i ω ↦ clampM C (marshalMult hBmeas T (V (ns (ms' (b k)))).val i ω))
        ((marshalEndpoints hBmeas T (V (ns (ms' (b k)))).val).card - 1) u ω)
      - a ^ 2 * (u : ℝ) / 2)) atTop
      (𝓝 (Real.exp (a * BthetaPred (μ := μ) T hBmeas hpred hbdd u ω - a ^ 2 * (u : ℝ) / 2))) :=
    (Real.continuous_exp.tendsto _).comp (((hDω.const_add (B u ω)).const_mul a).sub_const _)
  exact hD.mul hZ

include hB in
/-- **The limit `g = D_u·Z_T` is in `L¹`.** Fatou (`memLp_two_of_subseq_ae_of_sq_bound`) gives
`g ∈ L²` from the mixed-product `L²` membership + uniform second moment (`memLp_mixedProduct_two`,
`sq_integral_mixedProduct_le`) and the product a.e.-subsequence (`tendsto_fnPred_ae_subseq`), then
`L² ⊆ L¹`. Predictable analogue of `memLp_g_one`. -/
lemma memLp_gpred_one (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n ↦ simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd)))
    (a : ℝ) {u : ℝ≥0} (huT : u ≤ T) :
    MemLp (fun ω ↦ Real.exp (a * BthetaPred (μ := μ) T hBmeas hpred hbdd u ω - a ^ 2 * (u : ℝ) / 2)
      * ZTpred hB T hBmeas hpred hbdd ω) 1 μ := by
  haveI hFB : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  refine (memLp_two_of_subseq_ae_of_sq_bound (f := fun n ω ↦
      Real.exp (a * (B u ω + simpleDrift (marshalPart hBmeas T (V n).val)
        (fun i ω ↦ clampM C (marshalMult hBmeas T (V n).val i ω))
        ((marshalEndpoints hBmeas T (V n).val).card - 1) u ω) - a ^ 2 * (u : ℝ) / 2)
      * simpleDoleansExp (X := B) (marshalPart hBmeas T (V n).val)
        (fun i ω ↦ -(clampM C (marshalMult hBmeas T (V n).val i ω)))
        ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω)
    (fun n ↦ SimpleDoleansMoments.memLp_mixedProduct_two (X := B) (P := μ)
      (𝓕 := natFiltration hBmeas) (marshalPart_mono hBmeas T (V n).val (V n).property)
      (marshalPart_zero hBmeas T (V n).val (V n).property)
      (stronglyMeasurable_clampM_marshalMult hBmeas T (V n)) (clampM_marshalMult_abs_le hC hBmeas T (V n))
      a _ huT (marshalPart_card_sub_one hBmeas T (V n).val (V n).property).ge)
    (fun n ↦ (SimpleDoleansMoments.measurable_driftExp (X := B) (P := μ) (𝓕 := natFiltration hBmeas)
      (marshalPart_mono hBmeas T (V n).val (V n).property)
      (stronglyMeasurable_clampM_marshalMult hBmeas T (V n)) a _ u).mul
      (SimpleDoleansMoments.measurable_simpleDoleans (X := B) (P := μ) (𝓕 := natFiltration hBmeas)
        (marshalPart_mono hBmeas T (V n).val (V n).property)
        (stronglyMeasurable_clampM_marshalMult hBmeas T (V n)) (clampM_marshalMult_abs_le hC hBmeas T (V n)) _ T))
    (M := 2⁻¹ * (Real.exp (4 * |a| * C * (T : ℝ)) * (∫ ω, Real.exp (4 * a * B u ω) ∂μ)
        + Real.exp (6 * C ^ 2 * (T : ℝ))))
    (fun n ↦ SimpleDoleansMoments.sq_integral_mixedProduct_le (X := B) (P := μ)
      (𝓕 := natFiltration hBmeas) (marshalPart_mono hBmeas T (V n).val (V n).property)
      (marshalPart_zero hBmeas T (V n).val (V n).property)
      (stronglyMeasurable_clampM_marshalMult hBmeas T (V n)) (clampM_marshalMult_abs_le hC hBmeas T (V n))
      a _ huT (marshalPart_card_sub_one hBmeas T (V n).val (V n).property).ge)
    (tendsto_fnPred_ae_subseq hB hBmeas T hpred hC hbdd V hV a huT id tendsto_id
      |>.imp fun ms hms ↦ by simpa only [id_eq] using hms)).mono_exponent (by norm_num)

include hB in
/-- **Unit mean of the predictable limit density: `∫ Z_T = 1`.** The a.e.-subsequence engine gives
`∫ Zⁿ → ∫ Z_T`, and `∫ Zⁿ = 1` (`simpleDoleansExp_integral_eq_one`), so the limit is `1`. -/
lemma integral_ZTpred_eq_one (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n ↦ simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) :
    ∫ ω, ZTpred hB T hBmeas hpred hbdd ω ∂μ = 1 := by
  haveI hFB : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  have hone : ∀ n, ∫ ω, simpleDoleansExp (X := B) (marshalPart hBmeas T (V n).val)
      (fun i ω ↦ -(clampM C (marshalMult hBmeas T (V n).val i ω)))
      ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω ∂μ = 1 := fun n ↦
    simpleDoleansExp_integral_eq_one (X := B)
      (marshalPart hBmeas T (V n).val) (marshalPart_mono hBmeas T (V n).val (V n).property)
      (fun i ω ↦ -(clampM C (marshalMult hBmeas T (V n).val i ω)))
      (fun i ↦ (stronglyMeasurable_clampM_marshalMult hBmeas T (V n) i).neg)
      (fun i ω ↦ by rw [abs_neg]; exact clampM_marshalMult_abs_le hC hBmeas T (V n) i ω)
      ((marshalEndpoints hBmeas T (V n).val).card - 1) T
  have hlim := tendsto_setIntegral_of_subseq_ae_of_sq_bound (f := fun n ω ↦
      simpleDoleansExp (X := B) (marshalPart hBmeas T (V n).val)
        (fun i ω ↦ -(clampM C (marshalMult hBmeas T (V n).val i ω)))
        ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω)
    (fun n ↦ SimpleDoleansMoments.memLp_simpleDoleans_two (X := B) (P := μ)
      (𝓕 := natFiltration hBmeas) (marshalPart_mono hBmeas T (V n).val (V n).property)
      (marshalPart_zero hBmeas T (V n).val (V n).property)
      (stronglyMeasurable_clampM_marshalMult hBmeas T (V n)) (clampM_marshalMult_abs_le hC hBmeas T (V n))
      _ (marshalPart_card_sub_one hBmeas T (V n).val (V n).property).ge)
    (M := Real.exp (C ^ 2 * (T : ℝ)))
    (fun n ↦ SimpleDoleansMoments.sq_integral_simpleDoleans_le (X := B) (P := μ)
      (𝓕 := natFiltration hBmeas) (marshalPart_mono hBmeas T (V n).val (V n).property)
      (marshalPart_zero hBmeas T (V n).val (V n).property)
      (stronglyMeasurable_clampM_marshalMult hBmeas T (V n)) (clampM_marshalMult_abs_le hC hBmeas T (V n))
      _ (marshalPart_card_sub_one hBmeas T (V n).val (V n).property).ge)
    (memLp_ZTpred_one hB hBmeas T hpred hC hbdd V hV)
    (fun ns hns ↦ (tendsto_ZTpred_ae_subseq hB T hBmeas hpred hC hbdd V hV ns hns).imp
      fun ms h ↦ h.2) Set.univ
  simp only [setIntegral_univ, hone] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

include hB in
/-- **The predictable Girsanov measure is a probability measure.** `Q = μ.withDensity(Z_T)` with the
positive, unit-mean, `L¹` density `Z_T`. -/
lemma isProbabilityMeasure_predGirsanov (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n ↦ simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) :
    IsProbabilityMeasure (μ.withDensity fun ω ↦
      ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((memLp_ZTpred_one hB hBmeas T hpred hC hbdd V hV).integrable le_rfl)
      (ae_of_all _ fun ω ↦ (contDoleansExp_pos _ _ _ _).le),
    integral_ZTpred_eq_one hB hBmeas T hpred hC hbdd V hV, ENNReal.ofReal_one]

/-! ### The exponential-martingale data and the `Q`-Brownian conclusion -/

include hB in
/-- **Predictable bounded-θ exponential-martingale data.** For a bounded (`|θ| ≤ C`) predictable market
price of risk `θ` — the honest domain of the Itô `L²` integral — under `Q = μ.withDensity(Z_T)` with the
Doléans density `Z_T = exp(−∫₀ᵀθdB − ½∫₀ᵀθ²ds)`, the drift-corrected process
`B^θ_u = B_u + driftContinuousMod θ̂ u` is `𝓕`-adapted, starts at `0` a.e. `Q`, and every
`exp(a·B^θ − ½a²·)` is a `Q`-martingale on `[0,T]`. The martingale field is the limit of the simple-θ
identity (`isExpQMartingale_BthetaSimple` on the clamped marshalled approximants `Ṽⁿ`): transported to
`μ`, both sides pass through the a.e.-subsequence engine (`tendsto_setIntegral_of_subseq_ae_of_sq_bound`),
and the simple identity forces the limits equal. Predictable analogue of `isExpQMartingale_BthetaCont`,
with the marshalled density-approximation front half in place of the uniform grid. -/
theorem isExpQMartingale_BthetaPredictable (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n ↦ simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) :
    IsExpQMartingale (μ.withDensity fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω))
      (natFiltration hBmeas) (BthetaPred (μ := μ) T hBmeas hpred hbdd) T := by
  haveI hFB : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  have hZTaesm : AEStronglyMeasurable (ZTpred hB T hBmeas hpred hbdd) μ :=
    (memLp_ZTpred_one hB hBmeas T hpred hC hbdd V hV).1
  have hZTpos : ∀ ω, 0 ≤ ZTpred hB T hBmeas hpred hbdd ω := fun ω ↦ (contDoleansExp_pos _ _ _ _).le
  have hB0 : ∀ᵐ ω ∂μ, B 0 ω = 0 := by
    have hmap := Measure.map_apply (μ := μ) (hBmeas 0) (measurableSet_singleton (0 : ℝ)).compl
    rw [(hFB.hasLaw_eval 0).map_eq, gaussianReal_zero_var,
      Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl] at hmap
    rw [show B 0 ⁻¹' {(0 : ℝ)}ᶜ = {ω | B 0 ω ≠ 0} from by ext ω; simp [Set.mem_preimage]] at hmap
    exact ae_iff.mpr (by simpa using hmap.symm)
  have hdrift0 : ∀ᵐ ω ∂μ, driftContinuousMod T hBmeas
      (processToLpPredictable (μ := μ) T hBmeas hpred hbdd) 0 ω = 0 := by
    filter_upwards [driftContinuousMod_eq_setIntegral T hBmeas
      (processToLpPredictable (μ := μ) T hBmeas hpred hbdd) (zero_le : (0 : ℝ≥0) ≤ T)] with ω hω
    rw [hω]; simp
  refine ⟨fun u ↦ (hFB.stronglyAdapted u).add (driftContinuousMod_stronglyAdapted T hBmeas
    (processToLpPredictable (μ := μ) T hBmeas hpred hbdd) u), ?_, ?_⟩
  · filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le hB0,
      (withDensity_absolutelyContinuous _ _).ae_le hdrift0] with ω hω hωd
    simp only [BthetaPred, Pi.zero_apply, hω, hωd, add_zero]
  · intro a s' t' hst' ht'T A hA
    have hAmΩ : MeasurableSet A := (natFiltration hBmeas).le s' A hA
    have engine : ∀ (u : ℝ≥0), u ≤ T →
        Tendsto (fun n ↦ ∫ ω in A, (Real.exp (a * (B u ω
            + simpleDrift (marshalPart hBmeas T (V n).val)
              (fun i ω ↦ clampM C (marshalMult hBmeas T (V n).val i ω))
              ((marshalEndpoints hBmeas T (V n).val).card - 1) u ω) - a ^ 2 * (u : ℝ) / 2)
          * simpleDoleansExp (X := B) (marshalPart hBmeas T (V n).val)
              (fun i ω ↦ -(clampM C (marshalMult hBmeas T (V n).val i ω)))
              ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω) ∂μ) atTop
          (𝓝 (∫ ω in A, (Real.exp (a * BthetaPred (μ := μ) T hBmeas hpred hbdd u ω - a ^ 2 * (u : ℝ) / 2)
            * ZTpred hB T hBmeas hpred hbdd ω) ∂μ)) := fun u huT ↦
      tendsto_setIntegral_of_subseq_ae_of_sq_bound
        (fun n ↦ SimpleDoleansMoments.memLp_mixedProduct_two (X := B) (P := μ)
          (𝓕 := natFiltration hBmeas) (marshalPart_mono hBmeas T (V n).val (V n).property)
          (marshalPart_zero hBmeas T (V n).val (V n).property)
          (stronglyMeasurable_clampM_marshalMult hBmeas T (V n)) (clampM_marshalMult_abs_le hC hBmeas T (V n))
          a _ huT (marshalPart_card_sub_one hBmeas T (V n).val (V n).property).ge)
        (M := 2⁻¹ * (Real.exp (4 * |a| * C * (T : ℝ)) * (∫ ω, Real.exp (4 * a * B u ω) ∂μ)
            + Real.exp (6 * C ^ 2 * (T : ℝ))))
        (fun n ↦ SimpleDoleansMoments.sq_integral_mixedProduct_le (X := B) (P := μ)
          (𝓕 := natFiltration hBmeas) (marshalPart_mono hBmeas T (V n).val (V n).property)
          (marshalPart_zero hBmeas T (V n).val (V n).property)
          (stronglyMeasurable_clampM_marshalMult hBmeas T (V n)) (clampM_marshalMult_abs_le hC hBmeas T (V n))
          a _ huT (marshalPart_card_sub_one hBmeas T (V n).val (V n).property).ge)
        (memLp_gpred_one hB hBmeas T hpred hC hbdd V hV a huT)
        (fun ns hns ↦ tendsto_fnPred_ae_subseq hB hBmeas T hpred hC hbdd V hV a huT ns hns) A
    have hsimple : ∀ n, ∫ ω in A, (Real.exp (a * (B t' ω
          + simpleDrift (marshalPart hBmeas T (V n).val)
            (fun i ω ↦ clampM C (marshalMult hBmeas T (V n).val i ω))
            ((marshalEndpoints hBmeas T (V n).val).card - 1) t' ω) - a ^ 2 * (t' : ℝ) / 2)
        * simpleDoleansExp (X := B) (marshalPart hBmeas T (V n).val)
            (fun i ω ↦ -(clampM C (marshalMult hBmeas T (V n).val i ω)))
            ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω) ∂μ
        = ∫ ω in A, (Real.exp (a * (B s' ω
            + simpleDrift (marshalPart hBmeas T (V n).val)
              (fun i ω ↦ clampM C (marshalMult hBmeas T (V n).val i ω))
              ((marshalEndpoints hBmeas T (V n).val).card - 1) s' ω) - a ^ 2 * (s' : ℝ) / 2)
          * simpleDoleansExp (X := B) (marshalPart hBmeas T (V n).val)
              (fun i ω ↦ -(clampM C (marshalMult hBmeas T (V n).val i ω)))
              ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω) ∂μ := by
      intro n
      have hfield := (isExpQMartingale_BthetaSimple (X := B) (𝓕 := natFiltration hBmeas) (P := μ)
        (marshalPart hBmeas T (V n).val) (marshalPart_mono hBmeas T (V n).val (V n).property)
        (marshalPart_zero hBmeas T (V n).val (V n).property)
        (fun i ω ↦ clampM C (marshalMult hBmeas T (V n).val i ω))
        (stronglyMeasurable_clampM_marshalMult hBmeas T (V n))
        (clampM_marshalMult_abs_le hC hBmeas T (V n))
        ((marshalEndpoints hBmeas T (V n).val).card - 1)
        (marshalPart_card_sub_one hBmeas T (V n).val (V n).property).ge).martingale a hst' ht'T hA
      rwa [setIntegral_withDensity_ofReal (SimpleDoleansMoments.measurable_simpleDoleans (X := B)
            (P := μ) (𝓕 := natFiltration hBmeas) (marshalPart_mono hBmeas T (V n).val (V n).property)
            (stronglyMeasurable_clampM_marshalMult hBmeas T (V n))
            (clampM_marshalMult_abs_le hC hBmeas T (V n)) _ T).aestronglyMeasurable
          (fun ω ↦ (simpleDoleansExp_pos _ _ _ _ ω).le) _ hAmΩ,
        setIntegral_withDensity_ofReal (SimpleDoleansMoments.measurable_simpleDoleans (X := B)
            (P := μ) (𝓕 := natFiltration hBmeas) (marshalPart_mono hBmeas T (V n).val (V n).property)
            (stronglyMeasurable_clampM_marshalMult hBmeas T (V n))
            (clampM_marshalMult_abs_le hC hBmeas T (V n)) _ T).aestronglyMeasurable
          (fun ω ↦ (simpleDoleansExp_pos _ _ _ _ ω).le) _ hAmΩ] at hfield
    rw [setIntegral_withDensity_ofReal hZTaesm hZTpos _ hAmΩ,
      setIntegral_withDensity_ofReal hZTaesm hZTpos _ hAmΩ]
    exact tendsto_nhds_unique (engine t' ht'T)
      ((engine s' (hst'.trans ht'T)).congr'
        (Filter.eventually_atTop.mpr ⟨0, fun n _ ↦ (hsimple n).symm⟩))

include hB in
/-- **Predictable bounded-θ distributional Girsanov: `B^θ` is a `Q`-Brownian motion.** For a bounded
**predictable** market price of risk `θ` (the honest `L²` Itô-integrand domain, no continuity), under
`Q = μ.withDensity(Z_T)` with the Doléans density `Z_T = exp(−∫₀ᵀθdB − ½∫₀ᵀθ²ds)`, the drift-corrected
process `B^θ_u = B_u + driftContinuousMod θ̂ u` is a `Q`-Brownian motion on `[0,T]`: zero start, Gaussian
increments `𝒩(0,t−s)`, and independence of disjoint increments. One application of the exponential
characterization `isQBrownianMotion_of_expMartingale` to `isExpQMartingale_BthetaPredictable` — the
bounded-predictable case (Rung 1), strengthening the bounded-adapted-continuous
`Btheta_isQBrownianMotion_adapted` to the full honest Itô-integrand domain. -/
theorem Btheta_isQBrownianMotion_predictable (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n ↦ simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) :
    (∀ᵐ ω ∂(μ.withDensity fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω)),
        BthetaPred (μ := μ) T hBmeas hpred hbdd 0 ω = 0)
      ∧ (∀ ⦃s t : ℝ≥0⦄, s ≤ t → t ≤ T →
          (μ.withDensity fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω)).map
            (fun ω ↦ BthetaPred (μ := μ) T hBmeas hpred hbdd t ω
              - BthetaPred (μ := μ) T hBmeas hpred hbdd s ω) = gaussianReal 0 (t - s))
      ∧ (∀ ⦃s t u v : ℝ≥0⦄, s ≤ t → t ≤ u → u ≤ v → v ≤ T →
          IndepFun (fun ω ↦ BthetaPred (μ := μ) T hBmeas hpred hbdd t ω
              - BthetaPred (μ := μ) T hBmeas hpred hbdd s ω)
            (fun ω ↦ BthetaPred (μ := μ) T hBmeas hpred hbdd v ω
              - BthetaPred (μ := μ) T hBmeas hpred hbdd u ω)
            (μ.withDensity fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω))) := by
  haveI : IsProbabilityMeasure (μ.withDensity fun ω ↦
      ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω)) :=
    isProbabilityMeasure_predGirsanov hB hBmeas T hpred hC hbdd V hV
  exact isQBrownianMotion_of_expMartingale
    (isExpQMartingale_BthetaPredictable hB hBmeas hpred hC hbdd T V hV)

include hB in
/-- **Bounded-predictable-θ Girsanov, clean form.** For a bounded predictable market price of risk `θ`
(no approximating sequence in the hypotheses — one is obtained internally via `exists_approxSeq`, and
the conclusion `ZTpred`/`BthetaPred` depends only on `θ`), the drift-corrected process
`B^θ_u = B_u + driftContinuousMod θ̂ u` is a `Q`-Brownian motion on `[0,T]` under
`Q = μ.withDensity(exp(−∫₀ᵀθdB − ½∫₀ᵀθ²ds))`. The benchmark-facing form of
`Btheta_isQBrownianMotion_predictable`. -/
theorem Btheta_isQBrownianMotion_predictable_of_bdd (hBmeas : ∀ t, Measurable (B t))
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    (∀ᵐ ω ∂(μ.withDensity fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω)),
        BthetaPred (μ := μ) T hBmeas hpred hbdd 0 ω = 0)
      ∧ (∀ ⦃s t : ℝ≥0⦄, s ≤ t → t ≤ T →
          (μ.withDensity fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω)).map
            (fun ω ↦ BthetaPred (μ := μ) T hBmeas hpred hbdd t ω
              - BthetaPred (μ := μ) T hBmeas hpred hbdd s ω) = gaussianReal 0 (t - s))
      ∧ (∀ ⦃s t u v : ℝ≥0⦄, s ≤ t → t ≤ u → u ≤ v → v ≤ T →
          IndepFun (fun ω ↦ BthetaPred (μ := μ) T hBmeas hpred hbdd t ω
              - BthetaPred (μ := μ) T hBmeas hpred hbdd s ω)
            (fun ω ↦ BthetaPred (μ := μ) T hBmeas hpred hbdd v ω
              - BthetaPred (μ := μ) T hBmeas hpred hbdd u ω)
            (μ.withDensity fun ω ↦ ENNReal.ofReal (ZTpred hB T hBmeas hpred hbdd ω))) := by
  obtain ⟨V, hV⟩ := exists_approxSeq (μ := μ) hBmeas T hpred hbdd
  exact Btheta_isQBrownianMotion_predictable hB hBmeas hpred hC hbdd T V hV

end Assembly

end MathFin
