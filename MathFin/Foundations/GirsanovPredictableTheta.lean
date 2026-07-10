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
    simpleDrift (marshalPart hBmeas T V) (fun i ω => clampM C (marshalMult hBmeas T V i ω)) N u ω
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
  have hV_eq : Set.EqOn (fun s => ⇑(marshalStepSP hBmeas T V hle hC N).val s ω)
      (fun s => ∑ i ∈ Finset.range N,
        (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ => clampM C (marshalMult hBmeas T V i ω)) s) (Set.Ioc (0 : ℝ≥0) u) :=
    fun s _ => uncurry_marshalStepSP hBmeas T V hle hC N s ω
  have hint : ∀ i ∈ Finset.range N,
      Integrable (fun s => (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
        (fun _ => clampM C (marshalMult hBmeas T V i ω)) s)
        (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) u)) :=
    fun i _ => (integrable_const _).indicator measurableSet_Ioc
  rw [setIntegral_congr_fun measurableSet_Ioc hV_eq, integral_finsetSum _ hint, simpleDrift]
  refine Finset.sum_congr rfl (fun i _ => ?_)
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
        (fun i ω => clampM C (marshalMult hBmeas T V i ω)) N T ω
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
  have hsq_eq : Set.EqOn (fun s => (⇑(marshalStepSP hBmeas T V hle hC N).val s ω) ^ 2)
      (fun s => ∑ i ∈ Finset.range N,
        (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ => (clampM C (marshalMult hBmeas T V i ω)) ^ 2) s) (Set.Ioc (0 : ℝ≥0) T) := by
    intro s hs
    dsimp only
    have hlhs : (⇑(marshalStepSP hBmeas T V hle hC N).val s ω) ^ 2 = (clampM C (⇑V s ω)) ^ 2 := by
      rw [show ⇑(marshalStepSP hBmeas T V hle hC N).val s ω
          = Function.uncurry ⇑(marshalStepSP hBmeas T V hle hC N).val (s, ω) from rfl,
        uncurry_marshalStepSP_eq_clamp hBmeas T V hle hC hmpN hs.1 hs.2 ω]
    rw [hlhs]
    have hstep : ∀ i ∈ Finset.range N,
        (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
            (fun _ => (clampM C (marshalMult hBmeas T V i ω)) ^ 2) s
        = (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
            (fun _ => (clampM C (⇑V s ω)) ^ 2) s := by
      intro i _
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hmem : s ∈ Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))
      · rw [if_pos hmem, if_pos hmem, marshalMult_eq_uncurry hBmeas T V hle hmem.1 hmem.2 ω]
      · rw [if_neg hmem, if_neg hmem]
    have hconst : ∀ i,
        (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
            (fun _ => (clampM C (⇑V s ω)) ^ 2) s
        = (clampM C (⇑V s ω)) ^ 2 *
            (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
              (fun _ => (1 : ℝ)) s := by
      intro i
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hmem : s ∈ Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))
      · rw [if_pos hmem, if_pos hmem, mul_one]
      · rw [if_neg hmem, if_neg hmem, mul_zero]
    rw [Finset.sum_congr rfl hstep]
    simp_rw [hconst]
    rw [← Finset.mul_sum, sum_cell_indicator_eq_one hBmeas T V hle hmpN hs.1 hs.2, mul_one]
  have hint : ∀ i ∈ Finset.range N,
      Integrable (fun s => (Set.Ioc (marshalPart hBmeas T V i)
          (marshalPart hBmeas T V (i + 1))).indicator
        (fun _ => (clampM C (marshalMult hBmeas T V i ω)) ^ 2) s)
        (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
    fun i _ => (integrable_const _).indicator measurableSet_Ioc
  rw [setIntegral_congr_fun measurableSet_Ioc hsq_eq, integral_finsetSum _ hint, simpleQuadVar]
  refine Finset.sum_congr rfl (fun i _ => ?_)
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
    (hD0 : Tendsto (fun n => ∫ ω, D n ω ∂μ) atTop (𝓝 0))
    (hdom : ∀ n, ∀ᵐ ω ∂μ, dist (f n ω) (g ω) ≤ K * Real.sqrt (D n ω)) :
    TendstoInMeasure μ f atTop g := by
  have hDmeasure : TendstoInMeasure μ D atTop (fun _ => (0 : ℝ)) := by
    have hDeLp : Tendsto (fun n => eLpNorm (D n - fun _ => (0 : ℝ)) 1 μ) atTop (𝓝 0) := by
      have hrw : ∀ n, eLpNorm (D n - fun _ => (0 : ℝ)) 1 μ = ENNReal.ofReal (∫ ω, D n ω ∂μ) := by
        intro n
        have hsub : (D n - fun _ => (0 : ℝ)) = D n := by funext ω; simp
        have hlint : (∫⁻ ω, ‖D n ω‖ₑ ∂μ) = ∫⁻ ω, ENNReal.ofReal (D n ω) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hDnn n] with ω hω
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hω]
        rw [hsub, eLpNorm_one_eq_lintegral_enorm, hlint,
          ← ofReal_integral_eq_lintegral_ofReal (hDint n) (hDnn n)]
      rw [tendsto_congr hrw, ← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp hD0
    exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun n => (hDint n).aestronglyMeasurable)
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
    exact tendsto_const_nhds.congr fun n => (hz n).symm
  · set r : ℝ := ε.toReal with hr
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
      exact tendsto_const_nhds.congr fun n => (hz n).symm
    · -- `K > 0`: `r ≤ dist ≤ K√(Dₙ)` forces `Dₙ ≥ (r/K)²`, whose measure vanishes
      have hε'pos : (0 : ℝ≥0∞) < ENNReal.ofReal ((r / K) ^ 2) := ENNReal.ofReal_pos.mpr (by positivity)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hDmeasure (ENNReal.ofReal ((r / K) ^ 2)) hε'pos) (fun _ => zero_le)
        (fun n => measure_mono_ae ?_)
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
  have hmeas : AEStronglyMeasurable (fun ω => Real.sqrt (D ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hDint.1
  have hsqeq : (fun ω => (Real.sqrt (D ω)) ^ 2) =ᵐ[μ] D := by
    filter_upwards [hDnn] with ω hω; rw [Real.sq_sqrt hω]
  have hmem : MemLp (fun ω => Real.sqrt (D ω)) 2 μ :=
    (memLp_two_iff_integrable_sq hmeas).mpr (hDint.congr hsqeq.symm)
  have hcs := sq_integral_le_measureReal_mul (ν := μ) hmem
  rw [measure_univ, ENNReal.toReal_one, one_mul, integral_congr_ae hsqeq] at hcs
  rw [← Real.sqrt_sq (integral_nonneg fun ω => Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hcs

omit [IsProbabilityMeasure μ] in
/-- **`L¹` domination ⟹ convergence in measure.** If `dist(fₙ ω, g ω) ≤ hₙ ω` a.e. for an integrable
`hₙ` whose `μ`-mean vanishes, then `fₙ → g` in measure: the difference converges in `L¹(μ)`, whence in
measure. The `L¹`-form companion of `tendstoInMeasure_of_ae_dist_le_sqrt`, for a two-term dominator. -/
lemma tendstoInMeasure_of_ae_dist_le_of_tendsto_integral {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {h : ℕ → Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hhint : ∀ n, Integrable (h n) μ)
    (hdom : ∀ n, ∀ᵐ ω ∂μ, dist (f n ω) (g ω) ≤ h n ω)
    (hh0 : Tendsto (fun n => ∫ ω, h n ω ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop g := by
  refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hf hg ?_
  have hbnd : ∀ n, eLpNorm (f n - g) 1 μ ≤ ENNReal.ofReal (∫ ω, h n ω ∂μ) := by
    intro n
    have hnn : 0 ≤ᵐ[μ] h n := by filter_upwards [hdom n] with ω hω; exact dist_nonneg.trans hω
    rw [eLpNorm_one_eq_lintegral_enorm]
    calc ∫⁻ ω, ‖(f n - g) ω‖ₑ ∂μ
        = ∫⁻ ω, ENNReal.ofReal (dist (f n ω) (g ω)) ∂μ := by
          refine lintegral_congr fun ω => ?_
          rw [Pi.sub_apply, Real.enorm_eq_ofReal_abs, Real.dist_eq]
      _ ≤ ∫⁻ ω, ENNReal.ofReal (h n ω) ∂μ :=
          lintegral_mono_ae (by filter_upwards [hdom n] with ω hω; exact ENNReal.ofReal_le_ofReal hω)
      _ = ENNReal.ofReal (∫ ω, h n ω ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal (hhint n) hnn).symm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hbnd
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
    (hV : Tendsto (fun n => simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd)))
    {u : ℝ≥0} (huT : u ≤ T) :
    TendstoInMeasure μ (fun n => driftSimpleProcess hBmeas
        (marshalStepSP hBmeas T (V n).val (V n).property hC
          ((marshalEndpoints hBmeas T (V n).val).card - 1)).val u) atTop
      (driftContinuousMod T hBmeas (processToLpPredictable (μ := μ) T hBmeas hpred hbdd) u) := by
  set θhat := processToLpPredictable (μ := μ) T hBmeas hpred hbdd with hθhat
  set W : ℕ → TBoundedSP T hBmeas := fun n => marshalStepSP hBmeas T (V n).val (V n).property hC
    ((marshalEndpoints hBmeas T (V n).val).card - 1) with hW
  haveI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) u)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  -- ω-slice energy `Dₙ` and its `L¹(μ)` decay
  set D : ℕ → Ω → ℝ := fun n ω =>
    ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(W n).val s ω - ⇑θhat (s, ω)) ^ 2 ∂timeMeasure with hDdef
  have hDnn : ∀ n, 0 ≤ᵐ[μ] D n := fun n => ae_of_all _ fun ω => integral_nonneg fun s => sq_nonneg _
  have hDint : ∀ n, Integrable (D n) μ :=
    fun n => (drift_slice_sq_integrable T hBmeas θhat (W n)).integral_prod_right
  have hD0 : Tendsto (fun n => ∫ ω, D n ω ∂μ) atTop (𝓝 0) := by
    have heq : ∀ n, (∫ ω, D n ω ∂μ) = ‖simpleAssembly_T (μ := μ) T hBmeas (W n) - θhat‖ ^ 2 :=
      fun n => drift_slice_energy_eq T hBmeas θhat (W n)
    simp_rw [heq]
    have h0 : Tendsto (fun n => ‖simpleAssembly_T (μ := μ) T hBmeas (W n) - θhat‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp
        (tendsto_simpleAssembly_marshalStepSP T hBmeas hpred hC hbdd V hV)
    simpa using h0.pow 2
  -- `θ̂` sliced is `L²` a.e.
  have hg_prod : MemLp (⇑θhat) 2 ((timeMeasure_T T).prod μ) :=
    ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim (natFiltration hBmeas).predictable_le_prod
      (Lp.aestronglyMeasurable θhat),
     by rw [← eLpNorm_trim_ae (natFiltration hBmeas).predictable_le_prod (Lp.aestronglyMeasurable θhat)]
        exact (Lp.memLp θhat).2⟩
  have hg_slice : ∀ᵐ ω ∂μ, MemLp (fun s => ⇑θhat (s, ω)) 2 (timeMeasure_T T) := by
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
    have hVt : MemLp (fun s => ⇑(W n).val s ω) 2 (timeMeasure.restrict (Set.Ioc 0 u)) :=
      (memLp_slice T hBmeas (W n).val ω).mono_measure
        (Measure.restrict_mono (Set.Ioc_subset_Ioc_right huT) le_rfl)
    have hgt : MemLp (fun s => ⇑θhat (s, ω)) 2 (timeMeasure.restrict (Set.Ioc 0 u)) :=
      hωg.mono_measure (Measure.restrict_mono (Set.Ioc_subset_Ioc_right huT) le_rfl)
    have hfT : MemLp (fun s => ⇑(W n).val s ω - ⇑θhat (s, ω)) 2
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
            (setIntegral_mono_set hfT.integrable_sq (ae_of_all _ fun s => sq_nonneg _)
              (Set.Ioc_subset_Ioc_right huT).eventuallyLE) u.coe_nonneg
  refine tendstoInMeasure_of_ae_dist_le_sqrt (Real.sqrt_nonneg (u : ℝ)) hDnn hDint hD0 (fun n => ?_)
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
    (hV : Tendsto (fun n => simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) :
    TendstoInMeasure μ
      (fun n => simpleQuadVar (marshalPart hBmeas T (V n).val)
        (fun i ω => clampM C (marshalMult hBmeas T (V n).val i ω))
        ((marshalEndpoints hBmeas T (V n).val).card - 1) T)
      atTop
      (fun ω => ∫ s in Set.Ioc (0 : ℝ≥0) T,
        (⇑(processToLpPredictable (μ := μ) T hBmeas hpred hbdd) (s, ω)) ^ 2 ∂timeMeasure) := by
  set θhat := processToLpPredictable (μ := μ) T hBmeas hpred hbdd with hθhat
  set W : ℕ → TBoundedSP T hBmeas := fun n => marshalStepSP hBmeas T (V n).val (V n).property hC
    ((marshalEndpoints hBmeas T (V n).val).card - 1) with hW
  haveI hfin : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  set D : ℕ → Ω → ℝ := fun n ω =>
    ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(W n).val s ω - ⇑θhat (s, ω)) ^ 2 ∂timeMeasure with hDdef
  have hDnn : ∀ n, 0 ≤ᵐ[μ] D n := fun n => ae_of_all _ fun ω => integral_nonneg fun s => sq_nonneg _
  have hDint : ∀ n, Integrable (D n) μ :=
    fun n => (drift_slice_sq_integrable T hBmeas θhat (W n)).integral_prod_right
  have hD0 : Tendsto (fun n => ∫ ω, D n ω ∂μ) atTop (𝓝 0) := by
    have heq : ∀ n, (∫ ω, D n ω ∂μ) = ‖simpleAssembly_T (μ := μ) T hBmeas (W n) - θhat‖ ^ 2 :=
      fun n => drift_slice_energy_eq T hBmeas θhat (W n)
    simp_rw [heq]
    have h0 : Tendsto (fun n => ‖simpleAssembly_T (μ := μ) T hBmeas (W n) - θhat‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp
        (tendsto_simpleAssembly_marshalStepSP T hBmeas hpred hC hbdd V hV)
    simpa using h0.pow 2
  have hg_prod : MemLp (⇑θhat) 2 ((timeMeasure_T T).prod μ) :=
    ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim (natFiltration hBmeas).predictable_le_prod
      (Lp.aestronglyMeasurable θhat),
     by rw [← eLpNorm_trim_ae (natFiltration hBmeas).predictable_le_prod (Lp.aestronglyMeasurable θhat)]
        exact (Lp.memLp θhat).2⟩
  have hg_slice : ∀ᵐ ω ∂μ, MemLp (fun s => ⇑θhat (s, ω)) 2 (timeMeasure_T T) := by
    filter_upwards [hg_prod.1.prodMk_right, hg_prod.integrable_sq.prod_left_ae] with ω hω1 hω2
    exact (memLp_two_iff_integrable_sq hω1).mpr hω2
  have hQmeas : ∀ n, AEStronglyMeasurable
      (fun ω => simpleQuadVar (marshalPart hBmeas T (V n).val)
        (fun i ω => clampM C (marshalMult hBmeas T (V n).val i ω))
        ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω) μ := by
    intro n
    refine Measurable.aestronglyMeasurable ?_
    unfold SimpleDoleansMoments.simpleQuadVar
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (((measurable_clampM_comp hBmeas
      (stronglyMeasurable_marshalMult hBmeas T (V n).val i).measurable).pow_const 2).mul_const _).mono
      ((natFiltration hBmeas).le _) le_rfl
  have hLmeas : AEStronglyMeasurable
      (fun ω => ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑θhat (s, ω)) ^ 2 ∂timeMeasure) μ :=
    hg_prod.integrable_sq.swap.aestronglyMeasurable.integral_prod_right'
  -- the pointwise `|Q − L| ≤ 2C√T·√Dₙ + Dₙ` domination
  have hdom : ∀ n, ∀ᵐ ω ∂μ,
      dist (simpleQuadVar (marshalPart hBmeas T (V n).val)
          (fun i ω => clampM C (marshalMult hBmeas T (V n).val i ω))
          ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω)
        (∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑θhat (s, ω)) ^ 2 ∂timeMeasure)
        ≤ 2 * C * Real.sqrt (T : ℝ) * Real.sqrt (D n ω) + D n ω := by
    intro n
    filter_upwards [hg_slice] with ω hωg
    have hmpN : marshalPart hBmeas T (V n).val ((marshalEndpoints hBmeas T (V n).val).card - 1) = T :=
      marshalPart_card_sub_one hBmeas T (V n).val (V n).property
    have hQeq : simpleQuadVar (marshalPart hBmeas T (V n).val)
        (fun i ω => clampM C (marshalMult hBmeas T (V n).val i ω))
        ((marshalEndpoints hBmeas T (V n).val).card - 1) T ω
        = ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(W n).val s ω) ^ 2 ∂timeMeasure :=
      simpleQuadVar_marshalStepSP_eq hBmeas T (V n).val (V n).property hC hmpN ω
    have hVt : MemLp (fun s => ⇑(W n).val s ω) 2 (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
      memLp_slice T hBmeas (W n).val ω
    have hgt : MemLp (fun s => ⇑θhat (s, ω)) 2 (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) := hωg
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
        exact integral_congr_ae (ae_of_all _ fun s => by ring)
      have h2 : (∫ s in Set.Ioc (0 : ℝ≥0) T,
              (2 * (⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)))
                - (⇑(W n).val s ω - ⇑θhat (s, ω)) ^ 2) ∂timeMeasure)
          = 2 * (∫ s in Set.Ioc (0 : ℝ≥0) T,
              ⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)) ∂timeMeasure)
            - ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑(W n).val s ω - ⇑θhat (s, ω)) ^ 2 ∂timeMeasure := by
        rw [integral_sub (f := fun s => 2 * (⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω))))
            (g := fun s => (⇑(W n).val s ω - ⇑θhat (s, ω)) ^ 2)
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
          (fun s hs => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hstepbnd s hs) (abs_nonneg _)
      have hL1L2 : ∫ s in Set.Ioc (0 : ℝ≥0) T, |⇑(W n).val s ω - ⇑θhat (s, ω)| ∂timeMeasure
          ≤ Real.sqrt (T : ℝ) * Real.sqrt (D n ω) := by
        rw [← Real.sqrt_mul T.coe_nonneg (D n ω),
          ← Real.sqrt_sq (integral_nonneg fun s => abs_nonneg _)]
        refine Real.sqrt_le_sqrt ?_
        have hcs := sq_integral_le_measureReal_mul (ν := timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T))
          (hVt.sub hgt).abs
        rw [Measure.restrict_apply_univ, timeMeasure_Ioc,
          ENNReal.toReal_ofReal (by rw [NNReal.coe_zero, sub_zero]; exact T.coe_nonneg),
          NNReal.coe_zero, sub_zero] at hcs
        refine hcs.trans_eq ?_
        rw [hDdef]
        refine congrArg (fun z => (T : ℝ) * z) (integral_congr_ae (ae_of_all _ fun s => ?_))
        simp only [Pi.abs_apply, Pi.sub_apply, sq_abs]
      calc |∫ s in Set.Ioc (0 : ℝ≥0) T,
              ⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)) ∂timeMeasure|
          ≤ ∫ s in Set.Ioc (0 : ℝ≥0) T, C * |⇑(W n).val s ω - ⇑θhat (s, ω)| ∂timeMeasure := habs
        _ = C * ∫ s in Set.Ioc (0 : ℝ≥0) T, |⇑(W n).val s ω - ⇑θhat (s, ω)| ∂timeMeasure :=
            integral_const_mul _ _
        _ ≤ C * (Real.sqrt (T : ℝ) * Real.sqrt (D n ω)) := mul_le_mul_of_nonneg_left hL1L2 hC
        _ = C * Real.sqrt (T : ℝ) * Real.sqrt (D n ω) := by ring
    have hDeq : |D n ω| = D n ω := abs_of_nonneg (integral_nonneg fun s => sq_nonneg _)
    calc |2 * (∫ s in Set.Ioc (0 : ℝ≥0) T,
            ⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)) ∂timeMeasure) - D n ω|
        ≤ 2 * |∫ s in Set.Ioc (0 : ℝ≥0) T,
            ⇑(W n).val s ω * (⇑(W n).val s ω - ⇑θhat (s, ω)) ∂timeMeasure| + D n ω := by
          refine (abs_sub _ _).trans (le_of_eq ?_); rw [abs_mul, abs_two, hDeq]
      _ ≤ 2 * (C * Real.sqrt (T : ℝ) * Real.sqrt (D n ω)) + D n ω := by gcongr
      _ = 2 * C * Real.sqrt (T : ℝ) * Real.sqrt (D n ω) + D n ω := by ring
  have hsqrtint : ∀ n, Integrable (fun ω => Real.sqrt (D n ω)) μ := by
    intro n
    have hpt : ∀ ω, 0 ≤ D n ω := fun ω => integral_nonneg fun s => sq_nonneg _
    refine Integrable.mono' ((hDint n).add (integrable_const (1 : ℝ)))
      (Real.continuous_sqrt.comp_aestronglyMeasurable (hDint n).1) (ae_of_all _ fun ω => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [sq_nonneg (Real.sqrt (D n ω) - 1), Real.sq_sqrt (hpt ω), Real.sqrt_nonneg (D n ω),
      hpt ω]
  refine tendstoInMeasure_of_ae_dist_le_of_tendsto_integral hQmeas hLmeas
    (fun n => ((hsqrtint n).const_mul (2 * C * Real.sqrt (T : ℝ))).add (hDint n)) hdom ?_
  have hbnd : ∀ n, (∫ ω, (2 * C * Real.sqrt (T : ℝ) * Real.sqrt (D n ω) + D n ω) ∂μ)
      ≤ 2 * C * Real.sqrt (T : ℝ) * Real.sqrt (∫ ω, D n ω ∂μ) + ∫ ω, D n ω ∂μ := by
    intro n
    have hcf : (0 : ℝ) ≤ 2 * C * Real.sqrt (T : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hC) (Real.sqrt_nonneg _)
    rw [integral_add ((hsqrtint n).const_mul _) (hDint n), integral_const_mul]
    gcongr
    exact integral_sqrt_le_sqrt_integral (hDnn n) (hDint n)
  have hg0 : Tendsto (fun n => 2 * C * Real.sqrt (T : ℝ) * Real.sqrt (∫ ω, D n ω ∂μ)
      + ∫ ω, D n ω ∂μ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => Real.sqrt (∫ ω, D n ω ∂μ)) atTop (𝓝 0) := by
      rw [← Real.sqrt_zero]; exact (Real.continuous_sqrt.tendsto 0).comp hD0
    simpa using (h1.const_mul (2 * C * Real.sqrt (T : ℝ))).add hD0
  refine squeeze_zero (fun n => integral_nonneg fun ω => ?_) hbnd hg0
  exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)) (integral_nonneg fun s => sq_nonneg _)

end Convergence

end MathFin
