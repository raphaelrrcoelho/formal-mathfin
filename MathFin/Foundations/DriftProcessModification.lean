/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.DriftProcessPredictable
public import MathFin.Foundations.FiniteMeasureCauchySchwarz

/-! # The pathwise drift process: convergence and modification (SDE-existence bridge, #19→existence)

The `L²` drift operator `driftProcessAssembled : E →L E` is assembled abstractly (`extendOfNorm`);
`driftContinuousMod` is its pointwise-`limUnder` pathwise realization. This file supplies the drift
analog of the Itô side's `itoContinuousMod_tendsto` / `_modification`: the per-`t` value bridge that
lets an `E`-element be sliced into a genuine pathwise identity — the piece the pathwise SDE-existence
statement (`sc-thm-8.2.5`, existence half) needs.

The drift side is **simpler** than the Itô side: `driftSimpleProcess V · ω` is continuous for *every*
`ω` (a finite sum of `𝓕`-coefficients times continuous time-increments), so there is no exceptional
null set and no martingale maximal inequality — the uniform-in-`t` control is pure Cauchy–Schwarz
(`sq_intervalIntegral_le`) against the deterministic time integral.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcessContinuousModification
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- **The running-max keystone (drift).** For `i ≤ T`, `|driftSimpleProcess W i ω|` is bounded by the
running maximum over `[0,T]`. The supremum is genuine (not the junk value of an unbounded family):
`driftSimpleProcess W · ω` is continuous and `[0,T]` is compact, so the family is bounded above. -/
lemma drift_norm_le_iSup_Iic (hBmeas : ∀ t, Measurable (B t))
    (W : SimpleProcess ℝ (natFiltration hBmeas)) (ω : Ω) {i T : ℝ≥0} (hi : i ≤ T) :
    |driftSimpleProcess hBmeas W i ω|
      ≤ ⨆ j : Set.Iic T, |driftSimpleProcess hBmeas W (j : ℝ≥0) ω| := by
  have hcont : Continuous fun j : Set.Iic T => |driftSimpleProcess hBmeas W (j : ℝ≥0) ω| :=
    (continuous_abs.comp (driftSimpleProcess_continuous hBmeas W ω)).comp continuous_subtype_val
  have hIic : (Set.Iic T : Set ℝ≥0) = Set.Icc 0 T := by
    ext x; simp only [Set.mem_Iic, Set.mem_Icc, zero_le, true_and]
  haveI : CompactSpace (Set.Iic T) := isCompact_iff_compactSpace.mp (hIic ▸ isCompact_Icc)
  exact le_ciSup (isCompact_range hcont).bddAbove ⟨i, hi⟩

/-! ## Layer 1 — the drift maximal estimate (direct Chebyshev) and Borel–Cantelli -/

/-- The elementary drift **negates**: `drift (-V) = -drift V` (via `driftSimpleProcess_smul (-1)`). -/
lemma driftSimpleProcess_neg (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) :
    driftSimpleProcess hBmeas (-V) t = -driftSimpleProcess hBmeas V t := by
  rw [show (-V) = (-1 : ℝ) • V from (neg_one_smul ℝ V).symm, driftSimpleProcess_smul, neg_one_smul]

/-- The elementary drift is **subtractive** (from `_add` + `_neg`), mirroring `itoSimpleProcess_sub`. -/
lemma driftSimpleProcess_sub (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) :
    driftSimpleProcess hBmeas (V - W) t
      = driftSimpleProcess hBmeas V t - driftSimpleProcess hBmeas W t := by
  rw [sub_eq_add_neg, driftSimpleProcess_add, driftSimpleProcess_neg, ← sub_eq_add_neg]

/-- **The `E`-norm² of a simple embedding as a double integral.** Tonelli turns `‖simpleAssembly_T W‖²`
into `∫_Ω ∫₀ᵀ (⇑W)² ds dμ` — the outer-`ω`, inner-time energy that the drift Chebyshev bound reads. -/
lemma simpleAssembly_T_norm_sq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (W : TBoundedSP T hBmeas) :
    ‖simpleAssembly_T (μ := μ) T hBmeas W‖ ^ 2
      = ∫ ω, ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑W.val s ω) ^ 2 ∂timeMeasure ∂μ := by
  set 𝓕 := natFiltration (mΩ := mΩ) hBmeas
  have hmemV := memLp_uncurry_trim_T (μ := μ) T hBmeas W.val
  have hpredV := W.val.isStronglyPredictable
  have hmemV_prod : MemLp (Function.uncurry ⇑W.val) 2 ((timeMeasure_T T).prod μ) :=
    ⟨(hpredV.mono 𝓕.predictable_le_prod).aestronglyMeasurable, by
      rw [← eLpNorm_trim 𝓕.predictable_le_prod hpredV]; exact hmemV.2⟩
  have hintV := hmemV_prod.integrable_sq
  rw [show simpleAssembly_T (μ := μ) T hBmeas W = hmemV.toLp (Function.uncurry ⇑W.val) from rfl,
    lp_two_norm_sq, integral_congr_ae (g := fun z => (Function.uncurry ⇑W.val z) ^ 2)
      (by filter_upwards [hmemV.coeFn_toLp] with z hz; rw [hz]),
    show trimMeasure_T (μ := μ) T hBmeas
        = ((timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod from rfl,
    ← integral_trim 𝓕.predictable_le_prod (f := fun z => (Function.uncurry ⇑W.val z) ^ 2)
      (hpredV.pow 2)]
  symm
  rw [integral_prod _ hintV]
  exact integral_integral_swap hintV.swap

/-- **Pointwise sup bound.** For every `ω`, the squared running maximum of `|drift W · ω|` over `[0,T]`
is at most the deterministic energy `T·∫₀ᵀ (⇑W)²`: each slice obeys `driftSimpleProcess_sq_le`, so the
sup does too. Sup-free on the right — the input to a Chebyshev bound that dodges sup-measurability. -/
lemma drift_iSup_sq_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (W : SimpleProcess ℝ (natFiltration hBmeas)) (ω : Ω) :
    (⨆ i : Set.Iic T, |driftSimpleProcess hBmeas W (i : ℝ≥0) ω|) ^ 2
      ≤ (T : ℝ) * ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑W s ω) ^ 2 ∂timeMeasure := by
  haveI : Nonempty (Set.Iic T) := ⟨⟨0, by simp⟩⟩
  set R := (T : ℝ) * ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑W s ω) ^ 2 ∂timeMeasure with hR
  have hR0 : 0 ≤ R := mul_nonneg T.coe_nonneg (integral_nonneg fun s => sq_nonneg _)
  have hbound : (⨆ i : Set.Iic T, |driftSimpleProcess hBmeas W (i : ℝ≥0) ω|) ≤ Real.sqrt R :=
    ciSup_le fun i => by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (driftSimpleProcess_sq_le T hBmeas W (Set.mem_Iic.mp i.2) ω)
  have h0 : 0 ≤ ⨆ i : Set.Iic T, |driftSimpleProcess hBmeas W (i : ℝ≥0) ω| :=
    Real.iSup_nonneg fun i => abs_nonneg _
  calc (⨆ i : Set.Iic T, |driftSimpleProcess hBmeas W (i : ℝ≥0) ω|) ^ 2
      ≤ (Real.sqrt R) ^ 2 := by simpa [pow_two] using mul_self_le_mul_self h0 hbound
    _ = R := Real.sq_sqrt hR0

/-- **The drift maximal probability (direct Chebyshev).** For a `T`-bounded simple process `W`, the
probability that the running maximum of `|drift W|` over `[0,T]` reaches `ε` is at most
`(ε²)⁻¹·T·‖simpleAssembly_T W‖²`. Unlike the Itô side (Doob's weak-type maximal inequality), the drift
paths are honestly continuous, so the sup is controlled pathwise by `drift_iSup_sq_le`; bounding the
event by the sup-free set `{ε² ≤ T∫₀ᵀW²}` sidesteps sup-measurability and leaves a one-line Markov. -/
lemma drift_maximal_prob (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (W : TBoundedSP T hBmeas)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ ⨆ i : Set.Iic T, |driftSimpleProcess hBmeas W.val (i : ℝ≥0) ω|}
      ≤ (ε ^ 2)⁻¹ * ((T : ℝ) * ‖simpleAssembly_T (μ := μ) T hBmeas W‖ ^ 2) := by
  set 𝓕 := natFiltration (mΩ := mΩ) hBmeas
  have hmemV := memLp_uncurry_trim_T (μ := μ) T hBmeas W.val
  have hpredV := W.val.isStronglyPredictable
  have hmemV_prod : MemLp (Function.uncurry ⇑W.val) 2 ((timeMeasure_T T).prod μ) :=
    ⟨(hpredV.mono 𝓕.predictable_le_prod).aestronglyMeasurable, by
      rw [← eLpNorm_trim 𝓕.predictable_le_prod hpredV]; exact hmemV.2⟩
  have hintV := hmemV_prod.integrable_sq
  have hfun_int : Integrable
      (fun ω => (T : ℝ) * ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑W.val s ω) ^ 2 ∂timeMeasure) μ :=
    (hintV.integral_prod_right).const_mul _
  have hfun_nonneg : 0 ≤ᵐ[μ]
      fun ω => (T : ℝ) * ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑W.val s ω) ^ 2 ∂timeMeasure :=
    ae_of_all _ fun ω => mul_nonneg T.coe_nonneg (integral_nonneg fun s => sq_nonneg _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hfun_nonneg hfun_int (ε ^ 2)
  have hintg : (∫ ω, (T : ℝ) * ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑W.val s ω) ^ 2 ∂timeMeasure ∂μ)
      = (T : ℝ) * ‖simpleAssembly_T (μ := μ) T hBmeas W‖ ^ 2 := by
    rw [integral_const_mul, simpleAssembly_T_norm_sq]
  have hsub : {ω | ε ≤ ⨆ i : Set.Iic T, |driftSimpleProcess hBmeas W.val (i : ℝ≥0) ω|}
      ⊆ {ω | ε ^ 2 ≤ (T : ℝ) * ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑W.val s ω) ^ 2 ∂timeMeasure} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    calc ε ^ 2 ≤ (⨆ i : Set.Iic T, |driftSimpleProcess hBmeas W.val (i : ℝ≥0) ω|) ^ 2 := by
          simpa [pow_two] using mul_self_le_mul_self hε.le hω
      _ ≤ _ := drift_iSup_sq_le T hBmeas W.val ω
  have hmono : μ.real {ω | ε ≤ ⨆ i : Set.Iic T, |driftSimpleProcess hBmeas W.val (i : ℝ≥0) ω|}
      ≤ μ.real {ω | ε ^ 2 ≤ (T : ℝ) * ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑W.val s ω) ^ 2 ∂timeMeasure} := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
  have hchain : ε ^ 2 * μ.real {ω | ε ≤ ⨆ i : Set.Iic T, |driftSimpleProcess hBmeas W.val (i : ℝ≥0) ω|}
      ≤ (T : ℝ) * ‖simpleAssembly_T (μ := μ) T hBmeas W‖ ^ 2 :=
    (mul_le_mul_of_nonneg_left hmono (by positivity)).trans (hmarkov.trans_eq hintg)
  calc μ.real {ω | ε ≤ ⨆ i : Set.Iic T, |driftSimpleProcess hBmeas W.val (i : ℝ≥0) ω|}
      = (ε ^ 2)⁻¹
          * (ε ^ 2 * μ.real {ω | ε ≤ ⨆ i : Set.Iic T, |driftSimpleProcess hBmeas W.val (i : ℝ≥0) ω|}) := by
        rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    _ ≤ (ε ^ 2)⁻¹ * ((T : ℝ) * ‖simpleAssembly_T (μ := μ) T hBmeas W‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)

/-- **Summable maximal tail (drift).** For the fast subsequence `V` (`approxSeq`), the probabilities
that the running max of `|drift (Vₙ − Vₙ₊₁)|` over `[0,T]` reaches `(3/4)ⁿ` are summable: Chebyshev
gives `≤ ((3/4)ⁿ)⁻²·T·‖simpleAssembly_T (Vₙ−Vₙ₊₁)‖² ≤ (16/9)ⁿ·T·(2·2⁻ⁿ)² = 4T·(4/9)ⁿ`, and `4/9 < 1`. -/
theorem drift_summable_maximal_tail (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (V : ℕ → TBoundedSP T hBmeas)
    (hV : ∀ n, ‖simpleAssembly_T (μ := μ) T hBmeas (V n) - φ‖ ≤ (2⁻¹ : ℝ) ^ n) :
    Summable (fun n => μ.real {ω | (3 / 4 : ℝ) ^ n ≤
      ⨆ i : Set.Iic T, |driftSimpleProcess hBmeas (V n - V (n + 1)).val (i : ℝ≥0) ω|}) := by
  refine Summable.of_nonneg_of_le (fun n => measureReal_nonneg) (fun n => ?_)
    ((summable_geometric_of_lt_one (r := 4 / 9) (by norm_num) (by norm_num)).mul_left (4 * (T : ℝ)))
  refine (drift_maximal_prob T hBmeas (V n - V (n + 1)) (ε := (3 / 4 : ℝ) ^ n) (by positivity)).trans ?_
  have hnorm : ‖simpleAssembly_T (μ := μ) T hBmeas (V n - V (n + 1))‖ ≤ 2 * (2⁻¹ : ℝ) ^ n := by
    rw [map_sub]
    calc ‖simpleAssembly_T (μ := μ) T hBmeas (V n) - simpleAssembly_T (μ := μ) T hBmeas (V (n + 1))‖
        ≤ ‖simpleAssembly_T (μ := μ) T hBmeas (V n) - φ‖
            + ‖φ - simpleAssembly_T (μ := μ) T hBmeas (V (n + 1))‖ := by
          have h := norm_add_le (simpleAssembly_T (μ := μ) T hBmeas (V n) - φ)
            (φ - simpleAssembly_T (μ := μ) T hBmeas (V (n + 1)))
          simpa using h
      _ ≤ (2⁻¹ : ℝ) ^ n + (2⁻¹ : ℝ) ^ (n + 1) := by
          gcongr
          · exact hV n
          · rw [norm_sub_rev]; exact hV (n + 1)
      _ ≤ 2 * (2⁻¹ : ℝ) ^ n := by
          rw [pow_succ]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) n]
  calc (((3 / 4 : ℝ) ^ n) ^ 2)⁻¹
        * ((T : ℝ) * ‖simpleAssembly_T (μ := μ) T hBmeas (V n - V (n + 1))‖ ^ 2)
      ≤ (((3 / 4 : ℝ) ^ n) ^ 2)⁻¹ * ((T : ℝ) * (2 * (2⁻¹ : ℝ) ^ n) ^ 2) := by
        gcongr
    _ = 4 * (T : ℝ) * (4 / 9 : ℝ) ^ n := by
        have e1 : ((3 / 4 : ℝ) ^ n) ^ 2 = (9 / 16 : ℝ) ^ n := by
          rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
        have e2 : (2 * (2⁻¹ : ℝ) ^ n) ^ 2 = 4 * (1 / 4 : ℝ) ^ n := by
          rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]; norm_num
        rw [e1, e2, ← inv_pow, show (9 / 16 : ℝ)⁻¹ = 16 / 9 from by norm_num,
          show (16 / 9 : ℝ) ^ n * ((T : ℝ) * (4 * (1 / 4 : ℝ) ^ n))
              = 4 * (T : ℝ) * ((16 / 9 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) from by ring,
          ← mul_pow, show (16 / 9 : ℝ) * (1 / 4) = 4 / 9 from by norm_num]

/-- **A.s. eventual smallness (Borel–Cantelli, drift).** Since the maximal tail is summable, for
almost every `ω` the running maximum of `|drift (Vₙ − Vₙ₊₁)|` over `[0,T]` is eventually below
`(3/4)ⁿ` — the pathwise input to the uniform-Cauchy argument. -/
theorem drift_ae_eventually_sup_lt (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (V : ℕ → TBoundedSP T hBmeas)
    (hV : ∀ n, ‖simpleAssembly_T (μ := μ) T hBmeas (V n) - φ‖ ≤ (2⁻¹ : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      (⨆ i : Set.Iic T, |driftSimpleProcess hBmeas (V n - V (n + 1)).val (i : ℝ≥0) ω|)
        < (3 / 4 : ℝ) ^ n := by
  set A : ℕ → Set Ω := fun n => {ω | (3 / 4 : ℝ) ^ n ≤
    ⨆ i : Set.Iic T, |driftSimpleProcess hBmeas (V n - V (n + 1)).val (i : ℝ≥0) ω|} with hA
  have hconv : (∑' n, μ (A n)) ≠ ∞ := by
    have heq : ∀ n, μ (A n) = ENNReal.ofReal (μ.real (A n)) :=
      fun n => (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => measureReal_nonneg)
      (drift_summable_maximal_tail T hBmeas φ V hV)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hconv] with ω hω
  filter_upwards [hω] with n hn
  rwa [hA, Set.mem_setOf_eq, not_le] at hn

/-! ## Layer 2 — pointwise a.s. convergence of the elementary drifts -/

/-- **Pointwise a.s. convergence (drift).** For almost every `ω` and every `t ≤ T`, the approximating
elementary drifts `driftSimpleProcess Vₙ t ω` converge to `driftContinuousMod φ t ω`. The consecutive
distances are eventually `< (3/4)ⁿ` (a.s., uniformly in `t ≤ T`, by `drift_ae_eventually_sup_lt` +
the running-max keystone + subtractivity), hence summable, so the sequence is Cauchy in `ℝ`. This is
the drift analog of `itoContinuousMod_tendsto`, with no martingale and no exceptional null set beyond
the Borel–Cantelli one. -/
theorem driftContinuousMod_tendsto (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ T →
      Tendsto (fun n => driftSimpleProcess hBmeas ((approxSeq T hBmeas φ).choose n).val t ω) atTop
        (𝓝 (driftContinuousMod T hBmeas φ t ω)) := by
  set V := (approxSeq T hBmeas φ).choose with hVdef
  have hV := (approxSeq T hBmeas φ).choose_spec
  filter_upwards [drift_ae_eventually_sup_lt T hBmeas φ V hV] with ω hω
  intro t ht
  have hcauchy : CauchySeq (fun n => driftSimpleProcess hBmeas (V n).val t ω) := by
    apply cauchySeq_of_summable_dist
    obtain ⟨N, hN⟩ := eventually_atTop.mp hω
    rw [← summable_nat_add_iff N]
    refine Summable.of_nonneg_of_le (fun n => dist_nonneg) (fun n => ?_)
      (f := fun n => (3 / 4 : ℝ) ^ (n + N)) ?_
    · rw [dist_eq_norm, Real.norm_eq_abs]
      have hcoe : ((V (n + N) - V (n + N + 1)).val : SimpleProcess ℝ (natFiltration hBmeas))
          = (V (n + N)).val - (V (n + N + 1)).val := rfl
      have hlin : driftSimpleProcess hBmeas (V (n + N)).val t ω
            - driftSimpleProcess hBmeas (V (n + N + 1)).val t ω
          = driftSimpleProcess hBmeas (V (n + N) - V (n + N + 1)).val t ω := by
        rw [hcoe]
        exact (congrFun (driftSimpleProcess_sub hBmeas (V (n + N)).val (V (n + N + 1)).val t) ω).symm
      rw [hlin]
      exact (drift_norm_le_iSup_Iic hBmeas (V (n + N) - V (n + N + 1)).val ω ht).trans
        (hN (n + N) (Nat.le_add_left N n)).le
    · simp_rw [pow_add]
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  simpa only [driftContinuousMod, hVdef] using hcauchy.tendsto_limUnder

/-! ## Layer 3 — the assembled drift's pointwise realization (the crux) -/

/-- **The assembled drift, sliced, is the pathwise drift limit.** The abstract `extendOfNorm` operator
`driftProcessAssembled T g : E →L E` — built from the density of `simpleAssembly_T`, with no pathwise
content of its own — has `coeFn` almost everywhere equal to the honest pointwise `limUnder` process
`driftContinuousMod T g`. This is the drift analog of the Itô side's `itoProcessAssembled` being *built
from* `itoContinuousMod`; here the identification must be **proved**, via two convergences of the same
approximating sequence `driftSimpleProcessLp Vₙ` (`Vₙ → g` in `E`): to `driftProcessAssembled g` by the
operator's continuity, and to `driftContinuousMod T g` a.e. (Layer 2 lifted from the per-slice a.e. to
the trim measure — the convergence set is predictable-measurable, so its product-conull status
transfers to the trim via `trim_measurableSet_eq`). In-measure limits on the finite trim measure are
a.e.-unique. -/
theorem driftProcessAssembled_coeFn (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (g : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ⇑(driftProcessAssembled (μ := μ) T hBmeas g)
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas] Function.uncurry (driftContinuousMod T hBmeas g) := by
  set V := (approxSeq T hBmeas g).choose with hVdef
  have hV := (approxSeq T hBmeas g).choose_spec
  have hGpred : ∀ n, StronglyMeasurable[(natFiltration hBmeas).predictable]
      (Function.uncurry (driftSimpleProcess hBmeas (V n).val)) :=
    fun n => driftSimpleProcess_isStronglyPredictable hBmeas (V n).val
  have hHpred : StronglyMeasurable[(natFiltration hBmeas).predictable]
      (Function.uncurry (driftContinuousMod T hBmeas g)) :=
    driftContinuousMod_isStronglyPredictable T hBmeas g
  set C := {z : ℝ≥0 × Ω | Tendsto
      (fun n => Function.uncurry (driftSimpleProcess hBmeas (V n).val) z) atTop
      (𝓝 (Function.uncurry (driftContinuousMod T hBmeas g) z))} with hC
  have hCpred : MeasurableSet[(natFiltration hBmeas).predictable] C := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := (natFiltration hBmeas).predictable
    exact measurableSet_tendsto_fun (fun n => (hGpred n).measurable) hHpred.measurable
  -- C is prod-conull, built from the per-slice a.e. convergence of Layer 2
  have hCprod : ∀ᵐ z ∂((timeMeasure_T T).prod μ), z ∈ C := by
    have hset : MeasurableSet C :=
      measurableSet_tendsto_fun
        (fun n => ((hGpred n).mono (natFiltration hBmeas).predictable_le_prod).measurable)
        ((hHpred.mono (natFiltration hBmeas).predictable_le_prod).measurable)
    refine (Measure.ae_prod_iff_ae_ae hset).mpr ?_
    have hsub : ∀ᵐ t ∂(timeMeasure_T T), t ≤ T := by
      rw [timeMeasure_T]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
    filter_upwards [hsub] with t htT
    filter_upwards [driftContinuousMod_tendsto T hBmeas g] with ω hω
    exact hω t htT
  -- transfer prod-conull ↦ trim-conull (C is predictable-measurable)
  have h0 : (trimMeasure_T (μ := μ) T hBmeas) Cᶜ = 0 := by
    rw [show trimMeasure_T (μ := μ) T hBmeas
        = ((timeMeasure_T T).prod μ).trim (natFiltration hBmeas).predictable_le_prod from rfl,
      trim_measurableSet_eq (natFiltration hBmeas).predictable_le_prod hCpred.compl]
    exact hCprod
  have hae_trim : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), z ∈ C := by
    rw [ae_iff]; exact h0
  -- the E-limit: driftSimpleProcessLp Vₙ → driftProcessAssembled g by CLM continuity
  have hsa : Tendsto (fun n => simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop (𝓝 g) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hV
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hLp : Tendsto (fun n => driftSimpleProcessLp (μ := μ) T hBmeas (V n).val) atTop
      (𝓝 (driftProcessAssembled (μ := μ) T hBmeas g)) := by
    have hrw : (fun n => driftSimpleProcessLp (μ := μ) T hBmeas (V n).val)
        = fun n => driftProcessAssembled (μ := μ) T hBmeas (simpleAssembly_T (μ := μ) T hBmeas (V n)) :=
      funext fun n => (driftProcessAssembled_simpleAssembly T hBmeas (V n)).symm
    rw [hrw]
    exact ((driftProcessAssembled (μ := μ) T hBmeas).continuous.tendsto g).comp hsa
  -- two convergences in measure, then a.e.-uniqueness
  have hGmeas := fun n => (memLp_uncurry_driftSimpleProcess (μ := μ) T hBmeas (V n).val).1
  have hmeasG : TendstoInMeasure (trimMeasure_T (μ := μ) T hBmeas)
      (fun n => Function.uncurry (driftSimpleProcess hBmeas (V n).val)) atTop
      (Function.uncurry (driftContinuousMod T hBmeas g)) :=
    tendstoInMeasure_of_tendsto_ae hGmeas hae_trim
  have heLp : Tendsto (fun n => eLpNorm (Function.uncurry (driftSimpleProcess hBmeas (V n).val)
        - ⇑(driftProcessAssembled (μ := μ) T hBmeas g)) 2 (trimMeasure_T (μ := μ) T hBmeas))
      atTop (𝓝 0) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => Function.uncurry (driftSimpleProcess hBmeas (V n).val))
      (fun n => memLp_uncurry_driftSimpleProcess T hBmeas (V n).val)
      (⇑(driftProcessAssembled (μ := μ) T hBmeas g)) (Lp.memLp _)).mp ?_
    simp only [Lp.toLp_coeFn]
    exact hLp
  have hmeasP : TendstoInMeasure (trimMeasure_T (μ := μ) T hBmeas)
      (fun n => Function.uncurry (driftSimpleProcess hBmeas (V n).val)) atTop
      (⇑(driftProcessAssembled (μ := μ) T hBmeas g)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hGmeas (Lp.aestronglyMeasurable _) heLp
  exact (tendstoInMeasure_ae_unique hmeasG hmeasP).symm

end ItoIntegralProcessContinuousModification
end MathFin
