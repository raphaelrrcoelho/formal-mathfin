/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralProcessGeneral
public import MathFin.Foundations.ItoIntegralProcessLocalMartingale
public import BrownianMotion.StochasticIntegral.DoobLp

/-!
# Continuous modification of the general-integrand Itô process (the gate)

The first pathwise-regularity result for the **general** integrand: a continuous
modification of the `L²`-valued process `t ↦ itoProcessCLM T t φ` on a finite
horizon `[0,T]`, packaged as a continuous (hence local) martingale.

B1b (`ItoIntegralProcessGeneral`) built the general-integrand Itô integral as an
`Lp ℝ 2 μ`-valued process — adapted, an `L²` martingale, `L²`-continuous in `t`,
but with no honest sample paths. B3 (`ItoIntegralProcessLocalMartingale`) gave
pathwise continuity only for the **simple** integrand. This file closes the gap:
approximate `φ` by simple processes `Vₙ` (density, B1b); each `Vₙ ● B` has
continuous paths (B3); Degenne's continuous-time weak-type maximal inequality
(`maximal_ineq_norm`) + Borel–Cantelli on a fast subsequence make `(Vₙ ● B)`
a.s.-uniformly Cauchy on `[0,T]`, so the uniform limit is pathwise continuous,
equals `(φ ● B)_t` a.e. at every `t` (a **modification**), and is a continuous
`L²` martingale — hence an `IsLocalMartingale`, the localization gateway.

## Coherence

Pure consumption + assembly. Degenne's general càdlàg modification
(`exists_modification_isCadlag`) is `sorry`-backed, so this result is not a
duplicate; and the `L²`-continuity + Doob route yields a genuinely **continuous**
(not merely càdlàg) version. Nothing of the isometry, density, or martingale
property is reproved — the maximal inequality is Degenne's, the continuous
approximants are B3's, the density is B1b's.

See `docs/superpowers/specs/2026-06-26-ito-continuous-modification-design.md`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcessContinuousModification

open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-! ## Phase 1 — the maximal estimate -/

/-- **Continuous-time weak-type maximal bound** for the elementary Itô integral.
The process `t ↦ (V ● B)_t` is a continuous `L²` martingale (B1a's martingale
property + B3's path continuity), so Degenne's continuous-time maximal inequality
`maximal_ineq_norm` applies directly at `n := T`, where `⨆ i : Set.Iic T` is the
running supremum over the whole interval `[0,T]`. -/
theorem itoSimpleProcess_maximal_weak (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (T : ℝ≥0) (ε : ℝ) :
    ε • μ.real {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V i ω‖}
      ≤ ∫ ω in {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V i ω‖},
          ‖itoSimpleProcess hBmeas V T ω‖ ∂μ :=
  maximal_ineq_norm (itoSimpleProcess_isMartingale hB hBmeas V) ε T
    (fun ω _ => (itoSimpleProcess_pathContinuous hBmeas hBcont V ω).continuousWithinAt)

/-- **Chebyshev form** of the maximal bound, with the `L²` terminal norm on the
right. For a `T`-bounded simple process `V`, the probability that the running
maximum of `(V ● B)` over `[0,T]` reaches `ε` is at most
`ε⁻¹ · ‖simpleAssembly_T V‖`: combine the weak bound with `∫_S ‖(V●B)_T‖ ≤
∫ ‖(V●B)_T‖ ≤ ‖(V●B)_T‖_{L²}` (set-integral monotonicity + `L¹ ≤ L²` on the
probability space) and the terminal Itô isometry
`‖(V●B)_T‖_{L²} = ‖simpleAssembly_T V‖`. -/
theorem itoSimpleProcess_maximal_prob (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (T : ℝ≥0) (V : TBoundedSP T hBmeas) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V.val i ω‖}
      ≤ ε⁻¹ * ‖simpleAssembly_T (μ := μ) T hBmeas V‖ := by
  set f := itoSimpleProcess hBmeas V.val T with hf_def
  set S := {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V.val i ω‖} with hS
  have hf : MemLp f 2 μ := memLp_itoSimpleProcess hB hBmeas V.val T
  have hfi : Integrable f μ := hf.integrable (by norm_num)
  have hweak := itoSimpleProcess_maximal_weak hB hBmeas hBcont V.val T ε
  -- ∫_S ‖f‖ ≤ ∫ ‖f‖
  have hsub : ∫ ω in S, ‖f ω‖ ∂μ ≤ ∫ ω, ‖f ω‖ ∂μ :=
    setIntegral_le_integral hfi.norm (ae_of_all _ fun ω => norm_nonneg _)
  -- ∫ ‖f‖ ≤ ‖f‖_{L²} = ‖itoSimpleProcessLp V T‖
  have hL2 : ∫ ω, ‖f ω‖ ∂μ ≤ ‖itoSimpleProcessLp hB hBmeas V.val T‖ := by
    rw [itoSimpleProcessLp, Lp.norm_toLp,
      ← ENNReal.toReal_ofReal (integral_nonneg fun ω => norm_nonneg _),
      ofReal_integral_norm_eq_lintegral_enorm hfi, ← eLpNorm_one_eq_lintegral_enorm]
    exact ENNReal.toReal_mono hf.2.ne (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hf.1)
  -- terminal Itô isometry on the simple embedding
  have hterm : ‖itoSimpleProcessLp hB hBmeas V.val T‖ = ‖simpleAssembly_T (μ := μ) T hBmeas V‖ := by
    rw [← itoProcessCLM_simpleAssembly_T hB T T hBmeas V, itoProcessCLM_norm_terminal hB T hBmeas]
  -- assemble: ε * μ.real S ≤ ‖simpleAssembly_T V‖, then divide by ε > 0
  rw [smul_eq_mul] at hweak
  have hchain : ε * μ.real S ≤ ‖simpleAssembly_T (μ := μ) T hBmeas V‖ :=
    hweak.trans (hsub.trans (hL2.trans_eq hterm))
  calc μ.real S = ε⁻¹ * (ε * μ.real S) := by field_simp
    _ ≤ ε⁻¹ * ‖simpleAssembly_T (μ := μ) T hBmeas V‖ :=
        mul_le_mul_of_nonneg_left hchain (inv_nonneg.mpr hε.le)

/-! ## Phase 2 — approximating subsequence, Borel–Cantelli, continuous limit -/

omit hB in
/-- **Fast approximating subsequence.** By density of the simple-process
embedding (`simpleAssembly_T_denseRange`), every predictable integrand `φ` is
approximated by `T`-bounded simple processes `Vₙ` with
`‖simpleAssembly_T Vₙ − φ‖ ≤ 2⁻ⁿ`. -/
theorem approxSeq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ∃ V : ℕ → TBoundedSP T hBmeas,
      ∀ n, ‖simpleAssembly_T (μ := μ) T hBmeas (V n) - φ‖ ≤ (2⁻¹ : ℝ) ^ n := by
  have hd := simpleAssembly_T_denseRange (μ := μ) T hBmeas
  have hex : ∀ n : ℕ, ∃ V : TBoundedSP T hBmeas,
      ‖simpleAssembly_T (μ := μ) T hBmeas V - φ‖ ≤ (2⁻¹ : ℝ) ^ n := by
    intro n
    obtain ⟨V, hV⟩ := hd.exists_dist_lt φ (by positivity : (0 : ℝ) < (2⁻¹ : ℝ) ^ n)
    exact ⟨V, by rw [← dist_eq_norm, dist_comm]; exact hV.le⟩
  choose V hV using hex
  exact ⟨V, hV⟩

omit hB in
/-- The elementary process Itô integral is **subtractive** in the simple
process (from B1a's `itoSimpleProcess_add` / `_neg`). -/
lemma itoSimpleProcess_sub (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) :
    itoSimpleProcess hBmeas (V - W) t
      = itoSimpleProcess hBmeas V t - itoSimpleProcess hBmeas W t := by
  rw [sub_eq_add_neg, itoSimpleProcess_add, itoSimpleProcess_neg, ← sub_eq_add_neg]

/-- **Summable maximal tail.** For the fast subsequence `V` (`approxSeq`), the
probabilities that the running max of the consecutive difference
`(Vₙ − Vₙ₊₁) ● B` over `[0,T]` reaches `εₙ := (3/4)ⁿ` are summable: each is
`≤ εₙ⁻¹ · ‖simpleAssembly_T (Vₙ − Vₙ₊₁)‖ ≤ εₙ⁻¹ · 2·2⁻ⁿ = 2·(2/3)ⁿ`. The choice
`εₙ = (3/4)ⁿ ∈ (2⁻¹, 1)ⁿ` makes both `Σ εₙ⁻¹·2⁻ⁿ` and `Σ εₙ` converge. -/
theorem summable_maximal_tail (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (V : ℕ → TBoundedSP T hBmeas)
    (hV : ∀ n, ‖simpleAssembly_T (μ := μ) T hBmeas (V n) - φ‖ ≤ (2⁻¹ : ℝ) ^ n) :
    Summable (fun n => μ.real {ω | (3 / 4 : ℝ) ^ n ≤
      ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas (V n - V (n + 1)).val i ω‖}) := by
  refine Summable.of_nonneg_of_le (fun n => measureReal_nonneg) (fun n => ?_)
    ((summable_geometric_of_lt_one (r := 2 / 3) (by norm_num) (by norm_num)).mul_left 2)
  -- per-term: μ.real {…} ≤ 2 * (2/3)ⁿ
  refine (itoSimpleProcess_maximal_prob hB hBmeas hBcont T (V n - V (n + 1))
    (ε := (3 / 4 : ℝ) ^ n) (by positivity)).trans ?_
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
          rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) n]
  calc ((3 / 4 : ℝ) ^ n)⁻¹ * ‖simpleAssembly_T (μ := μ) T hBmeas (V n - V (n + 1))‖
      ≤ ((3 / 4 : ℝ) ^ n)⁻¹ * (2 * (2⁻¹ : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = 2 * (2 / 3 : ℝ) ^ n := by
        rw [← inv_pow, mul_comm (2 : ℝ) ((2⁻¹ : ℝ) ^ n), ← mul_assoc, ← mul_pow,
          show ((3 / 4 : ℝ)⁻¹ * 2⁻¹) = 2 / 3 from by norm_num, mul_comm]

/-- **A.s. eventual smallness (Borel–Cantelli).** Since the maximal tail is
summable, for almost every `ω` the running maximum of the consecutive difference
`(Vₙ − Vₙ₊₁) ● B` over `[0,T]` is eventually below `(3/4)ⁿ`. This is the pathwise
input to the uniform-Cauchy argument. -/
theorem ae_eventually_sup_lt (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (V : ℕ → TBoundedSP T hBmeas)
    (hV : ∀ n, ‖simpleAssembly_T (μ := μ) T hBmeas (V n) - φ‖ ≤ (2⁻¹ : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      (⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas (V n - V (n + 1)).val i ω‖) < (3 / 4 : ℝ) ^ n := by
  set A : ℕ → Set Ω := fun n => {ω | (3 / 4 : ℝ) ^ n ≤
    ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas (V n - V (n + 1)).val i ω‖} with hA
  have hconv : (∑' n, μ (A n)) ≠ ∞ := by
    have heq : ∀ n, μ (A n) = ENNReal.ofReal (μ.real (A n)) :=
      fun n => (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => measureReal_nonneg)
      (summable_maximal_tail hB T hBmeas hBcont φ V hV)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hconv] with ω hω
  filter_upwards [hω] with n hn
  rwa [hA, Set.mem_setOf_eq, not_le] at hn

/-! ## Phase 3 — continuous limit, modification, capstone -/

omit hB in
/-- **The running-max keystone.** For `i ≤ T`, the value `‖(W ● B)_i ω‖` is
bounded by the running maximum over `[0,T]`. The supremum is genuine (not the
junk value of an unbounded family): `(W ● B)_· ω` is continuous (B3) and `[0,T]`
is compact, so the family is bounded above. This unlocks the pointwise control of
consecutive differences. -/
lemma norm_le_iSup_Iic (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (W : SimpleProcess ℝ (natFiltration hBmeas)) (ω : Ω) {i : ℝ≥0} (hi : i ≤ T) :
    ‖itoSimpleProcess hBmeas W i ω‖
      ≤ ⨆ j : Set.Iic T, ‖itoSimpleProcess hBmeas W (j : ℝ≥0) ω‖ := by
  have hcont : Continuous fun j : Set.Iic T => ‖itoSimpleProcess hBmeas W (j : ℝ≥0) ω‖ :=
    (continuous_norm.comp (itoSimpleProcess_pathContinuous hBmeas hBcont W ω)).comp
      continuous_subtype_val
  have hIic : (Set.Iic T : Set ℝ≥0) = Set.Icc 0 T := by
    ext x; simp only [Set.mem_Iic, Set.mem_Icc, zero_le, true_and]
  haveI : CompactSpace (Set.Iic T) := isCompact_iff_compactSpace.mp (hIic ▸ isCompact_Icc)
  exact le_ciSup (isCompact_range hcont).bddAbove ⟨i, hi⟩

/-- The pathwise limit process: for each `t, ω` the limit (if it exists) of the
approximating simple integrals `(Vₙ ● B)_t ω`, junk off the convergence set. The
subsequence `Vₙ` is `approxSeq`'s choice for `φ`. -/
noncomputable def itoContinuousMod (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop fun n => itoSimpleProcess hBmeas ((approxSeq T hBmeas φ).choose n).val t ω

/-- **Pointwise a.s. convergence.** For almost every `ω` and every `t ≤ T`, the
approximating sequence `(Vₙ ● B)_t ω` converges to `itoContinuousMod φ t ω`. The
consecutive distances are eventually `< (3/4)ⁿ` (a.s., uniformly in `t ≤ T`, by
`ae_eventually_sup_lt` + the running-max keystone + linearity), hence summable,
so the sequence is Cauchy in the complete space `ℝ`. -/
theorem itoContinuousMod_tendsto (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ T →
      Tendsto (fun n => itoSimpleProcess hBmeas ((approxSeq T hBmeas φ).choose n).val t ω) atTop
        (𝓝 (itoContinuousMod T hBmeas φ t ω)) := by
  set V := (approxSeq T hBmeas φ).choose with hVdef
  have hV := (approxSeq T hBmeas φ).choose_spec
  filter_upwards [ae_eventually_sup_lt hB T hBmeas hBcont φ V hV] with ω hω
  intro t ht
  have hcauchy : CauchySeq (fun n => itoSimpleProcess hBmeas (V n).val t ω) := by
    apply cauchySeq_of_summable_dist
    obtain ⟨N, hN⟩ := eventually_atTop.mp hω
    rw [← summable_nat_add_iff N]
    refine Summable.of_nonneg_of_le (fun n => dist_nonneg) (fun n => ?_)
      (f := fun n => (3 / 4 : ℝ) ^ (n + N)) ?_
    · rw [dist_eq_norm]
      have hcoe : ((V (n + N) - V (n + N + 1)).val : SimpleProcess ℝ (natFiltration hBmeas))
          = (V (n + N)).val - (V (n + N + 1)).val := rfl
      have hlin : itoSimpleProcess hBmeas (V (n + N)).val t ω
            - itoSimpleProcess hBmeas (V (n + N + 1)).val t ω
          = itoSimpleProcess hBmeas (V (n + N) - V (n + N + 1)).val t ω := by
        rw [hcoe]
        exact (congrFun (itoSimpleProcess_sub hBmeas (V (n + N)).val (V (n + N + 1)).val t) ω).symm
      rw [hlin]
      exact (norm_le_iSup_Iic T hBmeas hBcont (V (n + N) - V (n + N + 1)).val ω ht).trans
        (hN (n + N) (Nat.le_add_left N n)).le
    · simp_rw [pow_add]
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  simpa only [itoContinuousMod, hVdef] using hcauchy.tendsto_limUnder

/-- **The modification (Task 7).** For every `t ≤ T`, the pathwise limit
`itoContinuousMod φ t` agrees almost everywhere with the `L²` process value
`itoProcessCLM T t φ`. Two convergences to compare: `Fₙ → itoContinuousMod` a.e.
(pointwise, above) and `Fₙ → itoProcessCLM T t φ` in measure (from the `L²`
convergence `itoSimpleProcessLp Vₙ t = itoProcessCLM T t (simpleAssembly_T Vₙ) →
itoProcessCLM T t φ`, via the bridge + CLM continuity). In-measure limits are
a.e.-unique. -/
theorem itoContinuousMod_modification (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {t : ℝ≥0} (ht : t ≤ T) :
    (fun ω => itoContinuousMod T hBmeas φ t ω) =ᵐ[μ] itoProcessCLM hB T t hBmeas φ := by
  set V := (approxSeq T hBmeas φ).choose with hVdef
  have hV := (approxSeq T hBmeas φ).choose_spec
  set F : ℕ → Ω → ℝ := fun n ω => itoSimpleProcess hBmeas (V n).val t ω with hF
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) μ :=
    fun n => (memLp_itoSimpleProcess hB hBmeas (V n).val t).1
  -- (a) F → itoContinuousMod a.e. ⟹ in measure
  have hmeasG : TendstoInMeasure μ F atTop (fun ω => itoContinuousMod T hBmeas φ t ω) := by
    refine tendstoInMeasure_of_tendsto_ae hFmeas ?_
    filter_upwards [itoContinuousMod_tendsto hB T hBmeas hBcont φ] with ω hω using hω t ht
  -- (b) F → ⇑(itoProcessCLM T t φ) in measure, from L² convergence
  have hsa : Tendsto (fun n => simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop (𝓝 φ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hV
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hLp : Tendsto (fun n => itoSimpleProcessLp hB hBmeas (V n).val t) atTop
      (𝓝 (itoProcessCLM hB T t hBmeas φ)) := by
    have hrw : (fun n => itoSimpleProcessLp hB hBmeas (V n).val t)
        = fun n => itoProcessCLM hB T t hBmeas (simpleAssembly_T (μ := μ) T hBmeas (V n)) :=
      funext fun n => (itoProcessCLM_simpleAssembly_T hB T t hBmeas (V n)).symm
    rw [hrw]
    exact ((itoProcessCLM hB T t hBmeas).continuous.tendsto φ).comp hsa
  have heLp : Tendsto (fun n => eLpNorm (F n - ⇑(itoProcessCLM hB T t hBmeas φ)) 2 μ) atTop (𝓝 0) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F
      (fun n => memLp_itoSimpleProcess hB hBmeas (V n).val t)
      (⇑(itoProcessCLM hB T t hBmeas φ)) (Lp.memLp _)).mp ?_
    simp only [Lp.toLp_coeFn]
    exact hLp
  have hmeasH : TendstoInMeasure μ F atTop (⇑(itoProcessCLM hB T t hBmeas φ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hFmeas
      (Lp.aestronglyMeasurable _) heLp
  exact tendstoInMeasure_ae_unique hmeasG hmeasH

end ItoIntegralProcessContinuousModification
end MathFin
