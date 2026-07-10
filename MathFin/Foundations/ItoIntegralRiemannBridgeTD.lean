/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralRiemannBridge

/-! # Riemann ↔ CLM bridge for bounded jointly-continuous time-dependent integrands

Generalizes `ItoIntegralRiemannBridge.itoIntegralCLM_T_of_bdd_cont` (integrand `φ ∘ B`)
to a **time-dependent** integrand `(s, ω) ↦ φ(s, B_s ω)` for bounded jointly continuous
`φ : ℝ → ℝ → ℝ`. The uniform-partition Riemann–Itô sums `∑ φ(tₖ, B_{tₖ})·ΔBₖ` converge
in `L²(μ)` to the genuine continuous Itô integral `itoIntegralCLM_T gφ`, where `gφ` is
the trim-`L²` realization of `s ↦ φ(s, B_s)`.

The structure is the bridge's verbatim: `φ(tₖ, B_{tₖ})` is a bounded adapted coefficient
(the time slot is the *deterministic* left endpoint), so the left-endpoint step process
is directly a `TBoundedSP`; the cell-collapse + path-continuity argument needs only that
`s ↦ φ(s, B_s ω)` is continuous — supplied by joint continuity composed with
`s ↦ (s, B_s ω)` — and `gφ` is obtained as the trim-`L²` limit of the step
approximations, inheriting predictability from the `TBoundedSP` approximants. The
time-dependent Itô formula consumes this at `φ = f_x`.
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralRiemannBridgeTD

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal MathFin.QuadraticVariationL2
open scoped MeasureTheory NNReal ENNReal InnerProductSpace
open ItoIntegralL2 ItoIntegralCLM ItoIsometryAdapted ItoIntegralBrownian ItoIntegralRiemannBridge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

omit hB in
/-- The uniform-partition Riemann–Itô sum for the time-dependent integrand
`(s, ω) ↦ φ(s, B_s ω)`: `∑_{k<n} φ(tₖ, B_{tₖ})·(B_{t_{k+1}} − B_{tₖ})`. -/
noncomputable def riemannφTD (_hBmeas : ∀ t, Measurable (B t)) (φ : ℝ → ℝ → ℝ) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, φ (unifPart T n k) (B (unifPart T n k) ω)
    * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)

/-- `MemLp` of the time-dependent Riemann sum (finite sum of bounded-adapted·increment
`L²` terms; the time slot of each coefficient is a deterministic node). -/
lemma memLp_riemannφTD (hBmeas : ∀ t, Measurable (B t)) {φ : ℝ → ℝ → ℝ}
    (hφ_meas : ∀ c : ℝ, Measurable (φ c))
    {C : ℝ} (hφ_bdd : ∀ t x, |φ t x| ≤ C) (T : ℝ≥0) (n : ℕ) :
    MemLp (riemannφTD hBmeas φ T n) 2 μ := by
  unfold riemannφTD
  refine memLp_finsetSum _ fun k _ ↦ ?_
  exact memLp_adapted_mul_increment hB hBmeas (unifPart_mono T n (Nat.le_succ k))
    (adaptedAt_comp_eval le_rfl (hφ_meas _))
    (MemLp.of_bound (((hφ_meas _).comp (hBmeas _)).aestronglyMeasurable) C
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hφ_bdd _ _))

omit hB in
/-- The **bounded left-endpoint step process** for the time-dependent integrand over the
uniform partition of `[0,T]`: `∑_{k<n} φ(tₖ, B_{tₖ}) · 𝟙_{(tₖ, t_{k+1}]}`. A genuine
`TBoundedSP` (`φ` bounded by `C`); the time-dependent analogue of
`ItoIntegralRiemannBridge.stepφ`. -/
noncomputable def stepφTD (hBmeas : ∀ t, Measurable (B t)) {φ : ℝ → ℝ → ℝ}
    (hφ_meas : ∀ c : ℝ, Measurable (φ c))
    {C : ℝ} (hφ_bdd : ∀ t x, |φ t x| ≤ C) (T : ℝ≥0) (n : ℕ) : TBoundedSP T hBmeas :=
  ∑ k ∈ (Finset.range n).attach,
    stepSP hBmeas (a := unifPart T n k.1) (b := unifPart T n (k.1 + 1))
      (unifPart_mono T n (Nat.le_succ k.1))
      (unifPart_le_T (Finset.mem_range.mp k.2))
      (φ := fun ω ↦ φ (unifPart T n k.1) (B (unifPart T n k.1) ω))
      ((hφ_meas _).comp (measurable_eval_natFiltration hBmeas (unifPart T n k.1)))
      (M := C) (fun ω ↦ hφ_bdd _ (B (unifPart T n k.1) ω))

omit hB in
/-- The bounded step process integrates to the time-dependent Riemann sum. -/
lemma itoSimple_stepφTD (hBmeas : ∀ t, Measurable (B t)) {φ : ℝ → ℝ → ℝ}
    (hφ_meas : ∀ c : ℝ, Measurable (φ c))
    {C : ℝ} (hφ_bdd : ∀ t x, |φ t x| ≤ C) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    itoSimple hBmeas (stepφTD hBmeas hφ_meas hφ_bdd T n).val ω
      = riemannφTD hBmeas φ T n ω := by
  rw [stepφTD, AddSubmonoidClass.coe_finsetSum, itoSimple_sum, Finset.sum_apply, riemannφTD,
    ← Finset.sum_attach (Finset.range n) (fun k ↦
      φ (unifPart T n k) (B (unifPart T n k) ω)
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [itoSimple_stepSP]

/-- **The CLM evaluated on `stepφTD` is the time-dependent Riemann sum's `L²` class.** -/
lemma itoIntegralCLM_T_stepφTD (hBmeas : ∀ t, Measurable (B t)) {φ : ℝ → ℝ → ℝ}
    (hφ_meas : ∀ c : ℝ, Measurable (φ c))
    {C : ℝ} (hφ_bdd : ∀ t x, |φ t x| ≤ C) (T : ℝ≥0) (n : ℕ) :
    itoIntegralCLM_T hB T hBmeas
        (simpleAssembly_T (μ := μ) T hBmeas (stepφTD hBmeas hφ_meas hφ_bdd T n))
      = (memLp_riemannφTD hB hBmeas hφ_meas hφ_bdd T n).toLp (riemannφTD hBmeas φ T n) := by
  rw [itoIntegralCLM_T, LinearMap.extendOfNorm_eq (simpleAssembly_T_denseRange T hBmeas)
        ⟨1, fun V ↦ by rw [one_mul]; exact (assembly_isometry_T hB T hBmeas V).le⟩]
  show itoSimpleLp hB hBmeas (stepφTD hBmeas hφ_meas hφ_bdd T n).val = _
  rw [itoSimpleLp]
  exact (MemLp.toLp_eq_toLp_iff _ _).mpr
    (Filter.Eventually.of_forall fun ω ↦ itoSimple_stepφTD hBmeas hφ_meas hφ_bdd T n ω)

omit hB in
/-- **The uncurried time-dependent step process is a sum of cell indicators**:
`uncurry (stepφTD n) (s,ω) = ∑_{k<n} 𝟙_{(tₖ,t_{k+1}]}(s)·φ(tₖ, B_{tₖ}ω)`. -/
lemma uncurry_stepφTD (hBmeas : ∀ t, Measurable (B t)) {φ : ℝ → ℝ → ℝ}
    (hφ_meas : ∀ c : ℝ, Measurable (φ c))
    {C : ℝ} (hφ_bdd : ∀ t x, |φ t x| ≤ C) (T : ℝ≥0) (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    Function.uncurry ⇑(stepφTD hBmeas hφ_meas hφ_bdd T n).val (s, ω)
      = ∑ k ∈ Finset.range n, (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
          (fun _ ↦ φ (unifPart T n k) (B (unifPart T n k) ω)) s := by
  show ⇑(stepφTD hBmeas hφ_meas hφ_bdd T n).val s ω = _
  rw [stepφTD, AddSubmonoidClass.coe_finsetSum, coe_finsetSum_apply,
    ← Finset.sum_attach (Finset.range n) (fun k ↦
      (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
        (fun _ ↦ φ (unifPart T n k) (B (unifPart T n k) ω)) s)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [SimpleProcess.apply_eq]
  simp only [stepSP]
  rw [Finsupp.sum_single_index (by simp)]
  simp

/-- **Riemann ↔ CLM bridge, time-dependent integrand.** For bounded jointly continuous
`φ : ℝ → ℝ → ℝ`, the uniform-partition Riemann–Itô sums `∑ φ(tₖ, B_{tₖ})·ΔBₖ` converge
in `L²(μ)` to `itoIntegralCLM_T gφ`, where `gφ` is the trim-`L²` realization of
`s ↦ φ(s, B_s)` (the trim-`L²` limit of the step approximations
`simpleAssembly_T (stepφTD n)`). -/
theorem itoIntegralCLM_T_of_bdd_cont_td (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 ↦ B s ω))
    {φ : ℝ → ℝ → ℝ} (hφ_cont : Continuous fun p : ℝ × ℝ ↦ φ p.1 p.2)
    {C : ℝ} (hφ_bdd : ∀ t x, |φ t x| ≤ C) (T : ℝ≥0) :
    ∃ gφ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (⇑gφ =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun z ↦ φ z.1 (B z.1 z.2)) ∧
      Tendsto (fun n ↦ (memLp_riemannφTD hB hBmeas
          (fun _c ↦ (hφ_cont.comp (continuous_const.prodMk continuous_id)).measurable)
          hφ_bdd T n).toLp (riemannφTD hBmeas φ T n))
        atTop (𝓝 (itoIntegralCLM_T hB T hBmeas gφ)) := by
  have hφ_meas : ∀ c : ℝ, Measurable (φ c) := fun c ↦
    (hφ_cont.comp (continuous_const.prodMk continuous_id)).measurable
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hφ_bdd 0 0)
  -- the pathwise composite `s ↦ φ(s, B_s ω)` is continuous
  have hψ_cont : ∀ ω, Continuous fun s : ℝ≥0 ↦ φ s (B s ω) := fun ω ↦
    hφ_cont.comp ((NNReal.continuous_coe).prodMk (hBcont ω))
  set f : ℕ → ℝ≥0 × Ω → ℝ := fun n ↦ Function.uncurry ⇑(stepφTD hBmeas hφ_meas hφ_bdd T n).val
    with hf
  set gφ_fn : ℝ≥0 × Ω → ℝ := fun z ↦ φ z.1 (B z.1 z.2) with hgφ
  have hf_memLp : ∀ n, MemLp (f n) 2 (trimMeasure_T (μ := μ) T hBmeas) :=
    fun n ↦ memLp_uncurry_trim_T T hBmeas _
  -- `trimMeasure_T` is supported on `(0,T] × Ω`
  have hsupp : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), z.1 ∈ Set.Ioc 0 T := by
    rw [trimMeasure_T_eq_restrict]
    refine ae_restrict_of_forall_mem
      (MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := natFiltration hBmeas) 0 T
        MeasurableSet.univ) (fun z hz ↦ hz.1)
  -- the uncurried step functions converge a.e. to `φ(·, B)` (cell collapse + continuity
  -- of the composite path `s ↦ φ(s, B_s ω)` — the frozen time and space slots converge
  -- together because both are evaluated along the same `tₖ → s`)
  have hae_conv : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
      Tendsto (fun n ↦ f n z) atTop (𝓝 (gφ_fn z)) := by
    filter_upwards [hsupp] with z hz
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp (hψ_cont z.2).continuousAt ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / δ)
    refine ⟨max N 1, fun n hn ↦ ?_⟩
    have hn1 : 0 < n := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hn)
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    obtain ⟨k, _, hval, hclose⟩ :=
      cell_collapse T n hn1 z.1 hz (fun j ↦ φ (unifPart T n j) (B (unifPart T n j) z.2))
    rw [show f n z = ∑ j ∈ Finset.range n,
          (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))).indicator
            (fun _ ↦ φ (unifPart T n j) (B (unifPart T n j) z.2)) z.1
        from uncurry_stepφTD hBmeas hφ_meas hφ_bdd T n z.1 z.2, hval]
    refine hδc ?_
    rw [NNReal.dist_eq]
    have hn_gt : (T : ℝ) / δ < n := lt_of_lt_of_le hN (by exact_mod_cast hnN)
    calc |(unifPart T n k : ℝ) - (z.1 : ℝ)| ≤ (T : ℝ) / n := hclose
      _ < δ := by
          rw [div_lt_iff₀ (by exact_mod_cast hn1 : (0 : ℝ) < (n : ℝ)), mul_comm]
          exact (div_lt_iff₀ hδ).mp hn_gt
  -- `gφ_fn ∈ L²` (predictable as an a.e. limit of predictable simple processes)
  have hgφ_aesm := aestronglyMeasurable_of_tendsto_ae atTop
    (fun n ↦ (hf_memLp n).aestronglyMeasurable) hae_conv
  have hgφ_memLp : MemLp gφ_fn 2 (trimMeasure_T (μ := μ) T hBmeas) :=
    MemLp.of_bound hgφ_aesm C (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hφ_bdd _ _)
  -- uniform bound `|f n| ≤ C` a.e.
  have hf_bdd : ∀ n, ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), |f n z| ≤ C := by
    intro n
    filter_upwards [hsupp] with z hz
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · simp only [hf, hn0]
      rw [show Function.uncurry ⇑(stepφTD hBmeas hφ_meas hφ_bdd T 0).val (z.1, z.2)
            = ∑ j ∈ Finset.range 0, (Set.Ioc (unifPart T 0 j) (unifPart T 0 (j + 1))).indicator
                (fun _ ↦ φ (unifPart T 0 j) (B (unifPart T 0 j) z.2)) z.1
          from uncurry_stepφTD hBmeas hφ_meas hφ_bdd T 0 z.1 z.2]
      simpa using hC0
    · obtain ⟨k, _, hval, _⟩ :=
        cell_collapse T n hn z.1 hz (fun j ↦ φ (unifPart T n j) (B (unifPart T n j) z.2))
      rw [show f n z = ∑ j ∈ Finset.range n,
            (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))).indicator
              (fun _ ↦ φ (unifPart T n j) (B (unifPart T n j) z.2)) z.1
          from uncurry_stepφTD hBmeas hφ_meas hφ_bdd T n z.1 z.2, hval]
      exact hφ_bdd _ _
  -- L² convergence of the integrals (dominated convergence, bound `(2C)²`)
  have hint : Tendsto (fun n ↦ ∫ z, (f n z - gφ_fn z) ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas))
      atTop (𝓝 0) := by
    have hlim : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
        Tendsto (fun n ↦ (f n z - gφ_fn z) ^ 2) atTop (𝓝 ((fun _ ↦ (0 : ℝ)) z)) := by
      filter_upwards [hae_conv] with z hz
      simpa using ((hz.sub_const (gφ_fn z)).pow 2)
    have hbnd : ∀ n, ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
        ‖(f n z - gφ_fn z) ^ 2‖ ≤ (2 * C) ^ 2 := by
      intro n
      filter_upwards [hf_bdd n] with z hzb
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hgb : |gφ_fn z| ≤ C := by rw [hgφ]; exact hφ_bdd _ _
      have : |f n z - gφ_fn z| ≤ 2 * C := (abs_sub _ _).trans (by linarith)
      nlinarith [this, abs_nonneg (f n z - gφ_fn z), sq_abs (f n z - gφ_fn z)]
    have := tendsto_integral_of_dominated_convergence (fun _ ↦ (2 * C) ^ 2)
      (fun n ↦ ((hf_memLp n).aestronglyMeasurable.sub hgφ_aesm).pow 2)
      (integrable_const _) hbnd hlim
    simpa using this
  refine ⟨hgφ_memLp.toLp gφ_fn, MemLp.coeFn_toLp _, ?_⟩
  have hLp : Tendsto (fun n ↦ (hf_memLp n).toLp (f n)) atTop (𝓝 (hgφ_memLp.toLp gφ_fn)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (tendsto_norm_toLp_sub' hf_memLp hgφ_memLp hint)
  have key : ∀ n, itoIntegralCLM_T hB T hBmeas ((hf_memLp n).toLp (f n))
      = (memLp_riemannφTD hB hBmeas hφ_meas hφ_bdd T n).toLp (riemannφTD hBmeas φ T n) := fun n ↦
    itoIntegralCLM_T_stepφTD hB hBmeas hφ_meas hφ_bdd T n
  exact (Filter.tendsto_congr key).mp
    (((itoIntegralCLM_T hB T hBmeas).continuous.tendsto _).comp hLp)

end ItoIntegralRiemannBridgeTD
end MathFin
