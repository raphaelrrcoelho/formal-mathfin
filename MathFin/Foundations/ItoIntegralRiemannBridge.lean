/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralBrownian

/-! # Riemann ↔ CLM bridge for bounded continuous integrands

Generalizes `ItoIntegralBrownian.itoIntegralCLM_T_brownian` (integrand `s ↦ B_s`) to a
bounded continuous integrand `φ ∘ B`. For bounded continuous `φ`, the uniform-partition
Riemann–Itô sums `∑ φ(B_{tₖ})·ΔBₖ` converge in `L²(μ)` to the genuine continuous Itô
integral `itoIntegralCLM_T gφ`, where `gφ` is the trim-`L²` realization of `s ↦ φ(B_s)`.

Because `φ` is **bounded**, `φ(B_{tₖ})` is a bounded adapted coefficient, so the step
process `∑ φ(B_{tₖ})·𝟙_{(tₖ,t_{k+1}]}` is directly a `TBoundedSP` — no `clampM`
truncation and no double limit (the unbounded `s ↦ B_s` case in `ItoIntegralBrownian`
needed both). `gφ` is obtained as the trim-`L²` limit of the step approximations
(`simpleAssembly_T (stepφ n)`), which sidesteps proving `φ∘B` predictable directly:
predictability is inherited from the `TBoundedSP` approximants and `Lp` closedness.
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralRiemannBridge

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal MathFin.QuadraticVariationL2
open scoped MeasureTheory NNReal ENNReal InnerProductSpace
open ItoIntegralL2 ItoIntegralCLM ItoIsometryAdapted ItoIntegralBrownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

omit hB in
/-- The uniform-partition Riemann–Itô sum for integrand `φ∘B`:
`∑_{k<n} φ(B_{tₖ})·(B_{t_{k+1}} − B_{tₖ})`. -/
noncomputable def riemannφ (_hBmeas : ∀ t, Measurable (B t)) (φ : ℝ → ℝ) (T : ℝ≥0) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, φ (B (unifPart T n k) ω)
    * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)

/-- `MemLp` of the φ-Riemann sum (finite sum of bounded-adapted·increment `L²` terms). -/
lemma memLp_riemannφ (hBmeas : ∀ t, Measurable (B t)) {φ : ℝ → ℝ} (hφ_meas : Measurable φ)
    {C : ℝ} (hφ_bdd : ∀ x, |φ x| ≤ C) (T : ℝ≥0) (n : ℕ) :
    MemLp (riemannφ hBmeas φ T n) 2 μ := by
  unfold riemannφ
  refine memLp_finsetSum _ fun k _ ↦ ?_
  exact memLp_adapted_mul_increment hB hBmeas (unifPart_mono T n (Nat.le_succ k))
    (adaptedAt_comp_eval le_rfl hφ_meas)
    (MemLp.of_bound ((hφ_meas.comp (hBmeas _)).aestronglyMeasurable) C
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hφ_bdd _))

omit hB in
/-- The **bounded left-endpoint step process** over the uniform partition of `[0,T]`:
`∑_{k<n} φ(B_{tₖ}) · 𝟙_{(tₖ, t_{k+1}]}`. A genuine `TBoundedSP` (φ bounded by `C`); the
clamp-free analogue of `ItoIntegralBrownian.truncStep`. -/
noncomputable def stepφ (hBmeas : ∀ t, Measurable (B t)) {φ : ℝ → ℝ} (hφ_meas : Measurable φ)
    {C : ℝ} (hφ_bdd : ∀ x, |φ x| ≤ C) (T : ℝ≥0) (n : ℕ) : TBoundedSP T hBmeas :=
  ∑ k ∈ (Finset.range n).attach,
    stepSP hBmeas (a := unifPart T n k.1) (b := unifPart T n (k.1 + 1))
      (unifPart_mono T n (Nat.le_succ k.1))
      (unifPart_le_T (Finset.mem_range.mp k.2))
      (φ := fun ω ↦ φ (B (unifPart T n k.1) ω))
      (hφ_meas.comp (measurable_eval_natFiltration hBmeas (unifPart T n k.1)))
      (M := C) (fun ω ↦ hφ_bdd (B (unifPart T n k.1) ω))

omit hB in
/-- The bounded step process integrates to the φ-Riemann sum. -/
lemma itoSimple_stepφ (hBmeas : ∀ t, Measurable (B t)) {φ : ℝ → ℝ} (hφ_meas : Measurable φ)
    {C : ℝ} (hφ_bdd : ∀ x, |φ x| ≤ C) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    itoSimple hBmeas (stepφ hBmeas hφ_meas hφ_bdd T n).val ω = riemannφ hBmeas φ T n ω := by
  rw [stepφ, AddSubmonoidClass.coe_finsetSum, itoSimple_sum, Finset.sum_apply, riemannφ,
    ← Finset.sum_attach (Finset.range n) (fun k ↦
      φ (B (unifPart T n k) ω) * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [itoSimple_stepSP]

/-- **The CLM evaluated on `stepφ` is the φ-Riemann sum's `L²` class.** The clamp-free
analogue of `ItoIntegralBrownian.itoIntegralCLM_T_truncStep`. -/
lemma itoIntegralCLM_T_stepφ (hBmeas : ∀ t, Measurable (B t)) {φ : ℝ → ℝ} (hφ_meas : Measurable φ)
    {C : ℝ} (hφ_bdd : ∀ x, |φ x| ≤ C) (T : ℝ≥0) (n : ℕ) :
    itoIntegralCLM_T hB T hBmeas
        (simpleAssembly_T (μ := μ) T hBmeas (stepφ hBmeas hφ_meas hφ_bdd T n))
      = (memLp_riemannφ hB hBmeas hφ_meas hφ_bdd T n).toLp (riemannφ hBmeas φ T n) := by
  rw [itoIntegralCLM_T, LinearMap.extendOfNorm_eq (simpleAssembly_T_denseRange T hBmeas)
        ⟨1, fun V ↦ by rw [one_mul]; exact (assembly_isometry_T hB T hBmeas V).le⟩]
  show itoSimpleLp hB hBmeas (stepφ hBmeas hφ_meas hφ_bdd T n).val = _
  rw [itoSimpleLp]
  exact (MemLp.toLp_eq_toLp_iff _ _).mpr
    (Filter.Eventually.of_forall fun ω ↦ itoSimple_stepφ hBmeas hφ_meas hφ_bdd T n ω)

omit hB in
/-- The simple-process coercion is additive over a finite sum (pointwise). -/
lemma coe_finsetSum_apply {ι' : Type*} (hBmeas : ∀ t, Measurable (B t)) (s : Finset ι')
    (W : ι' → SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (i : ℝ≥0) (ω : Ω) :
    ⇑(∑ k ∈ s, W k) i ω = ∑ k ∈ s, ⇑(W k) i ω := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, SimpleProcess.coe_add, Pi.add_apply, Pi.add_apply, ih,
      Finset.sum_insert ha]

omit hB in
/-- **The uncurried bounded step process is a sum of cell indicators**:
`uncurry (stepφ n) (s,ω) = ∑_{k<n} 𝟙_{(tₖ,t_{k+1}]}(s)·φ(B_{tₖ}ω)`. -/
lemma uncurry_stepφ (hBmeas : ∀ t, Measurable (B t)) {φ : ℝ → ℝ} (hφ_meas : Measurable φ)
    {C : ℝ} (hφ_bdd : ∀ x, |φ x| ≤ C) (T : ℝ≥0) (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    Function.uncurry ⇑(stepφ hBmeas hφ_meas hφ_bdd T n).val (s, ω)
      = ∑ k ∈ Finset.range n, (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
          (fun _ ↦ φ (B (unifPart T n k) ω)) s := by
  show ⇑(stepφ hBmeas hφ_meas hφ_bdd T n).val s ω = _
  rw [stepφ, AddSubmonoidClass.coe_finsetSum, coe_finsetSum_apply,
    ← Finset.sum_attach (Finset.range n) (fun k ↦
      (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
        (fun _ ↦ φ (B (unifPart T n k) ω)) s)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [SimpleProcess.apply_eq]
  simp only [stepSP]
  rw [Finsupp.sum_single_index (by simp)]
  simp

omit hB in
/-- On `(0,T]`, the cell-indicator sum collapses to the unique containing cell's value,
whose left endpoint is within `T/n` of `s` (the `Nat.find` partition-cell argument). -/
lemma cell_collapse (T : ℝ≥0) (n : ℕ) (hn : 0 < n) (s : ℝ≥0) (hs : s ∈ Set.Ioc 0 T)
    (v : ℕ → ℝ) :
    ∃ k, k < n ∧ (∑ j ∈ Finset.range n,
        (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))).indicator (fun _ ↦ v j) s) = v k
      ∧ |(unifPart T n k : ℝ) - s| ≤ (T : ℝ) / n := by
  have hmono : Monotone (unifPart T n) := unifPart_mono T n
  have hlast : unifPart T n n = T := by
    have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp only [unifPart, div_self hne, one_mul]
  have hgap : ∀ k, (unifPart T n (k + 1) : ℝ) - unifPart T n k = (T : ℝ) / n := fun k ↦ by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp only [unifPart]; push_cast; field_simp; ring
  have hex : ∃ k, s ≤ unifPart T n (k + 1) :=
    ⟨n - 1, by rw [Nat.sub_add_cancel hn, hlast]; exact hs.2⟩
  set K := Nat.find hex
  have hKspec : s ≤ unifPart T n (K + 1) := Nat.find_spec hex
  have hKle : K ≤ n - 1 := Nat.find_le (by rw [Nat.sub_add_cancel hn, hlast]; exact hs.2)
  have hKlt : K < n := lt_of_le_of_lt hKle (Nat.sub_lt hn one_pos)
  have hlow : unifPart T n K < s := by
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · rw [hK0]; simpa [unifPart] using hs.1
    · have hmin := Nat.find_min hex (m := K - 1) (Nat.sub_lt hKpos one_pos)
      have hK1 : K - 1 + 1 = K := by omega
      rw [hK1] at hmin
      exact not_le.mp hmin
  refine ⟨K, hKlt, ?_, ?_⟩
  · rw [Finset.sum_eq_single K]
    · rw [Set.indicator_of_mem]; exact ⟨hlow, hKspec⟩
    · intro l _ hlK
      apply Set.indicator_of_notMem
      rintro ⟨hl1, hl2⟩
      rcases lt_or_gt_of_ne hlK with hlt | hgt
      · exact (Nat.find_min hex hlt) hl2
      · exact absurd hl1 (not_lt.mpr (le_trans hKspec (hmono (Nat.succ_le_of_lt hgt))))
    · intro hKnot; exact absurd (Finset.mem_range.mpr hKlt) hKnot
  · rw [abs_le]
    have hcoe_low : (unifPart T n K : ℝ) < s := by exact_mod_cast hlow
    have hcoe_hi : (s : ℝ) ≤ unifPart T n (K + 1) := by exact_mod_cast hKspec
    have hg := hgap K
    have hTn : (0 : ℝ) ≤ (T : ℝ) / n := div_nonneg (NNReal.coe_nonneg T) (Nat.cast_nonneg n)
    exact ⟨by nlinarith [hcoe_low, hcoe_hi, hg], by nlinarith [hcoe_low, hTn]⟩

omit hB in
/-- If `∫ (Fₙ − G)² → 0` then `‖⟦Fₙ⟧ − ⟦G⟧‖ → 0`, any measure. The single-fixed-limit
variant of `ItoIntegralBrownian.tendsto_norm_toLp_sub` (which compares two *sequences*
`Fₙ, Gₙ`); kept as a separate lemma because the `G`-shape genuinely differs. The generic
`L²` facts `ItoIntegralL2.lp_two_norm_sq` / `ItoIntegralBrownian.lp_dist_sq` it rests on. -/
lemma tendsto_norm_toLp_sub' {α : Type*} {m : MeasurableSpace α} {ν : Measure α}
    {F : ℕ → α → ℝ} {G : α → ℝ} (hF : ∀ n, MemLp (F n) 2 ν) (hG : MemLp G 2 ν)
    (h : Tendsto (fun n ↦ ∫ z, (F n z - G z) ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ‖(hF n).toLp (F n) - hG.toLp G‖) atTop (𝓝 0) := by
  have heq : (fun n ↦ ‖(hF n).toLp (F n) - hG.toLp G‖)
      = fun n ↦ Real.sqrt (∫ z, (F n z - G z) ^ 2 ∂ν) := by
    funext n; rw [← lp_dist_sq (hF n) hG, Real.sqrt_sq (norm_nonneg _)]
  rw [heq]
  simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp h

/-- **Riemann ↔ CLM bridge.** For bounded continuous `φ`, the uniform-partition
Riemann–Itô sums `∑ φ(B_{tₖ})·ΔBₖ` converge in `L²(μ)` to `itoIntegralCLM_T gφ`, where
`gφ` is the trim-`L²` realization of `s ↦ φ(B_s)` (the trim-`L²` limit of the step
approximations `simpleAssembly_T (stepφ n)`). -/
theorem itoIntegralCLM_T_of_bdd_cont (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 ↦ B s ω))
    {φ : ℝ → ℝ} (hφ_cont : Continuous φ) {C : ℝ} (hφ_bdd : ∀ x, |φ x| ≤ C) (T : ℝ≥0) :
    ∃ gφ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      Tendsto (fun n ↦ (memLp_riemannφ hB hBmeas hφ_cont.measurable hφ_bdd T n).toLp
          (riemannφ hBmeas φ T n))
        atTop (𝓝 (itoIntegralCLM_T hB T hBmeas gφ)) := by
  have hφ_meas : Measurable φ := hφ_cont.measurable
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hφ_bdd 0)
  set f : ℕ → ℝ≥0 × Ω → ℝ := fun n ↦ Function.uncurry ⇑(stepφ hBmeas hφ_meas hφ_bdd T n).val with hf
  set gφ_fn : ℝ≥0 × Ω → ℝ := fun z ↦ φ (B z.1 z.2) with hgφ
  have hf_memLp : ∀ n, MemLp (f n) 2 (trimMeasure_T (μ := μ) T hBmeas) :=
    fun n ↦ memLp_uncurry_trim_T T hBmeas _
  -- `trimMeasure_T` is supported on `(0,T] × Ω`
  have hsupp : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), z.1 ∈ Set.Ioc 0 T := by
    rw [trimMeasure_T_eq_restrict]
    refine ae_restrict_of_forall_mem
      (MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := natFiltration hBmeas) 0 T
        MeasurableSet.univ) (fun z hz ↦ hz.1)
  -- the uncurried step functions converge a.e. to `φ∘B` (cell collapse + path continuity)
  have hae_conv : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
      Tendsto (fun n ↦ f n z) atTop (𝓝 (gφ_fn z)) := by
    filter_upwards [hsupp] with z hz
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδc⟩ :=
      Metric.continuousAt_iff.mp (hφ_cont.comp (hBcont z.2)).continuousAt ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / δ)
    refine ⟨max N 1, fun n hn ↦ ?_⟩
    have hn1 : 0 < n := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hn)
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    obtain ⟨k, _, hval, hclose⟩ :=
      cell_collapse T n hn1 z.1 hz (fun j ↦ φ (B (unifPart T n j) z.2))
    rw [show f n z = ∑ j ∈ Finset.range n,
          (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))).indicator
            (fun _ ↦ φ (B (unifPart T n j) z.2)) z.1
        from uncurry_stepφ hBmeas hφ_meas hφ_bdd T n z.1 z.2, hval]
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
    MemLp.of_bound hgφ_aesm C (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hφ_bdd _)
  -- uniform bound `|f n| ≤ C` a.e.
  have hf_bdd : ∀ n, ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), |f n z| ≤ C := by
    intro n
    filter_upwards [hsupp] with z hz
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · simp only [hf, hn0]
      rw [show Function.uncurry ⇑(stepφ hBmeas hφ_meas hφ_bdd T 0).val (z.1, z.2)
            = ∑ j ∈ Finset.range 0, (Set.Ioc (unifPart T 0 j) (unifPart T 0 (j + 1))).indicator
                (fun _ ↦ φ (B (unifPart T 0 j) z.2)) z.1 from uncurry_stepφ hBmeas hφ_meas hφ_bdd T 0 z.1 z.2]
      simpa using hC0
    · obtain ⟨k, _, hval, _⟩ :=
        cell_collapse T n hn z.1 hz (fun j ↦ φ (B (unifPart T n j) z.2))
      rw [show f n z = ∑ j ∈ Finset.range n,
            (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))).indicator
              (fun _ ↦ φ (B (unifPart T n j) z.2)) z.1
          from uncurry_stepφ hBmeas hφ_meas hφ_bdd T n z.1 z.2, hval]
      exact hφ_bdd _
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
      have hgb : |gφ_fn z| ≤ C := by rw [hgφ]; exact hφ_bdd _
      have : |f n z - gφ_fn z| ≤ 2 * C := (abs_sub _ _).trans (by linarith)
      nlinarith [this, abs_nonneg (f n z - gφ_fn z), sq_abs (f n z - gφ_fn z)]
    have := tendsto_integral_of_dominated_convergence (fun _ ↦ (2 * C) ^ 2)
      (fun n ↦ ((hf_memLp n).aestronglyMeasurable.sub hgφ_aesm).pow 2)
      (integrable_const _) hbnd hlim
    simpa using this
  refine ⟨hgφ_memLp.toLp gφ_fn, ?_⟩
  have hLp : Tendsto (fun n ↦ (hf_memLp n).toLp (f n)) atTop (𝓝 (hgφ_memLp.toLp gφ_fn)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (tendsto_norm_toLp_sub' hf_memLp hgφ_memLp hint)
  have key : ∀ n, itoIntegralCLM_T hB T hBmeas ((hf_memLp n).toLp (f n))
      = (memLp_riemannφ hB hBmeas hφ_meas hφ_bdd T n).toLp (riemannφ hBmeas φ T n) := fun n ↦
    itoIntegralCLM_T_stepφ hB hBmeas hφ_meas hφ_bdd T n
  exact (Filter.tendsto_congr key).mp
    (((itoIntegralCLM_T hB T hBmeas).continuous.tendsto _).comp hLp)

end ItoIntegralRiemannBridge
end MathFin
