/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralRiemannBridge
public import MathFin.Foundations.AdaptedProcessToLp

/-! # Riemann ↔ CLM bridge for a bounded **adapted continuous** integrand `θ`

`ItoIntegralRiemannBridge.itoIntegralCLM_T_of_bdd_cont` handles the special integrand `φ ∘ B`
(a bounded continuous function of the current Brownian value). This file generalizes it to an
**arbitrary bounded adapted continuous** process `θ : ℝ≥0 → Ω → ℝ` — the integrand shape the
general adapted Girsanov theorem needs (the market price of risk is a genuine adapted process,
not a function of `B_s` alone).

For such a `θ` the uniform-partition Riemann–Itô sums `∑_{k<n} θ(tₖ)·(B_{t_{k+1}} − B_{tₖ})`
converge in `L²(μ)` to `itoIntegralCLM_T (processToLp θ)` — the genuine continuous Itô integral
of the σ-realization `processToLp θ` (`AdaptedProcessToLp`). The proof mirrors the `φ∘B` template
line-for-line, with two changes: the bounded coefficient `φ(B_{tₖ})` becomes the general adapted
`θ(tₖ)` (`𝓕_{tₖ}`-measurable + bounded — exactly `stepSP`'s requirement), and the `L²`-membership
of the Riemann sum is obtained by plain domination (bounded · increment) rather than the
increment-independence route, so no `AdaptedAt`-vs-`natFiltration` bridge is needed. The a.e.
convergence reuses the same partition-cell collapse (`cell_collapse`) — now against `θ`'s own
path continuity.

## Main results

* `itoIntegralCLM_T_of_bdd_adapted_cont` — `∑ θ(tₖ)·ΔBₖ → itoIntegralCLM_T (processToLp θ)` in `L²`.
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
/-- The uniform-partition Riemann–Itô sum for a general adapted integrand `θ`:
`∑_{k<n} θ(tₖ)·(B_{t_{k+1}} − B_{tₖ})`. -/
noncomputable def riemannσ (θ : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, θ (unifPart T n k) ω
    * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)

omit [IsProbabilityMeasure μ] in
/-- `MemLp` of the adapted Riemann sum, by **domination**: each term `θ(tₖ)·ΔBₖ` is a bounded
(`|θ| ≤ C`) measurable coefficient times an `L²` increment, hence `L²` (`‖θ·Δ‖ ≤ ‖C·Δ‖`). No
increment-independence / `AdaptedAt` needed for membership. -/
lemma memLp_riemannσ (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    MemLp (riemannσ (B := B) θ T n) 2 μ := by
  unfold riemannσ
  refine memLp_finsetSum _ fun k _ => ?_
  have hΔ : MemLp (fun ω => B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) 2 μ :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hθm : StronglyMeasurable (θ (unifPart T n k)) :=
    (hadap (unifPart T n k)).mono ((natFiltration hBmeas).le _)
  refine (hΔ.const_mul C).mono
    (hθm.aestronglyMeasurable.mul hΔ.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hbdd (unifPart T n k) ω).trans (le_abs_self C)) (abs_nonneg _)

omit hB in
/-- The **bounded left-endpoint step process** for a general adapted `θ`:
`∑_{k<n} θ(tₖ) · 𝟙_{(tₖ, t_{k+1}]}`. A `TBoundedSP` — each coefficient `θ(tₖ)` is
`𝓕_{tₖ}`-measurable (adaptedness) and bounded by `C`. -/
noncomputable def stepσ (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) : TBoundedSP T hBmeas :=
  ∑ k ∈ (Finset.range n).attach,
    stepSP hBmeas (a := unifPart T n k.1) (b := unifPart T n (k.1 + 1))
      (unifPart_mono T n (Nat.le_succ k.1))
      (unifPart_le_T (Finset.mem_range.mp k.2))
      (φ := θ (unifPart T n k.1))
      (hadap (unifPart T n k.1)).measurable
      (M := C) (fun ω => hbdd (unifPart T n k.1) ω)

omit hB in
/-- The step process integrates to the `θ`-Riemann sum. -/
lemma itoSimple_stepσ (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    itoSimple hBmeas (stepσ hBmeas hadap hbdd T n).val ω = riemannσ (B := B) θ T n ω := by
  rw [stepσ, AddSubmonoidClass.coe_finsetSum, itoSimple_sum, Finset.sum_apply, riemannσ,
    ← Finset.sum_attach (Finset.range n) (fun k =>
      θ (unifPart T n k) ω * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [itoSimple_stepSP]

/-- **The CLM evaluated on `stepσ` is the `θ`-Riemann sum's `L²` class.** -/
lemma itoIntegralCLM_T_stepσ (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    itoIntegralCLM_T hB T hBmeas
        (simpleAssembly_T (μ := μ) T hBmeas (stepσ hBmeas hadap hbdd T n))
      = (memLp_riemannσ hB hBmeas hadap hbdd T n).toLp (riemannσ (B := B) θ T n) := by
  rw [itoIntegralCLM_T, LinearMap.extendOfNorm_eq (simpleAssembly_T_denseRange T hBmeas)
        ⟨1, fun V => by rw [one_mul]; exact (assembly_isometry_T hB T hBmeas V).le⟩]
  show itoSimpleLp hB hBmeas (stepσ hBmeas hadap hbdd T n).val = _
  rw [itoSimpleLp]
  exact (MemLp.toLp_eq_toLp_iff _ _).mpr
    (Filter.Eventually.of_forall fun ω => itoSimple_stepσ hBmeas hadap hbdd T n ω)

omit hB in
/-- **The uncurried step process is a sum of cell indicators**:
`uncurry (stepσ n) (s,ω) = ∑_{k<n} 𝟙_{(tₖ,t_{k+1}]}(s)·θ(tₖ)ω`. -/
lemma uncurry_stepσ (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    Function.uncurry ⇑(stepσ hBmeas hadap hbdd T n).val (s, ω)
      = ∑ k ∈ Finset.range n, (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
          (fun _ => θ (unifPart T n k) ω) s := by
  show ⇑(stepσ hBmeas hadap hbdd T n).val s ω = _
  rw [stepσ, AddSubmonoidClass.coe_finsetSum, coe_finsetSum_apply,
    ← Finset.sum_attach (Finset.range n) (fun k =>
      (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
        (fun _ => θ (unifPart T n k) ω) s)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [SimpleProcess.apply_eq]
  simp only [stepSP]
  rw [Finsupp.sum_single_index (by simp)]
  simp

/-- **Riemann ↔ CLM bridge, adapted case.** For a bounded (`|θ| ≤ C`) adapted (`𝓕`-measurable in
each `t`) continuous (every path `s ↦ θ_s ω`) integrand, the uniform-partition Riemann–Itô sums
`∑ θ(tₖ)·ΔBₖ` converge in `L²(μ)` to `itoIntegralCLM_T (processToLp θ)`. -/
theorem itoIntegralCLM_T_of_bdd_adapted_cont (hBmeas : ∀ t, Measurable (B t))
    {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    Tendsto (fun n => (memLp_riemannσ hB hBmeas hadap hbdd T n).toLp (riemannσ (B := B) θ T n))
      atTop (𝓝 (itoIntegralCLM_T hB T hBmeas
        (processToLp (μ := μ) T hBmeas hadap hcont hbdd))) := by
  classical
  set f : ℕ → ℝ≥0 × Ω → ℝ := fun n => Function.uncurry ⇑(stepσ hBmeas hadap hbdd T n).val with hf
  set gθ_fn : ℝ≥0 × Ω → ℝ := Function.uncurry θ with hgθ
  have hf_memLp : ∀ n, MemLp (f n) 2 (trimMeasure_T (μ := μ) T hBmeas) :=
    fun n => memLp_uncurry_trim_T T hBmeas _
  have hgθ_memLp : MemLp gθ_fn 2 (trimMeasure_T (μ := μ) T hBmeas) :=
    memLp_uncurry_of_bdd_adapted_cont T hBmeas hadap hcont hbdd
  -- `trimMeasure_T` is supported on `(0,T] × Ω`
  have hsupp : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), z.1 ∈ Set.Ioc 0 T := by
    rw [trimMeasure_T_eq_restrict]
    refine ae_restrict_of_forall_mem
      (MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := natFiltration hBmeas) 0 T
        MeasurableSet.univ) (fun z hz => hz.1)
  -- the uncurried step functions converge a.e. to `θ` (cell collapse + path continuity)
  have hae_conv : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
      Tendsto (fun n => f n z) atTop (𝓝 (gθ_fn z)) := by
    filter_upwards [hsupp] with z hz
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp (hcont z.2).continuousAt ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / δ)
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 0 < n := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hn)
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    obtain ⟨k, _, hval, hclose⟩ :=
      cell_collapse T n hn1 z.1 hz (fun j => θ (unifPart T n j) z.2)
    rw [show f n z = ∑ j ∈ Finset.range n,
          (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))).indicator
            (fun _ => θ (unifPart T n j) z.2) z.1
        from uncurry_stepσ hBmeas hadap hbdd T n z.1 z.2, hval]
    refine hδc ?_
    rw [NNReal.dist_eq]
    have hn_gt : (T : ℝ) / δ < n := lt_of_lt_of_le hN (by exact_mod_cast hnN)
    calc |(unifPart T n k : ℝ) - (z.1 : ℝ)| ≤ (T : ℝ) / n := hclose
      _ < δ := by
          rw [div_lt_iff₀ (by exact_mod_cast hn1 : (0 : ℝ) < (n : ℝ)), mul_comm]
          exact (div_lt_iff₀ hδ).mp hn_gt
  -- uniform bound `|f n| ≤ C` a.e.
  have hf_bdd : ∀ n, ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), |f n z| ≤ C := by
    intro n
    filter_upwards [hsupp] with z hz
    have hC0 : (0 : ℝ) ≤ C := (abs_nonneg _).trans (hbdd 0 z.2)
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · simp only [hf, hn0]
      rw [show Function.uncurry ⇑(stepσ hBmeas hadap hbdd T 0).val (z.1, z.2)
            = ∑ j ∈ Finset.range 0, (Set.Ioc (unifPart T 0 j) (unifPart T 0 (j + 1))).indicator
                (fun _ => θ (unifPart T 0 j) z.2) z.1 from uncurry_stepσ hBmeas hadap hbdd T 0 z.1 z.2]
      simpa using hC0
    · obtain ⟨k, _, hval, _⟩ :=
        cell_collapse T n hn z.1 hz (fun j => θ (unifPart T n j) z.2)
      rw [show f n z = ∑ j ∈ Finset.range n,
            (Set.Ioc (unifPart T n j) (unifPart T n (j + 1))).indicator
              (fun _ => θ (unifPart T n j) z.2) z.1
          from uncurry_stepσ hBmeas hadap hbdd T n z.1 z.2, hval]
      exact hbdd _ _
  -- L² convergence of the integrals (dominated convergence, bound `(2C)²`)
  have hint : Tendsto (fun n => ∫ z, (f n z - gθ_fn z) ^ 2 ∂(trimMeasure_T (μ := μ) T hBmeas))
      atTop (𝓝 0) := by
    have hlim : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
        Tendsto (fun n => (f n z - gθ_fn z) ^ 2) atTop (𝓝 ((fun _ => (0 : ℝ)) z)) := by
      filter_upwards [hae_conv] with z hz
      simpa using ((hz.sub_const (gθ_fn z)).pow 2)
    have hbnd : ∀ n, ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
        ‖(f n z - gθ_fn z) ^ 2‖ ≤ (2 * C) ^ 2 := by
      intro n
      filter_upwards [hf_bdd n, hsupp] with z hzb hz
      have hC0 : (0 : ℝ) ≤ C := (abs_nonneg _).trans (hbdd 0 z.2)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hgb : |gθ_fn z| ≤ C := by rw [hgθ]; exact hbdd _ _
      have : |f n z - gθ_fn z| ≤ 2 * C := (abs_sub _ _).trans (by linarith)
      nlinarith [this, abs_nonneg (f n z - gθ_fn z), sq_abs (f n z - gθ_fn z)]
    have := tendsto_integral_of_dominated_convergence (fun _ => (2 * C) ^ 2)
      (fun n => ((hf_memLp n).aestronglyMeasurable.sub hgθ_memLp.aestronglyMeasurable).pow 2)
      (integrable_const _) hbnd hlim
    simpa using this
  have hLp : Tendsto (fun n => (hf_memLp n).toLp (f n)) atTop (𝓝 (hgθ_memLp.toLp gθ_fn)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (tendsto_norm_toLp_sub' hf_memLp hgθ_memLp hint)
  have key : ∀ n, itoIntegralCLM_T hB T hBmeas ((hf_memLp n).toLp (f n))
      = (memLp_riemannσ hB hBmeas hadap hbdd T n).toLp (riemannσ (B := B) θ T n) := fun n =>
    itoIntegralCLM_T_stepσ hB hBmeas hadap hbdd T n
  have htarget : hgθ_memLp.toLp gθ_fn = processToLp (μ := μ) T hBmeas hadap hcont hbdd := rfl
  rw [← htarget]
  exact (Filter.tendsto_congr key).mp
    (((itoIntegralCLM_T hB T hBmeas).continuous.tendsto _).comp hLp)

end ItoIntegralRiemannBridge
end MathFin
