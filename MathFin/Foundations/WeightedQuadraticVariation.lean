/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin.Foundations.QuadraticVariationL2
import MathFin.Foundations.ItoIntegralL2

/-! # Weighted quadratic variation — `∑ g(B_{tₖ})(ΔBₖ)² → ∫₀ᵀ g(B_s) ds` in `L²`

The second-order term of Itô's lemma. For bounded continuous `g` (the use case is
`g = f''`), the `g(B)`-weighted sum of squared Brownian increments along the uniform
partition of `[0,T]` converges in `L²(μ)` to the pathwise integral `∫₀ᵀ g(B_s) ds`.

This generalizes `QuadraticVariationL2.tendsto_qv` (the `g ≡ 1` case, limit `T`) from a
constant to a continuous weight. The proof splits the difference into

* **Term I** (fluctuation) `∑ g(B_{tₖ})·((ΔBₖ)² − Δtₖ)`, which → 0 in `L²` by the same
  weak-Markov orthogonality + Gaussian-kurtosis engine as `tendsto_qv`, now carrying the
  `𝓕_{tₖ}`-measurable bounded weight `g(B_{tₖ})`; and
* **Term II** (Riemann sum of a continuous path)
  `∑ g(B_{tₖ})·Δtₖ − ∫₀ᵀ g(B_s) ds → 0`, pathwise by continuity of `s ↦ g(B_s)`, then
  in `L²` by dominated convergence (`|·| ≤ C·T`).
-/

namespace MathFin

open MeasureTheory ProbabilityTheory Filter ItoIsometryAdapted QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  [hB : IsPreBrownian B μ]

/-- For `χ` adapted to `𝓕_{t₀}` and in `L²`, the centered squared increment integrates
against `χ` to zero: `E[χ·((ΔB)² − (t₁−t₀))] = 0`. The `χ ≡ 1` case is
`integral_increment_centered_mean`; the general adapted `L²` weight is what makes the
weighted-QV fluctuation's cross terms vanish. Immediate from the isometry kernel
`integral_adapted_mul_increment_sq` (`E[χ·(ΔB)²] = E[χ]·(t₁−t₀)`) minus `(t₁−t₀)·E[χ]`. -/
private theorem integral_adapted_mul_centered_sq
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {χ : Ω → ℝ} (hχ : AdaptedAt B t₀ χ) :
    ∫ ω, χ ω * ((B t₁ ω - B t₀ ω) ^ 2 - ((t₁ : ℝ) - t₀)) ∂μ = 0 := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hχm : Measurable χ := hχ.measurable hBmeas
  have hYm : Measurable (fun ω => (B t₁ ω - B t₀ ω) ^ 2 - ((t₁ : ℝ) - t₀)) := by fun_prop
  have hindep : IndepFun χ (fun ω => (B t₁ ω - B t₀ ω) ^ 2 - ((t₁ : ℝ) - t₀)) μ := by
    have h := (adapted_indepFun_increment (μ := μ) hBmeas ht hχ).comp
      (φ := (id : ℝ → ℝ)) (ψ := fun x => x ^ 2 - ((t₁ : ℝ) - t₀)) measurable_id (by fun_prop)
    simpa [Function.comp_def] using h
  rw [hindep.integral_fun_mul_eq_mul_integral hχm.aestronglyMeasurable hYm.aestronglyMeasurable,
      integral_increment_centered_mean ht, mul_zero]

/-- **Term I, per-`n` bound.** The `L²` norm² of the weighted fluctuation
`∑ₖ g(B_{tₖ})·((ΔBₖ)² − Δtₖ)` is at most `∑ₖ C²·2(Δtₖ)²`: the cross terms vanish
(`integral_adapted_mul_centered_sq`), and each diagonal term is `≤ C²·2(Δtₖ)²`
(pointwise `g² ≤ C²` plus `integral_increment_sq_centered`). The weighted analogue of
`sum_increment_sq_sub_sq_integral`. -/
private theorem weighted_fluctuation_integral_le
    (hBmeas : ∀ t, Measurable (B t)) {g : ℝ → ℝ} (hg_meas : Measurable g)
    {C : ℝ} (hg_bdd : ∀ x, |g x| ≤ C) (T : ℝ≥0) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n,
        g (B (unifPart T n k) ω)
          * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
             - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) ^ 2 ∂μ
      ≤ ∑ k ∈ Finset.range n,
          C ^ 2 * (2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2) := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  classical
  have hmono : Monotone (unifPart T n) := fun i j hij => by simp only [unifPart]; gcongr
  set t : ℕ → ℝ≥0 := unifPart T n with ht_def
  set Y : ℕ → Ω → ℝ := fun k ω => (B (t (k + 1)) ω - B (t k) ω) ^ 2 - ((t (k + 1) : ℝ) - t k)
    with hY_def
  set a : ℕ → Ω → ℝ := fun k ω => g (B (t k) ω) * Y k ω with ha_def
  have hC : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hg_bdd 0)
  have hYL2 : ∀ k, MemLp (Y k) 2 μ := fun k => memLp_increment_sq_centered_two (t k) (t (k + 1)) _
  have ha_aesm : ∀ k, AEStronglyMeasurable (a k) μ := fun k =>
    ((hg_meas.comp (hBmeas (t k))).aestronglyMeasurable).mul (hYL2 k).aestronglyMeasurable
  have haL2 : ∀ k, MemLp (a k) 2 μ := fun k =>
    MemLp.mono ((hYL2 k).const_mul C) (ha_aesm k) (ae_of_all _ fun ω => by
      simp only [ha_def, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hg_bdd _) (abs_nonneg _))
  have hint : ∀ k l, Integrable (fun ω => a k ω * a l ω) μ :=
    fun k l => (haL2 k).integrable_mul (haL2 l)
  have hY_adapt : ∀ k, AdaptedAt B (t (k + 1)) (Y k) := fun k =>
    adaptedAt_increment_sq_sub (hmono (Nat.le_succ k)) le_rfl _
  have ha_adapt : ∀ k, AdaptedAt B (t (k + 1)) (a k) := fun k =>
    (adaptedAt_comp_eval (hmono (Nat.le_succ k)) hg_meas).mul (hY_adapt k)
  have hcross : ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n, l ≠ k →
      ∫ ω, a k ω * a l ω ∂μ = 0 := by
    intro k _ l _ hlk
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · have hχ : AdaptedAt B (t k) (fun ω => a l ω * g (B (t k) ω)) :=
        ((ha_adapt l).mono (hmono (Nat.succ_le_of_lt hlt))).mul (adaptedAt_comp_eval le_rfl hg_meas)
      have h := integral_adapted_mul_centered_sq (μ := μ) hBmeas (hmono (Nat.le_succ k)) hχ
      rw [show (fun ω => a k ω * a l ω)
            = (fun ω => (a l ω * g (B (t k) ω))
                * ((B (t (k + 1)) ω - B (t k) ω) ^ 2 - ((t (k + 1) : ℝ) - t k)))
          from funext fun ω => by simp only [ha_def, hY_def]; ring]
      exact h
    · have hχ : AdaptedAt B (t l) (fun ω => a k ω * g (B (t l) ω)) :=
        ((ha_adapt k).mono (hmono (Nat.succ_le_of_lt hgt))).mul (adaptedAt_comp_eval le_rfl hg_meas)
      have h := integral_adapted_mul_centered_sq (μ := μ) hBmeas (hmono (Nat.le_succ l)) hχ
      rw [show (fun ω => a k ω * a l ω)
            = (fun ω => (a k ω * g (B (t l) ω))
                * ((B (t (l + 1)) ω - B (t l) ω) ^ 2 - ((t (l + 1) : ℝ) - t l)))
          from funext fun ω => by simp only [ha_def, hY_def]; ring]
      exact h
  have hdiag : ∀ k ∈ Finset.range n,
      ∫ ω, a k ω * a k ω ∂μ ≤ C ^ 2 * (2 * ((t (k + 1) : ℝ) - t k) ^ 2) := by
    intro k _
    have hgsq : ∀ ω, (g (B (t k) ω)) ^ 2 ≤ C ^ 2 := fun ω => by
      nlinarith [hg_bdd (B (t k) ω), abs_nonneg (g (B (t k) ω)), sq_abs (g (B (t k) ω))]
    have hle : ∀ ω, a k ω * a k ω ≤ C ^ 2 * (Y k ω * Y k ω) := fun ω => by
      simp only [ha_def]
      nlinarith [hgsq ω, mul_self_nonneg (Y k ω)]
    calc ∫ ω, a k ω * a k ω ∂μ
        ≤ ∫ ω, C ^ 2 * (Y k ω * Y k ω) ∂μ :=
          integral_mono (hint k k) (((hYL2 k).integrable_mul (hYL2 k)).const_mul _) hle
      _ = C ^ 2 * ∫ ω, Y k ω * Y k ω ∂μ := integral_const_mul _ _
      _ = C ^ 2 * (2 * ((t (k + 1) : ℝ) - t k) ^ 2) := by
          rw [show (fun ω => Y k ω * Y k ω)
                = (fun ω => ((B (t (k + 1)) ω - B (t k) ω) ^ 2 - ((t (k + 1) : ℝ) - t k)) ^ 2)
              from funext fun ω => by simp only [hY_def]; ring,
              integral_increment_sq_centered (hmono (Nat.le_succ k))]
  calc ∫ ω, (∑ k ∈ Finset.range n, a k ω) ^ 2 ∂μ
      = ∫ ω, ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, a k ω * a l ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show (∑ k ∈ Finset.range n, a k ω) ^ 2
          = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, a k ω * a l ω
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, ∫ ω, a k ω * a l ω ∂μ := by
        rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
        exact Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun l _ => hint k l
    _ ≤ ∑ k ∈ Finset.range n, C ^ 2 * (2 * ((t (k + 1) : ℝ) - t k) ^ 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.sum_eq_single k (fun l hl hlk => hcross k hk l hl hlk) fun h => absurd hk h]
        exact hdiag k hk

/-- **Term I → 0 in `L²`.** The weighted fluctuation `∑ₖ g(B_{tₖ})·((ΔBₖ)² − Δtₖ)`
vanishes in `L²(μ)` as the mesh shrinks, with explicit rate `2C²T²/n`. Squeeze of the
per-`n` bound `weighted_fluctuation_integral_le` (the weighted analogue of the `tendsto_qv`
rate `2T²/n`). -/
private theorem tendsto_weighted_fluctuation
    (hBmeas : ∀ t, Measurable (B t)) {g : ℝ → ℝ} (hg_meas : Measurable g)
    {C : ℝ} (hg_bdd : ∀ x, |g x| ≤ C) (T : ℝ≥0) :
    Tendsto (fun n : ℕ =>
        ∫ ω, (∑ k ∈ Finset.range n,
            g (B (unifPart T n k) ω)
              * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
                 - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  refine squeeze_zero' (g := fun n : ℕ => 2 * C ^ 2 * (T : ℝ) ^ 2 / n)
    (Eventually.of_forall fun n => integral_nonneg fun ω => sq_nonneg _) ?_
    (by simpa using tendsto_const_div_atTop_nhds_zero_nat (2 * C ^ 2 * (T : ℝ) ^ 2))
  filter_upwards [eventually_gt_atTop 0] with n hn
  refine (weighted_fluctuation_integral_le hBmeas hg_meas hg_bdd T n).trans (le_of_eq ?_)
  have hΔ : ∀ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) / n :=
    fun k _ => by simp only [unifPart]; push_cast; field_simp; ring
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [show (∑ k ∈ Finset.range n, C ^ 2 * (2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2))
        = ∑ _k ∈ Finset.range n, C ^ 2 * (2 * ((T : ℝ) / n) ^ 2)
      from Finset.sum_congr rfl fun k hk => by rw [hΔ k hk],
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- **Riemann sums of a continuous, bounded path converge to its integral.** For
`h : ℝ≥0 → ℝ` continuous and bounded by `C`, the left-endpoint Riemann sums along the
uniform partition of `[0,T]` converge to `∫₀ᵀ h ∂timeMeasure`. Mathlib has no Riemann-sum
lemma, so this is built from scratch: the left-endpoint step function integrates (over
`timeMeasure`, via `timeMeasure_Ioc`) to the Riemann sum, converges pointwise to `h` on
`(0,T]` by continuity (each `s` lies in a unique partition cell whose left endpoint is
within `T/n`), and dominated convergence (bound `C`, finite measure `timeMeasure (0,T]=T`)
upgrades this to convergence of the integrals. -/
private theorem tendsto_riemann_continuous {h : ℝ≥0 → ℝ} (hcont : Continuous h)
    {C : ℝ} (hbdd : ∀ s, |h s| ≤ C) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
        h (unifPart T n k) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      atTop (𝓝 (∫ s in Set.Ioc 0 T, h s ∂ItoIntegralL2.timeMeasure)) := by
  classical
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hbdd 0)
  set ν := ItoIntegralL2.timeMeasure with hν
  haveI hfin : IsFiniteMeasure (ν.restrict (Set.Ioc 0 T)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hν,
        ItoIntegralL2.timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  -- partition facts
  have hmono : ∀ n, Monotone (unifPart T n) := fun n a b hab => by
    simp only [unifPart]; gcongr
  have hzero : ∀ n, unifPart T n 0 = 0 := fun n => by simp [unifPart]
  have hlast : ∀ n, 0 < n → unifPart T n n = T := fun n hn => by
    have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp only [unifPart, div_self hne, one_mul]
  have hle_T : ∀ n k, k ≤ n → unifPart T n k ≤ T := fun n k hk => by
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0; rw [Nat.le_zero.mp hk, hzero]; exact zero_le'
    · exact (hmono n hk).trans_eq (hlast n hn)
  have hgap : ∀ n, 0 < n → ∀ k, (unifPart T n (k + 1) : ℝ) - unifPart T n k = (T : ℝ) / n :=
    fun n hn k => by
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [unifPart]; push_cast; field_simp; ring
  -- the left-endpoint step function
  set F : ℕ → ℝ≥0 → ℝ := fun n s => ∑ k ∈ Finset.range n,
    (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator (fun _ => h (unifPart T n k)) s
    with hF
  -- on `(0,T]`, the step function equals the unique cell's left value, within `T/n` of `s`
  have hkey : ∀ n, 0 < n → ∀ s ∈ Set.Ioc (0 : ℝ≥0) T, ∃ k, k < n ∧
      F n s = h (unifPart T n k) ∧ |(unifPart T n k : ℝ) - s| ≤ (T : ℝ) / n := by
    intro n hn s hs
    have hex : ∃ k, s ≤ unifPart T n (k + 1) :=
      ⟨n - 1, by rw [Nat.sub_add_cancel hn, hlast n hn]; exact hs.2⟩
    set K := Nat.find hex with hK
    have hKspec : s ≤ unifPart T n (K + 1) := Nat.find_spec hex
    have hKle : K ≤ n - 1 := Nat.find_le (by rw [Nat.sub_add_cancel hn, hlast n hn]; exact hs.2)
    have hKlt : K < n := lt_of_le_of_lt hKle (Nat.sub_lt hn one_pos)
    have hlow : unifPart T n K < s := by
      rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · rw [hK0, hzero]; exact hs.1
      · have hmin := Nat.find_min hex (m := K - 1) (Nat.sub_lt hKpos one_pos)
        have hK1 : K - 1 + 1 = K := by omega
        rw [hK1] at hmin
        exact not_le.mp hmin
    refine ⟨K, hKlt, ?_, ?_⟩
    · simp only [hF]
      rw [Finset.sum_eq_single K]
      · rw [Set.indicator_of_mem]; exact ⟨hlow, hKspec⟩
      · intro l _ hlK
        apply Set.indicator_of_notMem
        rintro ⟨hl1, hl2⟩
        rcases lt_or_gt_of_ne hlK with hlt | hgt
        · exact (Nat.find_min hex hlt) hl2
        · exact absurd hl1 (not_lt.mpr (le_trans hKspec (hmono n (Nat.succ_le_of_lt hgt))))
      · intro hKnot; exact absurd (Finset.mem_range.mpr hKlt) hKnot
    · rw [abs_le]
      have hcoe_low : (unifPart T n K : ℝ) < s := by exact_mod_cast hlow
      have hcoe_hi : (s : ℝ) ≤ unifPart T n (K + 1) := by exact_mod_cast hKspec
      have hg := hgap n hn K
      have hTn : (0 : ℝ) ≤ (T : ℝ) / n := div_nonneg (NNReal.coe_nonneg T) (Nat.cast_nonneg n)
      constructor
      · nlinarith [hcoe_low, hcoe_hi, hg]
      · nlinarith [hcoe_low, hTn]
  -- pointwise bound on `(0,T]`
  have hbound : ∀ n, ∀ s ∈ Set.Ioc (0 : ℝ≥0) T, ‖F n s‖ ≤ C := by
    intro n s hs
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · simp only [hF, hn0, Finset.range_zero, Finset.sum_empty, norm_zero]; exact hC0
    · obtain ⟨k, _, hval, _⟩ := hkey n hn s hs
      rw [hval, Real.norm_eq_abs]; exact hbdd _
  -- pointwise convergence `F n s → h s` on `(0,T]`
  have hptwise : ∀ s ∈ Set.Ioc (0 : ℝ≥0) T, Tendsto (fun n => F n s) atTop (𝓝 (h s)) := by
    intro s hs
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hcont.continuousAt ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / δ)
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 0 < n := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hn)
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    obtain ⟨k, _, hval, hclose⟩ := hkey n hn1 s hs
    rw [hval]
    refine hδc ?_
    rw [NNReal.dist_eq]
    have hn_gt : (T : ℝ) / δ < n := lt_of_lt_of_le hN (by exact_mod_cast hnN)
    calc |(unifPart T n k : ℝ) - s| ≤ (T : ℝ) / n := hclose
      _ < δ := by
          rw [div_lt_iff₀ (by exact_mod_cast hn1 : (0 : ℝ) < (n : ℝ)), mul_comm]
          exact (div_lt_iff₀ hδ).mp hn_gt
  -- the step function integrates to the Riemann sum
  have hstep_integ : ∀ n, ∫ s in Set.Ioc 0 T, F n s ∂ν
      = ∑ k ∈ Finset.range n, h (unifPart T n k) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    intro n
    have hInt : ∀ k ∈ Finset.range n,
        Integrable ((Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
          (fun _ => h (unifPart T n k))) (ν.restrict (Set.Ioc 0 T)) :=
      fun k _ => (integrable_const _).indicator measurableSet_Ioc
    simp only [hF]
    rw [integral_finsetSum _ hInt]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul,
      show Set.Ioc (0 : ℝ≥0) T ∩ Set.Ioc (unifPart T n k) (unifPart T n (k + 1))
          = Set.Ioc (unifPart T n k) (unifPart T n (k + 1)) by
        rw [Set.Ioc_inter_Ioc, max_eq_right zero_le', min_eq_right (hle_T n (k + 1) hkn)],
      measureReal_def, hν, ItoIntegralL2.timeMeasure_Ioc, ENNReal.toReal_ofReal
        (sub_nonneg.mpr (by exact_mod_cast hmono n (Nat.le_succ k)))]
    ring
  -- dominated convergence assembles the result
  have hmeas : ∀ n, AEStronglyMeasurable (F n) (ν.restrict (Set.Ioc 0 T)) := fun n => by
    simp only [hF]
    exact (Finset.measurable_sum _
      (fun k _ => measurable_const.indicator measurableSet_Ioc)).aestronglyMeasurable
  have hconv := tendsto_integral_of_dominated_convergence (F := F) (f := h)
    (fun _ => C) hmeas (integrable_const C)
    (fun n => ae_restrict_of_forall_mem measurableSet_Ioc (hbound n))
    (ae_restrict_of_forall_mem measurableSet_Ioc hptwise)
  exact (tendsto_congr hstep_integ).mp hconv

/-- The uniform-partition mesh telescopes: `∑_{k<n} (t_{k+1} − t_k) = T` for `n > 0`. -/
private lemma unifPart_mesh_sum (T : ℝ≥0) {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) := by
  rw [Finset.sum_range_sub (fun k => (unifPart T n k : ℝ))]
  have h1 : unifPart T n n = T := by
    have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp only [unifPart, div_self hne, one_mul]
  have h0 : unifPart T n 0 = 0 := by simp [unifPart]
  rw [h1, h0]; simp

/-- A left-endpoint Riemann weight-sum of a bounded function is bounded by `C·T`:
`|∑_{k<n} g(B_{t_k} ω)·(t_{k+1} − t_k)| ≤ C·T`. Shared left-endpoint bound for
`tendsto_weighted_qv` (the `Rsum` term) and `memLp_pathIntegral`. -/
private lemma abs_riemann_weight_sum_le {g : ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hg_bdd : ∀ x, |g x| ≤ C) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    |∑ k ∈ Finset.range n,
        g (B (unifPart T n k) ω) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)| ≤ C * T := by
  have hΔnn : ∀ k, (0 : ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k := fun k =>
    sub_nonneg.mpr (by
      exact_mod_cast (show Monotone (unifPart T n) from fun a b hab => by
        simp only [unifPart]; gcongr) (Nat.le_succ k))
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
    exact mul_nonneg hC0 (NNReal.coe_nonneg T)
  · calc |∑ k ∈ Finset.range n,
            g (B (unifPart T n k) ω) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)|
        ≤ ∑ k ∈ Finset.range n,
            |g (B (unifPart T n k) ω) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, C * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) :=
          Finset.sum_le_sum fun k _ => by
            rw [abs_mul, abs_of_nonneg (hΔnn k)]
            exact mul_le_mul_of_nonneg_right (hg_bdd _) (hΔnn k)
      _ = C * ∑ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
          rw [Finset.mul_sum]
      _ = C * T := by rw [unifPart_mesh_sum T hn]

/-- **Weighted quadratic variation.** For bounded continuous `g`, the `g(B)`-weighted sum
of squared increments along the uniform partition of `[0,T]` converges in `L²(μ)` to
`∫₀ᵀ g(B_s) ds`. The continuous-weight generalization of `tendsto_qv`. -/
theorem tendsto_weighted_qv
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 => B s ω))
    {g : ℝ → ℝ} (hg_cont : Continuous g) {C : ℝ} (hg_bdd : ∀ x, |g x| ≤ C) (T : ℝ≥0) :
    Tendsto (fun n : ℕ =>
        ∫ ω, (∑ k ∈ Finset.range n,
                g (B (unifPart T n k) ω)
                  * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
              - ∫ s in Set.Ioc 0 T, g (B s ω) ∂ItoIntegralL2.timeMeasure) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  classical
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hg_bdd 0)
  have hg_meas : Measurable g := hg_cont.measurable
  set Ssum : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n,
      g (B (unifPart T n k) ω) * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 with hSsum
  set Rsum : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n,
      g (B (unifPart T n k) ω) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) with hRsum
  set Ipath : Ω → ℝ := fun ω => ∫ s in Set.Ioc 0 T, g (B s ω) ∂ItoIntegralL2.timeMeasure with hIpath
  show Tendsto (fun n => ∫ ω, (Ssum n ω - Ipath ω) ^ 2 ∂μ) atTop (𝓝 0)
  -- pathwise Riemann convergence `Rsum n ω → Ipath ω`, via `tendsto_riemann_continuous`
  have hpath : ∀ ω, Tendsto (fun n => Rsum n ω) atTop (𝓝 (Ipath ω)) := fun ω =>
    tendsto_riemann_continuous (h := fun s => g (B s ω)) (hg_cont.comp (hBcont ω))
      (fun s => hg_bdd _) T
  have hR_meas : ∀ n, Measurable (Rsum n) := fun n =>
    Finset.measurable_sum _ (fun k _ => (hg_meas.comp (hBmeas _)).mul_const _)
  have hI_meas : Measurable Ipath :=
    measurable_of_tendsto_metrizable hR_meas (tendsto_pi_nhds.mpr hpath)
  -- both `Rsum n` and `Ipath` are bounded by `C·T` (mesh sums telescope to `T`)
  have hR_bdd : ∀ n ω, |Rsum n ω| ≤ C * T := fun n ω => by
    simp only [hRsum]; exact abs_riemann_weight_sum_le hC0 hg_bdd T n ω
  have hI_bdd : ∀ ω, |Ipath ω| ≤ C * T := fun ω =>
    le_of_tendsto ((hpath ω).abs) (Eventually.of_forall fun n => hR_bdd n ω)
  -- the Riemann remainder `(Rsum − Ipath)²` is bounded by `(2CT)²` and measurable
  have hRI_nbd : ∀ n, ∀ᵐ ω ∂μ, ‖(Rsum n ω - Ipath ω) ^ 2‖ ≤ (2 * C * (T : ℝ)) ^ 2 := by
    intro n
    refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := abs_le.mp (hR_bdd n ω)
    have h2 := abs_le.mp (hI_bdd ω)
    exact sq_le_sq' (by nlinarith [h1.1, h2.2]) (by nlinarith [h1.2, h2.1])
  have hRI_meas : ∀ n, AEStronglyMeasurable (fun ω => (Rsum n ω - Ipath ω) ^ 2) μ := fun n =>
    (((hR_meas n).sub hI_meas).pow_const 2).aestronglyMeasurable
  -- **Term I**: the fluctuation `Ssum − Rsum → 0` in `L²` (= `tendsto_weighted_fluctuation`)
  have hTermI : Tendsto (fun n => ∫ ω, (Ssum n ω - Rsum n ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    refine (tendsto_congr fun n => ?_).mp
      (tendsto_weighted_fluctuation (μ := μ) hBmeas hg_meas hg_bdd T)
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show (∑ k ∈ Finset.range n, g (B (unifPart T n k) ω)
          * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) ^ 2 = (Ssum n ω - Rsum n ω) ^ 2
    have hbase : (∑ k ∈ Finset.range n, g (B (unifPart T n k) ω)
          * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) = Ssum n ω - Rsum n ω := by
      simp only [hSsum, hRsum]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hbase]
  -- **Term II**: the Riemann remainder `Rsum − Ipath → 0` in `L²`, by dominated convergence
  have hTermII : Tendsto (fun n => ∫ ω, (Rsum n ω - Ipath ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    have hlim : ∀ᵐ ω ∂μ,
        Tendsto (fun n => (Rsum n ω - Ipath ω) ^ 2) atTop (𝓝 ((fun _ => (0 : ℝ)) ω)) :=
      Eventually.of_forall fun ω => by simpa using ((hpath ω).sub_const (Ipath ω)).pow 2
    simpa using tendsto_integral_of_dominated_convergence
      (fun _ => (2 * C * (T : ℝ)) ^ 2) hRI_meas (integrable_const _) hRI_nbd hlim
  -- integrability of the two squared pieces (upper bounds for the squeeze)
  have hInt_I : ∀ n, Integrable (fun ω => (Ssum n ω - Rsum n ω) ^ 2) μ := by
    intro n
    have heq : (fun ω => Ssum n ω - Rsum n ω) = fun ω => ∑ k ∈ Finset.range n,
        g (B (unifPart T n k) ω) * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
          - ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) := by
      funext ω
      rw [hSsum, hRsum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hmemS : MemLp (fun ω => Ssum n ω - Rsum n ω) 2 μ := by
      rw [heq]
      refine memLp_finsetSum _ fun k _ => ?_
      have hZ : MemLp (fun ω => (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
          - ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) 2 μ :=
        memLp_increment_sq_centered_two (unifPart T n k) (unifPart T n (k + 1)) _
      have haesm : AEStronglyMeasurable (fun ω => g (B (unifPart T n k) ω)
          * ((B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) μ :=
        (hg_meas.comp (hBmeas _)).aestronglyMeasurable.mul hZ.aestronglyMeasurable
      refine MemLp.mono (hZ.const_mul C) haesm (Eventually.of_forall fun ω => ?_)
      simp only [Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right (hg_bdd _) (abs_nonneg _)
    have hsq : (fun ω => (Ssum n ω - Rsum n ω) ^ 2)
        = fun ω => (Ssum n ω - Rsum n ω) * (Ssum n ω - Rsum n ω) := by funext ω; ring
    rw [hsq]; exact hmemS.integrable_mul hmemS
  have hInt_II : ∀ n, Integrable (fun ω => (Rsum n ω - Ipath ω) ^ 2) μ := fun n =>
    Integrable.mono' (integrable_const ((2 * C * (T : ℝ)) ^ 2)) (hRI_meas n) (hRI_nbd n)
  -- **Assembly**: `(Ssum−Ipath)² ≤ 2(Ssum−Rsum)² + 2(Rsum−Ipath)²`, squeeze both terms to `0`
  have hupper : Tendsto (fun n => 2 * ∫ ω, (Ssum n ω - Rsum n ω) ^ 2 ∂μ
      + 2 * ∫ ω, (Rsum n ω - Ipath ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa using (hTermI.const_mul 2).add (hTermII.const_mul 2)
  refine squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) (fun n => ?_) hupper
  have hptwise : ∀ ω, (Ssum n ω - Ipath ω) ^ 2
      ≤ 2 * (Ssum n ω - Rsum n ω) ^ 2 + 2 * (Rsum n ω - Ipath ω) ^ 2 := fun ω => by
    nlinarith [sq_nonneg (Ssum n ω - 2 * Rsum n ω + Ipath ω)]
  calc ∫ ω, (Ssum n ω - Ipath ω) ^ 2 ∂μ
      ≤ ∫ ω, (2 * (Ssum n ω - Rsum n ω) ^ 2 + 2 * (Rsum n ω - Ipath ω) ^ 2) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
          (((hInt_I n).const_mul 2).add ((hInt_II n).const_mul 2))
          (Eventually.of_forall hptwise)
    _ = 2 * ∫ ω, (Ssum n ω - Rsum n ω) ^ 2 ∂μ + 2 * ∫ ω, (Rsum n ω - Ipath ω) ^ 2 ∂μ := by
        rw [integral_add ((hInt_I n).const_mul 2) ((hInt_II n).const_mul 2),
          integral_const_mul, integral_const_mul]

/-- The pathwise second-order term `ω ↦ ∫₀ᵀ g(B_s ω) ds` of a bounded continuous weight
lies in `L²(μ)`: it is measurable (a pointwise limit of the measurable Riemann sums via
`tendsto_riemann_continuous`) and bounded by `C·T`. Exported for the Itô-formula assembly,
where the second-order term must be an `L²` function. -/
theorem memLp_pathIntegral (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 => B s ω)) {g : ℝ → ℝ} (hg_cont : Continuous g)
    {C : ℝ} (hg_bdd : ∀ x, |g x| ≤ C) (T : ℝ≥0) :
    MemLp (fun ω => ∫ s in Set.Ioc 0 T, g (B s ω) ∂ItoIntegralL2.timeMeasure) 2 μ := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hg_bdd 0)
  have hg_meas : Measurable g := hg_cont.measurable
  have hpath : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n,
      g (B (unifPart T n k) ω) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) atTop
      (𝓝 (∫ s in Set.Ioc 0 T, g (B s ω) ∂ItoIntegralL2.timeMeasure)) := fun ω =>
    tendsto_riemann_continuous (h := fun s => g (B s ω)) (hg_cont.comp (hBcont ω))
      (fun s => hg_bdd _) T
  have hR_meas : ∀ n, Measurable (fun ω => ∑ k ∈ Finset.range n,
      g (B (unifPart T n k) ω) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) := fun n =>
    Finset.measurable_sum _ (fun k _ => (hg_meas.comp (hBmeas _)).mul_const _)
  have hI_meas : Measurable (fun ω => ∫ s in Set.Ioc 0 T, g (B s ω) ∂ItoIntegralL2.timeMeasure) :=
    measurable_of_tendsto_metrizable hR_meas (tendsto_pi_nhds.mpr hpath)
  have hR_bdd : ∀ n ω, |∑ k ∈ Finset.range n,
      g (B (unifPart T n k) ω) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)| ≤ C * T :=
    fun n ω => abs_riemann_weight_sum_le hC0 hg_bdd T n ω
  have hI_bdd : ∀ ω, |∫ s in Set.Ioc 0 T, g (B s ω) ∂ItoIntegralL2.timeMeasure| ≤ C * T :=
    fun ω => le_of_tendsto ((hpath ω).abs) (Eventually.of_forall fun n => hR_bdd n ω)
  exact MemLp.of_bound hI_meas.aestronglyMeasurable (C * T)
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hI_bdd ω)

end MathFin
