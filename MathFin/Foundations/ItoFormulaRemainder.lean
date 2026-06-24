/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.GaussianMoments
public import MathFin.Foundations.QuadraticVariationL2
public import MathFin.Foundations.DiscreteIto

/-! # The Itô–Taylor remainder vanishes in `L²`

The third (remainder) term of the discrete Itô formula `discrete_ito_formula`, summed
along the uniform partition of `[0,T]`, converges to `0` in `L²(μ)` for `f ∈ C³` with
bounded `f‴`. This is the term the continuous-time Itô formula discards.

Each per-step remainder `Rₖ` is `O(|ΔBₖ|³)` (order-2 Taylor bound,
`abs_discreteTaylorRemainder_le`), so `E[Rₖ²] = O(E[(ΔBₖ)⁶]) = O((Δtₖ)³)` (the Gaussian
sixth moment `integral_pow6_gaussianReal`). Cauchy–Schwarz on the sum gives
`E[(∑ₖ Rₖ)²] ≤ n·∑ₖ E[Rₖ²] = O(n·n·(T/n)³) = O(n⁻¹) → 0`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter QuadraticVariationL2
open scoped NNReal Topology

/-- **Cubic Taylor bound on the discrete remainder.** For `f ∈ C³` with `|f‴| ≤ Cf3`,
the order-2 Taylor remainder `R = f y − f x − f′x·(y−x) − ½f″x·(y−x)²` is `O(|y−x|³)`:
`|R| ≤ Cf3·|y−x|³`. Proved by three applications of the convex mean-value bound on the
segment `[[x,y]]` — bounding `f″−f″x`, then the primitive defect `f′−f′x−f″x·(·−x)`, then
the full remainder — each level gaining one power of `|y−x|`. (The sharp constant `Cf3/6`
is not needed; any cubic bound drives the `L²` limit.) -/
theorem abs_discreteTaylorRemainder_le {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x) {Cf3 : ℝ} (hf3 : ∀ x, |f''' x| ≤ Cf3)
    (x y : ℝ) : |discreteTaylorRemainder f f' f'' x y| ≤ Cf3 * |y - x| ^ 3 := by
  have hCf3 : 0 ≤ Cf3 := le_trans (abs_nonneg _) (hf3 0)
  have hmem : ∀ t ∈ Set.uIcc x y, |t - x| ≤ |y - x| := by
    intro t ht
    rcases le_total x y with hxy | hyx
    · rw [Set.uIcc_of_le hxy] at ht
      rw [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - x),
        abs_of_nonneg (by linarith [hxy] : (0 : ℝ) ≤ y - x)]
      linarith [ht.2]
    · rw [Set.uIcc_of_ge hyx] at ht
      rw [abs_of_nonpos (by linarith [ht.2] : t - x ≤ 0),
        abs_of_nonpos (by linarith [hyx] : y - x ≤ 0)]
      linarith [ht.1]
  -- Level 2: `|f″ t − f″ x| ≤ Cf3·|y−x|`
  have hL2 : ∀ t ∈ Set.uIcc x y, |f'' t - f'' x| ≤ Cf3 * |y - x| := by
    intro t ht
    have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (hf'' u).hasDerivWithinAt) (fun u _ => by rw [Real.norm_eq_abs]; exact hf3 u)
      Set.left_mem_uIcc ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hmem t ht) hCf3)
  -- Level 1: `|f′ t − f′ x − f″ x·(t−x)| ≤ Cf3·|y−x|²`
  have hd1 : ∀ u, HasDerivAt (fun s => f' s - f' x - f'' x * (s - x)) (f'' u - f'' x) u :=
    fun u => by
      have h := ((hf' u).sub_const (f' x)).sub
        (((hasDerivAt_id u).sub_const x).const_mul (f'' x))
      simp only [id_eq] at h
      convert h using 1 <;> first | rfl | ring
  have hL1 : ∀ t ∈ Set.uIcc x y, |f' t - f' x - f'' x * (t - x)| ≤ Cf3 * |y - x| ^ 2 := by
    intro t ht
    have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (hd1 u).hasDerivWithinAt)
      (fun u hu => by rw [Real.norm_eq_abs]; exact hL2 u hu)
      Set.left_mem_uIcc ht
    simp only [Real.norm_eq_abs, sub_self, mul_zero, sub_zero] at h
    calc |f' t - f' x - f'' x * (t - x)| ≤ Cf3 * |y - x| * |t - x| := h
      _ ≤ Cf3 * |y - x| * |y - x| :=
          mul_le_mul_of_nonneg_left (hmem t ht) (mul_nonneg hCf3 (abs_nonneg _))
      _ = Cf3 * |y - x| ^ 2 := by ring
  -- Level 0: the remainder itself
  have hd0 : ∀ u, HasDerivAt (fun s => f s - f x - f' x * (s - x) - 1 / 2 * f'' x * (s - x) ^ 2)
      (f' u - f' x - f'' x * (u - x)) u := fun u => by
    have h := (((hf u).sub_const (f x)).sub
        (((hasDerivAt_id u).sub_const x).const_mul (f' x))).sub
        ((((hasDerivAt_id u).sub_const x).pow 2).const_mul (1 / 2 * f'' x))
    simp only [id_eq] at h
    convert h using 1 <;> first | rfl | ring
  have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hd0 u).hasDerivWithinAt)
    (fun u hu => by rw [Real.norm_eq_abs]; exact hL1 u hu)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.norm_eq_abs] at h
  rw [show f y - f x - f' x * (y - x) - 1 / 2 * f'' x * (y - x) ^ 2
        - (f x - f x - f' x * (x - x) - 1 / 2 * f'' x * (x - x) ^ 2)
      = discreteTaylorRemainder f f' f'' x y from by unfold discreteTaylorRemainder; ring] at h
  exact h.trans_eq (by ring)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  (hB : IsPreBrownianReal B μ)

include hB

/-- **Sixth moment of a Brownian increment**: `E[(B_{t₁} − B_{t₀})⁶] = 15(t₁ − t₀)³`
for `t₀ ≤ t₁` (law-transfer of the Gaussian identity `integral_pow6_gaussianReal`). -/
theorem integral_increment_pow6 {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) :
    ∫ ω, (B t₁ ω - B t₀ ω) ^ 6 ∂μ = 15 * ((t₁ : ℝ) - t₀) ^ 3 := by
  have hmax : ((max (t₁ - t₀) (t₀ - t₁) : ℝ≥0) : ℝ) = (t₁ : ℝ) - t₀ := by
    rw [max_eq_left (by rw [tsub_eq_zero_of_le ht]; exact zero_le), NNReal.coe_sub ht]
  have hbridge : (max (t₁ - t₀) (t₀ - t₁) : ℝ≥0) = nndist (t₁ : ℝ) (t₀ : ℝ) := by
    apply NNReal.coe_injective
    rw [coe_nndist, Real.dist_eq, hmax,
      abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht))]
  have hlaw : HasLaw (B t₁ - B t₀) (gaussianReal 0 (max (t₁ - t₀) (t₀ - t₁))) μ := by
    rw [hbridge]; exact hB.hasLaw_sub t₁ t₀
  have hcomp := hlaw.integral_comp (f := fun x : ℝ => x ^ 6)
    (measurable_id.pow_const 6).aestronglyMeasurable
  simp only [Function.comp_def, Pi.sub_apply] at hcomp
  rw [hcomp, integral_pow6_gaussianReal, hmax]

/-- The sixth power of a Brownian increment is integrable (all Gaussian moments are
finite); the companion to `integral_increment_pow6`. -/
theorem integrable_increment_pow6 (t₀ t₁ : ℝ≥0) :
    Integrable (fun ω => (B t₁ ω - B t₀ ω) ^ 6) μ := by
  have hg : Integrable (fun x : ℝ => x ^ 6) (gaussianReal 0 (nndist (t₁ : ℝ) (t₀ : ℝ))) := by
    have h := (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := nndist (t₁ : ℝ) (t₀ : ℝ)) 6).integrable_norm_pow
      (p := 6) (by norm_num)
    simp only [id_eq, Real.norm_eq_abs] at h
    have hfe : (fun x : ℝ => |x| ^ 6) = fun x : ℝ => x ^ 6 :=
      funext fun x => by rw [pow_abs, abs_of_nonneg (by positivity)]
    rwa [hfe] at h
  have hmap : Integrable (fun x : ℝ => x ^ 6) (Measure.map (B t₁ - B t₀) μ) := by
    rw [(hB.hasLaw_sub t₁ t₀).map_eq]; exact hg
  exact (integrable_map_measure hmap.aestronglyMeasurable (hB.hasLaw_sub t₁ t₀).aemeasurable).mp hmap

/-- **The Itô–Taylor remainder vanishes in `L²`.** For `f ∈ C³` with `|f‴| ≤ Cf3`,
`∑ₖ Rₖ → 0` in `L²(μ)` along the uniform partition of `[0,T]`. -/
theorem tendsto_ito_remainder
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x) {Cf3 : ℝ} (hf3 : ∀ x, |f''' x| ≤ Cf3) :
    Tendsto (fun n : ℕ => ∫ ω, (∑ k ∈ Finset.range n,
        discreteTaylorRemainder f f' f''
          (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2 ∂μ) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hCf3 : 0 ≤ Cf3 := le_trans (abs_nonneg _) (hf3 0)
  have hfm : Measurable f := (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt).measurable
  have hf'm : Measurable f' := (continuous_iff_continuousAt.mpr fun x => (hf' x).continuousAt).measurable
  have hf''m : Measurable f'' := (continuous_iff_continuousAt.mpr fun x => (hf'' x).continuousAt).measurable
  have hmono : ∀ n, Monotone (unifPart T n) := fun n a b hab => by simp only [unifPart]; gcongr
  -- per-step squared remainder: measurable, and `≤ Cf3²·(ΔBₖ)⁶`
  have hRk_meas : ∀ n k, Measurable (fun ω => discreteTaylorRemainder f f' f''
      (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) := by
    intro n k
    unfold discreteTaylorRemainder
    exact (((hfm.comp (hBmeas _)).sub (hfm.comp (hBmeas _))).sub
      ((hf'm.comp (hBmeas _)).mul ((hBmeas _).sub (hBmeas _)))).sub
      (((hf''m.comp (hBmeas _)).mul (((hBmeas _).sub (hBmeas _)).pow_const 2)).const_mul (1 / 2))
  have hRsq_le : ∀ n k ω, (discreteTaylorRemainder f f' f''
        (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2
      ≤ Cf3 ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 6 := by
    intro n k ω
    have hb := abs_discreteTaylorRemainder_le hf hf' hf'' hf3
      (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)
    have he : |B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω| ^ 6
        = (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 6 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    calc (discreteTaylorRemainder f f' f'' (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2
        = |discreteTaylorRemainder f f' f'' (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)|
            * |discreteTaylorRemainder f f' f'' (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)| := by
          rw [sq]; exact (abs_mul_abs_self _).symm
      _ ≤ (Cf3 * |B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω| ^ 3)
            * (Cf3 * |B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω| ^ 3) :=
          mul_self_le_mul_self (abs_nonneg _) hb
      _ = Cf3 ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 6 := by rw [← he]; ring
  have hRsq_int : ∀ n k, Integrable (fun ω => (discreteTaylorRemainder f f' f''
      (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2) μ := by
    intro n k
    refine Integrable.mono'
      ((integrable_increment_pow6 hB (unifPart T n k) (unifPart T n (k + 1))).const_mul (Cf3 ^ 2))
      ((hRk_meas n k).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hRsq_le n k ω
  -- squeeze: `∫ (∑ₖ Rₖ)² ≤ 15·Cf3²·T³/n → 0`
  refine squeeze_zero' (g := fun n : ℕ => 15 * Cf3 ^ 2 * (T : ℝ) ^ 3 / n)
    (Eventually.of_forall fun n => integral_nonneg fun ω => sq_nonneg _) ?_
    (by simpa using tendsto_const_div_atTop_nhds_zero_nat (15 * Cf3 ^ 2 * (T : ℝ) ^ 3))
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hΔ : ∀ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) / n :=
    fun k _ => by simp only [unifPart]; push_cast; field_simp; ring
  calc ∫ ω, (∑ k ∈ Finset.range n, discreteTaylorRemainder f f' f''
            (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2 ∂μ
      ≤ ∫ ω, (n : ℝ) * ∑ k ∈ Finset.range n, (discreteTaylorRemainder f f' f''
            (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2 ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
          ((integrable_finsetSum _ fun k _ => hRsq_int n k).const_mul _)
          (Eventually.of_forall fun ω => ?_)
        have := sq_sum_le_card_mul_sum_sq (s := Finset.range n)
          (f := fun k => discreteTaylorRemainder f f' f''
            (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω))
        rwa [Finset.card_range] at this
    _ = (n : ℝ) * ∑ k ∈ Finset.range n, ∫ ω, (discreteTaylorRemainder f f' f''
            (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2 ∂μ := by
        rw [integral_const_mul, integral_finsetSum _ fun k _ => hRsq_int n k]
    _ ≤ (n : ℝ) * ∑ k ∈ Finset.range n, 15 * Cf3 ^ 2 * ((T : ℝ) / n) ^ 3 := by
        gcongr with k hk
        calc ∫ ω, (discreteTaylorRemainder f f' f''
              (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2 ∂μ
            ≤ ∫ ω, Cf3 ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 6 ∂μ :=
              integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
                ((integrable_increment_pow6 hB _ _).const_mul _)
                (Eventually.of_forall fun ω => hRsq_le n k ω)
          _ = Cf3 ^ 2 * ∫ ω, (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 6 ∂μ :=
              integral_const_mul _ _
          _ = Cf3 ^ 2 * (15 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 3) := by
              rw [integral_increment_pow6 hB (hmono n (Nat.le_succ k))]
          _ = 15 * Cf3 ^ 2 * ((T : ℝ) / n) ^ 3 := by rw [hΔ k hk]; ring
    _ = 15 * Cf3 ^ 2 * (T : ℝ) ^ 3 / n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

end MathFin
