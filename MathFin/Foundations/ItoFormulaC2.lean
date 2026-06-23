/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.WeightedQuadraticVariation
public import MathFin.Foundations.ItoFormulaRemainder

/-! # Bounded-derivative continuous-time Itô formula (L², named-limit form)

Assembles the discrete Itô formula (`discrete_ito_formula`) with the two `L²` limits —
the weighted quadratic variation (`tendsto_weighted_qv`, A1) and the vanishing Itô–Taylor
remainder (`tendsto_ito_remainder`, A2) — into the continuous-time Itô formula on `[0,T]`.

For `f ∈ C³` with bounded `f″, f‴`, the uniform-partition Riemann–Itô sums
`∑ f′(B_{tₖ})·ΔBₖ` converge in `L²(μ)` to `f(B_T) − f(B_0) − ½∫₀ᵀ f″(B_s) ds`. This is
Itô's lemma in named-limit form: the stochastic integral `∫₀ᵀ f′(B) dB` (the `L²`-limit)
plus the second-order correction recovers `f(B_T) − f(B_0)`. The discrete identity makes
`Isumₙ − I = −½(QVₙ − ∫f″ds) − Remₙ`, in which the unbounded boundary term
`f(B_T) − f(B_0)` cancels, so the `L²` estimate only ever sees the two vanishing terms.

The integral term is identified with the genuine `itoIntegralCLM_T` in
`ItoIntegralRiemannBridge` (A3/A4).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter QuadraticVariationL2
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  [hB : IsPreBrownianReal B μ]

/-- **Bounded-derivative Itô formula in `L²` (named-limit form).** For `f ∈ C³` with
`|f″| ≤ C₂` and `|f‴| ≤ C₃`, the uniform-partition Riemann–Itô sums `∑ f′(B_{tₖ})·ΔBₖ`
converge in `L²(μ)` to `f(B_T) − f(B_0) − ½∫₀ᵀ f″(B_s) ds`. -/
theorem ito_formula_L2
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 => B s ω)) (T : ℝ≥0)
    {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C2 : ℝ} (hf2 : ∀ x, |f'' x| ≤ C2) {C3 : ℝ} (hf3 : ∀ x, |f''' x| ≤ C3) :
    Tendsto (fun n : ℕ =>
        ∫ ω, (∑ k ∈ Finset.range n,
                f' (B (unifPart T n k) ω) * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)
              - (f (B T ω) - f (B 0 ω)
                  - (1 / 2) * ∫ s in Set.Ioc 0 T, f'' (B s ω) ∂ItoIntegralL2.timeMeasure)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  classical
  have hf''_cont : Continuous f'' := continuous_iff_continuousAt.mpr fun x => (hf'' x).continuousAt
  have hf'm : Measurable f' :=
    (continuous_iff_continuousAt.mpr fun x => (hf' x).continuousAt).measurable
  have hf''m : Measurable f'' := hf''_cont.measurable
  have hfm : Measurable f := (continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt).measurable
  have hA1 := tendsto_weighted_qv (μ := μ) hBmeas hBcont (g := f'') hf''_cont hf2 T
  have hA2 := tendsto_ito_remainder (μ := μ) hBmeas T hf hf' hf'' hf3
  set Isum : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n,
      f' (B (unifPart T n k) ω) * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) with hIsum
  set QV : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n,
      f'' (B (unifPart T n k) ω) * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 with hQVdef
  set Rem : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n,
      discreteTaylorRemainder f f' f'' (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω) with hRemdef
  set I2 : Ω → ℝ := fun ω => ∫ s in Set.Ioc 0 T, f'' (B s ω) ∂ItoIntegralL2.timeMeasure with hI2def
  show Tendsto (fun n => ∫ ω, (Isum n ω - (f (B T ω) - f (B 0 ω) - (1 / 2) * I2 ω)) ^ 2 ∂μ)
    atTop (𝓝 0)
  -- `L²` membership of the second-order integral and the two discrete sums
  have hI2_memLp : MemLp I2 2 μ := memLp_pathIntegral hBmeas hBcont hf''_cont hf2 T
  have hQV_memLp : ∀ n, MemLp (QV n) 2 μ := by
    intro n
    rw [hQVdef]
    refine memLp_finsetSum _ fun k _ => ?_
    have hZ : MemLp (fun ω => (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) 2 μ := by
      have h := (memLp_increment_sq_centered_two (B := B) (unifPart T n k) (unifPart T n (k + 1))
          ((unifPart T n (k + 1) : ℝ) - unifPart T n k)).add
          (memLp_const (μ := μ) ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      have heq : ((fun ω => (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
          + fun _ : Ω => ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
          = fun ω => (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 := by
        funext ω; simp only [Pi.add_apply]; ring
      rwa [heq] at h
    have haesm : AEStronglyMeasurable (fun ω => f'' (B (unifPart T n k) ω)
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) μ :=
      (hf''m.comp (hBmeas _)).aestronglyMeasurable.mul hZ.aestronglyMeasurable
    refine MemLp.mono (hZ.const_mul C2) haesm (Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (le_trans (abs_nonneg _) (hf2 0))]
    exact mul_le_mul_of_nonneg_right (hf2 _) (abs_nonneg _)
  have hRem_memLp : ∀ n, MemLp (Rem n) 2 μ := by
    intro n
    rw [hRemdef]
    refine memLp_finsetSum _ fun k _ => ?_
    have hmeas : Measurable (fun ω => discreteTaylorRemainder f f' f''
        (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) := by
      unfold discreteTaylorRemainder
      exact (((hfm.comp (hBmeas _)).sub (hfm.comp (hBmeas _))).sub
        ((hf'm.comp (hBmeas _)).mul ((hBmeas _).sub (hBmeas _)))).sub
        (((hf''m.comp (hBmeas _)).mul (((hBmeas _).sub (hBmeas _)).pow_const 2)).const_mul (1 / 2))
    rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
    refine Integrable.mono'
      ((integrable_increment_pow6 (B := B) (unifPart T n k) (unifPart T n (k + 1))).const_mul (C3 ^ 2))
      (hmeas.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := abs_discreteTaylorRemainder_le hf hf' hf'' hf3
      (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)
    have he : |B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω| ^ 6
        = (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 6 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    calc discreteTaylorRemainder f f' f'' (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω) ^ 2
        = |discreteTaylorRemainder f f' f'' (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)|
            * |discreteTaylorRemainder f f' f'' (B (unifPart T n k) ω)
                (B (unifPart T n (k + 1)) ω)| := by rw [sq]; exact (abs_mul_abs_self _).symm
      _ ≤ (C3 * |B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω| ^ 3)
            * (C3 * |B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω| ^ 3) :=
          mul_self_le_mul_self (abs_nonneg _) hb
      _ = C3 ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 6 := by rw [← he]; ring
  have hInt_a : ∀ n, Integrable (fun ω => (QV n ω - I2 ω) ^ 2) μ :=
    fun n => ((hQV_memLp n).sub hI2_memLp).integrable_sq
  have hInt_b : ∀ n, Integrable (fun ω => Rem n ω ^ 2) μ :=
    fun n => (hRem_memLp n).integrable_sq
  -- the upper bound `½∫(QVₙ−∫f″ds)² + 2∫Remₙ² → 0` (A1 + A2)
  have hupper : Tendsto (fun n => (1 / 2) * ∫ ω, (QV n ω - I2 ω) ^ 2 ∂μ
      + 2 * ∫ ω, Rem n ω ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := (hA1.const_mul (1 / 2)).add (hA2.const_mul 2)
    simp only [mul_zero, add_zero] at h
    exact h
  refine squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun ω => sq_nonneg _) ?_ hupper
  filter_upwards [eventually_gt_atTop 0] with n hn
  -- discrete Itô formula: `Isumₙ − I = −½(QVₙ − ∫f″ds) − Remₙ` (`n > 0`)
  have hpt : ∀ ω, Isum n ω - (f (B T ω) - f (B 0 ω) - (1 / 2) * I2 ω)
      = -(1 / 2) * (QV n ω - I2 ω) - Rem n ω := by
    intro ω
    have hd := discrete_ito_formula n (fun k => B (unifPart T n k) ω) f f' f''
    have hnn : unifPart T n n = T := by
      have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [unifPart, div_self hne, one_mul]
    have hz : unifPart T n 0 = 0 := by simp [unifPart]
    rw [hnn, hz] at hd
    simp only [hIsum, hQVdef, hRemdef]
    linarith [hd]
  calc ∫ ω, (Isum n ω - (f (B T ω) - f (B 0 ω) - (1 / 2) * I2 ω)) ^ 2 ∂μ
      = ∫ ω, (-(1 / 2) * (QV n ω - I2 ω) - Rem n ω) ^ 2 ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        show (Isum n ω - (f (B T ω) - f (B 0 ω) - 1 / 2 * I2 ω)) ^ 2
          = (-(1 / 2) * (QV n ω - I2 ω) - Rem n ω) ^ 2
        rw [hpt ω]
    _ ≤ ∫ ω, ((1 / 2) * (QV n ω - I2 ω) ^ 2 + 2 * Rem n ω ^ 2) ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
          (((hInt_a n).const_mul (1 / 2)).add ((hInt_b n).const_mul 2))
          (Eventually.of_forall fun ω => ?_)
        nlinarith [sq_nonneg ((1 / 2) * (QV n ω - I2 ω) - Rem n ω)]
    _ = (1 / 2) * ∫ ω, (QV n ω - I2 ω) ^ 2 ∂μ + 2 * ∫ ω, Rem n ω ^ 2 ∂μ := by
        rw [integral_add ((hInt_a n).const_mul (1 / 2)) ((hInt_b n).const_mul 2),
          integral_const_mul, integral_const_mul]

end MathFin
