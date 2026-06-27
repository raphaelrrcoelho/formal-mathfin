/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralBrownian

/-! # Exponential moments of Brownian marginals

A pre-Brownian motion's marginal `B_s` is `N(0, s)`, so it has *every* exponential
moment. Concretely, transferring the standard Gaussian moment-generating function
(`integrable_exp_mul_gaussianReal`, `mgf_id_gaussianReal`) along the law
`hB.hasLaw_eval s : HasLaw (B s) (gaussianReal 0 s) μ`,

  `∫ exp(c · B_s) ∂μ = exp(c² s / 2)`,

and the absolute-value variant `exp(c · |B_s|) ∈ L²(μ)` with the uniform bound
`∫ exp(c · |B_s|) ∂μ ≤ 2 · exp(c² s / 2)` (via `exp(c|x|) ≤ exp(cx) + exp(−cx)`).

These are the integrability base stones the exponential-growth Itô formula
(`ItoFormulaLocalized`) needs to dominate its cutoff approximants: the marginal
exponential moment, together with Tonelli, controls the `L²` norm of path
integrals of exponential-growth integrands. `GaussianMoments` holds the
*polynomial* moments; this file holds the exponential ones.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- Pointwise: `exp(c|x|) ≤ exp(cx) + exp(−cx)` (the absolute value picks the larger
exponent; the other summand is nonnegative). -/
private lemma exp_abs_le_add (c x : ℝ) :
    Real.exp (c * |x|) ≤ Real.exp (c * x) + Real.exp (-c * x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hx, mul_neg, ← neg_mul]; exact le_add_of_nonneg_left (Real.exp_nonneg _)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- `exp(c · B_s)` is integrable: transfer `integrable_exp_mul_gaussianReal` along the
marginal law `B_s ~ N(0, s)`. -/
lemma integrable_exp_mul_eval (s : ℝ≥0) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * B s ω)) μ := by
  rw [show (fun ω => Real.exp (c * B s ω)) = (fun x => Real.exp (c * x)) ∘ B s from rfl]
  refine Integrable.comp_aemeasurable ?_ (hB.hasLaw_eval s).aemeasurable
  rw [(hB.hasLaw_eval s).map_eq]
  exact integrable_exp_mul_gaussianReal c

/-- The Brownian marginal MGF: `∫ exp(c · B_s) ∂μ = exp(c² s / 2)`. -/
lemma integral_exp_mul_eval (s : ℝ≥0) (c : ℝ) :
    ∫ ω, Real.exp (c * B s ω) ∂μ = Real.exp (c ^ 2 * (s : ℝ) / 2) := by
  have hg : AEStronglyMeasurable (fun x : ℝ => Real.exp (c * x)) (Measure.map (B s) μ) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hint : ∫ ω, Real.exp (c * B s ω) ∂μ
      = ∫ x, Real.exp (c * x) ∂(Measure.map (B s) μ) :=
    (integral_map (hB.hasLaw_eval s).aemeasurable hg).symm
  rw [hint, (hB.hasLaw_eval s).map_eq]
  have h := congr_fun (mgf_id_gaussianReal (μ := (0 : ℝ)) (v := s)) c
  show mgf id (gaussianReal 0 s) c = _
  rw [h]; ring_nf

/-- `exp(c · B_s) ∈ L²(μ)`: its square is `exp(2c · B_s)`, integrable by the marginal MGF. -/
lemma memLp_exp_mul_eval (s : ℝ≥0) (c : ℝ) :
    MemLp (fun ω => Real.exp (c * B s ω)) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (c * B s ω)) μ :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp_aemeasurable
      (hB.hasLaw_eval s).aemeasurable).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hsq : (fun ω => Real.exp (c * B s ω) ^ 2) = (fun ω => Real.exp (2 * c * B s ω)) := by
    funext ω; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hsq]
  exact integrable_exp_mul_eval hB s (2 * c)

/-- `exp(c · |B_s|) ∈ L²(μ)`: dominated by `exp(c · B_s) + exp(−c · B_s) ∈ L²`. -/
lemma memLp_exp_abs_eval (s : ℝ≥0) (c : ℝ) :
    MemLp (fun ω => Real.exp (c * |B s ω|)) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (c * |B s ω|)) μ :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).measurable.comp_aemeasurable
      (hB.hasLaw_eval s).aemeasurable).aestronglyMeasurable
  refine ((memLp_exp_mul_eval hB s c).add (memLp_exp_mul_eval hB s (-c))).mono hmeas
    (ae_of_all _ fun ω => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.exp (c * B s ω) + Real.exp (-c * B s ω))]
  exact exp_abs_le_add c (B s ω)

/-- Uniform exponential-moment bound: `∫ exp(c · |B_s|) ∂μ ≤ 2 · exp(c² s / 2)`. -/
lemma integral_exp_abs_eval_le (s : ℝ≥0) (c : ℝ) :
    ∫ ω, Real.exp (c * |B s ω|) ∂μ ≤ 2 * Real.exp (c ^ 2 * (s : ℝ) / 2) := by
  have hbnd : ∀ ω, Real.exp (c * |B s ω|)
      ≤ Real.exp (c * B s ω) + Real.exp (-c * B s ω) := fun ω => exp_abs_le_add c (B s ω)
  have hsum_int : Integrable (fun ω => Real.exp (c * B s ω) + Real.exp (-c * B s ω)) μ :=
    (integrable_exp_mul_eval hB s c).add (integrable_exp_mul_eval hB s (-c))
  have hlhs_int : Integrable (fun ω => Real.exp (c * |B s ω|)) μ :=
    hsum_int.mono'
      ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).measurable.comp_aemeasurable
        (hB.hasLaw_eval s).aemeasurable).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]; exact hbnd ω)
  calc ∫ ω, Real.exp (c * |B s ω|) ∂μ
      ≤ ∫ ω, (Real.exp (c * B s ω) + Real.exp (-c * B s ω)) ∂μ :=
        integral_mono hlhs_int hsum_int hbnd
    _ = Real.exp (c ^ 2 * (s : ℝ) / 2) + Real.exp ((-c) ^ 2 * (s : ℝ) / 2) := by
        rw [integral_add (integrable_exp_mul_eval hB s c) (integrable_exp_mul_eval hB s (-c)),
          integral_exp_mul_eval hB s c, integral_exp_mul_eval hB s (-c)]
    _ = 2 * Real.exp (c ^ 2 * (s : ℝ) / 2) := by rw [neg_sq]; ring

end MathFin
