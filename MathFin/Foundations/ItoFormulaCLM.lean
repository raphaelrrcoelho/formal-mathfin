/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin.Foundations.ItoFormulaC2
import MathFin.Foundations.ItoIntegralRiemannBridge

/-! # CLM-identified continuous-time Itô formula (L²)

Identifies the named-limit Itô formula (`ito_formula_L2`, A-core) with the genuine
continuous Itô integral `itoIntegralCLM_T` (A3). For `f ∈ C³` with bounded `f′, f″, f‴`,

  `f(B_T) − f(B_0) =ᵐ[μ] itoIntegralCLM_T gf' + ½∫₀ᵀ f″(B_s) ds`,

where `gf'` is the Itô-`L²` realization of `s ↦ f′(B_s)`. The named limit `I` of the
Riemann–Itô sums (A-core) and the CLM integral (A3) are *both* the `L²`-limit of the same
sums `∑ f′(B_{tₖ})·ΔBₖ`, so by uniqueness of `L²` limits they coincide a.e.

`I ∈ L²` (needed to take the `toLp` class) because `f` is Lipschitz (`f′` bounded), so
`f(B_T)` is dominated by `|f 0| + C₁·|B_T|`, an `L²` function.
-/

namespace MathFin

open MeasureTheory ProbabilityTheory Filter QuadraticVariationL2 ItoIntegralCLM
  ItoIntegralBrownian ItoIntegralRiemannBridge
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} [hB : IsPreBrownian B μ]

/-- **CLM-identified bounded-derivative Itô formula in `L²`.** For `f ∈ C³` with `|f′| ≤ C₁`,
`|f″| ≤ C₂`, `|f‴| ≤ C₃`, there is an Itô-`L²` integrand `gf'` (the realization of
`s ↦ f′(B_s)`) with `f(B_T) − f(B_0) =ᵐ[μ] itoIntegralCLM_T gf' + ½∫₀ᵀ f″(B_s) ds`. -/
theorem ito_formula_L2_bddDeriv
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 => B s ω)) (T : ℝ≥0)
    {f f' f'' f''' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C1 : ℝ} (hf1 : ∀ x, |f' x| ≤ C1) {C2 : ℝ} (hf2 : ∀ x, |f'' x| ≤ C2)
    {C3 : ℝ} (hf3 : ∀ x, |f''' x| ≤ C3) :
    ∃ gf' : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω => f (B T ω) - f (B 0 ω)) =ᵐ[μ]
        (fun ω => (itoIntegralCLM_T (μ := μ) T hBmeas gf') ω
          + (1 / 2) * ∫ s in Set.Ioc 0 T, f'' (B s ω) ∂ItoIntegralL2.timeMeasure) := by
  have hf'_cont : Continuous f' := continuous_iff_continuousAt.mpr fun x => (hf' x).continuousAt
  have hf''_cont : Continuous f'' := continuous_iff_continuousAt.mpr fun x => (hf'' x).continuousAt
  have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  obtain ⟨gf', hgf'⟩ := itoIntegralCLM_T_of_bdd_cont (μ := μ) hBmeas hBcont hf'_cont hf1 T
  refine ⟨gf', ?_⟩
  set I : Ω → ℝ := fun ω => f (B T ω) - f (B 0 ω)
    - (1 / 2) * ∫ s in Set.Ioc 0 T, f'' (B s ω) ∂ItoIntegralL2.timeMeasure with hI
  -- `f` is `C₁`-Lipschitz, so `f(B_t)` is dominated by `|f 0| + C₁·|B_t| ∈ L²`
  have hlip : ∀ x : ℝ, |f x| ≤ |f 0| + C1 * |x| := fun x => by
    have h := (convex_uIcc (0 : ℝ) x).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (hf u).hasDerivWithinAt) (fun u _ => by rw [Real.norm_eq_abs]; exact hf1 u)
      Set.left_mem_uIcc Set.right_mem_uIcc
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at h
    have h2 : |f x| - |f 0| ≤ |f x - f 0| := abs_sub_abs_le_abs_sub _ _
    linarith [h, h2]
  have hfB : ∀ t : ℝ≥0, MemLp (fun ω => f (B t ω)) 2 μ := fun t => by
    refine MemLp.mono ((memLp_const (μ := μ) |f 0|).add
        ((memLp_eval (B := B) t).norm.const_mul C1))
      ((hf_cont.measurable.comp (hBmeas t)).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    calc ‖f (B t ω)‖ = |f (B t ω)| := Real.norm_eq_abs _
      _ ≤ |f 0| + C1 * ‖B t ω‖ := by rw [Real.norm_eq_abs]; exact hlip (B t ω)
      _ ≤ ‖|f 0| + C1 * ‖B t ω‖‖ := le_abs_self _
  have hI_memLp : MemLp I 2 μ :=
    ((hfB T).sub (hfB 0)).sub
      ((memLp_pathIntegral hBmeas hBcont hf''_cont hf2 T).const_mul (1 / 2))
  -- A-core: the Riemann sums converge in `L²` to `I`; lift to `Lp`
  have hcore := ito_formula_L2 (μ := μ) hBmeas hBcont T hf hf' hf'' hf2 hf3
  have hcore_Lp : Tendsto (fun n => (memLp_riemannφ (μ := μ) hBmeas hf'_cont.measurable hf1 T n).toLp
        (riemannφ hBmeas f' T n)) atTop (𝓝 (hI_memLp.toLp I)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (tendsto_norm_toLp_sub' (fun n => memLp_riemannφ (μ := μ) hBmeas hf'_cont.measurable hf1 T n)
        hI_memLp hcore)
  -- both limits are the same `L²` limit ⇒ they coincide
  have huniq : hI_memLp.toLp I = itoIntegralCLM_T (μ := μ) T hBmeas gf' :=
    tendsto_nhds_unique hcore_Lp hgf'
  have hae : I =ᵐ[μ] (itoIntegralCLM_T (μ := μ) T hBmeas gf') := by
    rw [← huniq]; exact (hI_memLp.coeFn_toLp).symm
  filter_upwards [hae] with ω hω
  rw [hI] at hω
  simp only at hω
  linarith [hω]

end MathFin
