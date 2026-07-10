/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.WeightedQuadraticVariation
public import MathFin.Foundations.ItoFormulaTDRemainder
public import MathFin.Foundations.ItoIntegralRiemannBridgeTD

/-! # Time-dependent Itô formula in `L²` (named-limit + CLM-identified)

Summit A′: the time-dependent analogue of `ito_formula_L2` / `ito_formula_L2_bddDeriv`.
For `f(t, x)` of class `C^{1,2}` with the displayed bounded higher partials,

  `f(T, B_T) − f(0, B_0) =ᵐ[μ] itoIntegralCLM_T gfx + ∫₀ᵀ (f_t + ½ f_xx)(s, B_s) ds`,

where `gfx` is the trim-`L²` realization of `s ↦ f_x(s, B_s)` — the classical
`df = f_x dB + (f_t + ½ f_xx) dt` in integrated `L²` form.

The assembly mirrors the time-independent one, with one extra vanishing term. The discrete
2D Itô formula (`discrete_ito_formula_2d`) makes, along the uniform partition of `[0,T]`,

  `Isumₙ − (f(T,B_T) − f(0,B_0) − ∫f_t ds − ½∫f_xx ds)
     = −(Tsumₙ − ∫f_t ds) − ½(QVₙ − ∫f_xx ds) − Remₙ`,

in which the unbounded boundary term cancels, so the `L²` estimate only ever sees three
vanishing terms: the drift Riemann sums (`tendsto_riemann_L2_process`, with the joint
continuity of `f_t` *derived* from its bounded partials — `f_tt, f_tx` bounded makes
`f_t` jointly Lipschitz), the weighted quadratic variation with the adapted weight
`f_xx(·, B)` (`tendsto_weighted_qv_process`), and the 2D Itô–Taylor remainder
(`tendsto_ito_remainder_td`). The CLM identification then runs through the
time-dependent Riemann ↔ CLM bridge (`itoIntegralCLM_T_of_bdd_cont_td` at `φ = f_x`):
both the named limit and `itoIntegralCLM_T gfx` are the `L²`-limit of the same sums
`∑ f_x(tₖ, B_{tₖ})·ΔBₖ`, so they coincide a.e.

Unbounded coefficients (e.g. GBM's exponential value function) remain honestly out of
scope — the same named gap as the time-independent layer.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter QuadraticVariationL2 ItoIsometryAdapted
  ItoIntegralCLM ItoIntegralBrownian ItoIntegralRiemannBridge ItoIntegralRiemannBridgeTD
open scoped NNReal Topology

/-- **Joint continuity from bounded partials.** A two-variable `g(t, x)` whose time and
space partial derivatives are both bounded is jointly Lipschitz, hence continuous: split
the increment through the corner `(q₁, p₂)` and apply the mean-value bound in each slot.
Consumed at `g = f_t` — the time-dependent Itô formula never needs joint continuity of
`f_t` as a *hypothesis*, since its bounded partials already force it. -/
theorem continuous_uncurry_of_bdd_partials {g g_t g_x : ℝ → ℝ → ℝ}
    (hg_t : ∀ t x, HasDerivAt (fun s ↦ g s x) (g_t t x) t)
    (hg_x : ∀ t x, HasDerivAt (fun u ↦ g t u) (g_x t x) x)
    {Mt Mx : ℝ} (hMt : ∀ t x, |g_t t x| ≤ Mt) (hMx : ∀ t x, |g_x t x| ≤ Mx) :
    Continuous fun p : ℝ × ℝ ↦ g p.1 p.2 := by
  have hMt0 : 0 ≤ Mt := le_trans (abs_nonneg _) (hMt 0 0)
  have hMx0 : 0 ≤ Mx := le_trans (abs_nonneg _) (hMx 0 0)
  refine (LipschitzWith.of_dist_le_mul (K := ⟨Mt + Mx, add_nonneg hMt0 hMx0⟩)
    fun p q ↦ ?_).continuous
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  show |g p.1 p.2 - g q.1 q.2| ≤ (Mt + Mx) * max |p.1 - q.1| |p.2 - q.2|
  have h1 : |g p.1 p.2 - g q.1 p.2| ≤ Mt * |p.1 - q.1| :=
    abs_sub_le_of_hasDerivAt (fun s ↦ hg_t s p.2) (fun s ↦ hMt s p.2) q.1 p.1
  have h2 : |g q.1 p.2 - g q.1 q.2| ≤ Mx * |p.2 - q.2| :=
    abs_sub_le_of_hasDerivAt (fun u ↦ hg_x q.1 u) (fun u ↦ hMx q.1 u) q.2 p.2
  have h3 : |g p.1 p.2 - g q.1 q.2| ≤ Mt * |p.1 - q.1| + Mx * |p.2 - q.2| :=
    (abs_sub_le _ _ _).trans (add_le_add h1 h2)
  have e1 : Mt * |p.1 - q.1| ≤ Mt * max |p.1 - q.1| |p.2 - q.2| :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hMt0
  have e2 : Mx * |p.2 - q.2| ≤ Mx * max |p.1 - q.1| |p.2 - q.2| :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hMx0
  nlinarith [h3, e1, e2]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- **Time-dependent Itô formula in `L²` (named-limit form).** For `f(t, x)` with the
`C^{1,2}`-with-bounds package (`f_t, f_tt, f_tx` and `f_x, f_xx, f_xxx`, with `f_t, f_xx,
f_tt, f_tx, f_xxx` bounded and `f_xx` jointly continuous), the uniform-partition
Riemann–Itô sums `∑ f_x(tₖ, B_{tₖ})·ΔBₖ` converge in `L²(μ)` to
`f(T, B_T) − f(0, B_0) − ∫₀ᵀ f_t(s, B_s) ds − ½∫₀ᵀ f_xx(s, B_s) ds`. No bound on `f_x`
is needed: the discrete identity cancels the boundary term before any estimate. -/
theorem ito_formula_td_L2
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 ↦ B s ω))
    (T : ℝ≥0) {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
    (hf_tt : ∀ t x, HasDerivAt (fun s ↦ f_t s x) (f_tt t x) t)
    (hf_tx : ∀ t x, HasDerivAt (fun u ↦ f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
    (hf_xxx : ∀ t x, HasDerivAt (fun u ↦ f_xx t u) (f_xxx t x) x)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)
    {Ct C2 Ctt Ctx Cxxx : ℝ}
    (hbd_t : ∀ t x, |f_t t x| ≤ Ct) (hbd_xx : ∀ t x, |f_xx t x| ≤ C2)
    (hbd_tt : ∀ t x, |f_tt t x| ≤ Ctt) (hbd_tx : ∀ t x, |f_tx t x| ≤ Ctx)
    (hbd_xxx : ∀ t x, |f_xxx t x| ≤ Cxxx) :
    Tendsto (fun n : ℕ ↦
        ∫ ω, (∑ k ∈ Finset.range n,
                f_x (unifPart T n k) (B (unifPart T n k) ω)
                  * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)
              - (f T (B T ω) - f 0 (B 0 ω)
                  - ∫ s in Set.Ioc 0 T, f_t s (B s ω) ∂ItoIntegralL2.timeMeasure
                  - (1 / 2) * ∫ s in Set.Ioc 0 T,
                      f_xx s (B s ω) ∂ItoIntegralL2.timeMeasure)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  classical
  have hCt0 : 0 ≤ Ct := le_trans (abs_nonneg _) (hbd_t 0 0)
  have hC20 : 0 ≤ C2 := le_trans (abs_nonneg _) (hbd_xx 0 0)
  -- section measurability (each section is differentiable, hence continuous)
  have hf_tm : ∀ c : ℝ, Measurable (f_t c) := fun c ↦
    (continuous_iff_continuousAt.mpr fun x ↦ (hf_tx c x).continuousAt).measurable
  have hf_xxm : ∀ c : ℝ, Measurable (f_xx c) := fun c ↦
    (continuous_iff_continuousAt.mpr fun x ↦ (hf_xxx c x).continuousAt).measurable
  -- joint continuity of `f_t` (bounded partials ⇒ jointly Lipschitz), then the pathwise
  -- continuity of the two weight processes
  have hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2 :=
    continuous_uncurry_of_bdd_partials hf_tt hf_tx hbd_tt hbd_tx
  have hwt_cont : ∀ ω, Continuous fun s : ℝ≥0 ↦ f_t s (B s ω) := fun ω ↦
    hf_t_cont.comp ((NNReal.continuous_coe).prodMk (hBcont ω))
  have hwxx_cont : ∀ ω, Continuous fun s : ℝ≥0 ↦ f_xx s (B s ω) := fun ω ↦
    hf_xx_cont.comp ((NNReal.continuous_coe).prodMk (hBcont ω))
  -- the three vanishing terms: drift Riemann sums (A2′), weighted QV with the adapted
  -- weight `f_xx(·, B)` (A1′), and the 2D Itô–Taylor remainder (A3′)
  have hA1 := tendsto_weighted_qv_process hB hBmeas
    (w := fun s ω ↦ f_xx s (B s ω))
    (fun s ↦ adaptedAt_comp_eval le_rfl (hf_xxm s))
    hwxx_cont hC20 (fun s ω ↦ hbd_xx _ _) T
  have hA2 := tendsto_riemann_L2_process (μ := μ)
    (w := fun s ω ↦ f_t s (B s ω))
    (fun s ↦ (hf_tm s).comp (hBmeas s))
    hwt_cont hCt0 (fun s ω ↦ hbd_t _ _) T
  have hA3 := tendsto_ito_remainder_td hB hBmeas T hf_t hf_tt hf_tx hf_x hf_xx hf_xxx
    hbd_tt hbd_tx hbd_xxx
  set Isum : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n,
      f_x (unifPart T n k) (B (unifPart T n k) ω)
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) with hIsum
  set Tsum : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n,
      f_t (unifPart T n k) (B (unifPart T n k) ω)
        * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) with hTsum
  set QVw : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n,
      f_xx (unifPart T n k) (B (unifPart T n k) ω)
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 with hQVw
  set Rem : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n,
      discreteTaylorRemainder2D f f_t f_x f_xx (unifPart T n k) (unifPart T n (k + 1))
        (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω) with hRem
  set It : Ω → ℝ := fun ω ↦
    ∫ s in Set.Ioc 0 T, f_t s (B s ω) ∂ItoIntegralL2.timeMeasure with hIt
  set Ixx : Ω → ℝ := fun ω ↦
    ∫ s in Set.Ioc 0 T, f_xx s (B s ω) ∂ItoIntegralL2.timeMeasure with hIxx
  show Tendsto (fun n ↦ ∫ ω,
      (Isum n ω - (f T (B T ω) - f 0 (B 0 ω) - It ω - (1 / 2) * Ixx ω)) ^ 2 ∂μ)
    atTop (𝓝 0)
  -- `L²` membership of the three difference terms (for the squeeze's integrability)
  have hTsum_memLp : ∀ n, MemLp (Tsum n) 2 μ := by
    intro n
    simp only [hTsum]
    exact MemLp.of_bound
      (Finset.measurable_sum _ fun k _ ↦
        ((hf_tm _).comp (hBmeas _)).mul_const _).aestronglyMeasurable
      (Ct * T) (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]
        exact abs_riemann_weight_sum_le (w := fun s ω ↦ f_t s (B s ω))
          hCt0 (fun s ω ↦ hbd_t _ _) T n ω)
  have hIt_memLp : MemLp It 2 μ := memLp_pathIntegral_process (μ := μ)
    (fun s ↦ (hf_tm s).comp (hBmeas s)) hwt_cont hCt0 (fun s ω ↦ hbd_t _ _) T
  have hIxx_memLp : MemLp Ixx 2 μ := memLp_pathIntegral_process (μ := μ)
    (fun s ↦ (hf_xxm s).comp (hBmeas s)) hwxx_cont hC20 (fun s ω ↦ hbd_xx _ _) T
  have hQVw_memLp : ∀ n, MemLp (QVw n) 2 μ := by
    intro n
    rw [hQVw]
    refine memLp_finsetSum _ fun k _ ↦ ?_
    have hZ : MemLp (fun ω ↦ (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) 2 μ := by
      have h := (memLp_increment_sq_centered_two hB (unifPart T n k) (unifPart T n (k + 1))
          ((unifPart T n (k + 1) : ℝ) - unifPart T n k)).add
          (memLp_const (μ := μ) ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
      have heq : ((fun ω ↦ (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            - ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
          + fun _ : Ω ↦ ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
          = fun ω ↦ (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2 := by
        funext ω; simp only [Pi.add_apply]; ring
      rwa [heq] at h
    have haesm : AEStronglyMeasurable (fun ω ↦ f_xx (unifPart T n k) (B (unifPart T n k) ω)
        * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) μ :=
      ((hf_xxm _).comp (hBmeas _)).aestronglyMeasurable.mul hZ.aestronglyMeasurable
    refine MemLp.mono (hZ.const_mul C2) haesm (Eventually.of_forall fun ω ↦ ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg hC20]
    exact mul_le_mul_of_nonneg_right (hbd_xx _ _) (abs_nonneg _)
  have hRem_memLp : ∀ n, MemLp (Rem n) 2 μ := by
    intro n
    rw [hRem]
    exact memLp_finsetSum _ fun k _ ↦
      memLp_discreteTaylorRemainder2D_two hB hBmeas hf_t hf_tt hf_tx hf_x hf_xx hf_xxx
        hbd_tt hbd_tx hbd_xxx _ _
  have hInt_t : ∀ n, Integrable (fun ω ↦ (Tsum n ω - It ω) ^ 2) μ := fun n ↦
    ((hTsum_memLp n).sub hIt_memLp).integrable_sq
  have hInt_x : ∀ n, Integrable (fun ω ↦ (QVw n ω - Ixx ω) ^ 2) μ := fun n ↦
    ((hQVw_memLp n).sub hIxx_memLp).integrable_sq
  have hInt_r : ∀ n, Integrable (fun ω ↦ Rem n ω ^ 2) μ := fun n ↦
    (hRem_memLp n).integrable_sq
  -- the upper bound `3∫(Tsumₙ−∫f_t)² + ¾∫(QVₙ−∫f_xx)² + 3∫Remₙ² → 0` (A2′ + A1′ + A3′)
  have hupper : Tendsto (fun n ↦ 3 * ∫ ω, (Tsum n ω - It ω) ^ 2 ∂μ
      + (3 / 4) * ∫ ω, (QVw n ω - Ixx ω) ^ 2 ∂μ + 3 * ∫ ω, Rem n ω ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := ((hA2.const_mul 3).add (hA1.const_mul (3 / 4))).add (hA3.const_mul 3)
    simp only [mul_zero, add_zero] at h
    exact h
  refine squeeze_zero' (Eventually.of_forall fun n ↦ integral_nonneg fun ω ↦ sq_nonneg _)
    ?_ hupper
  filter_upwards [eventually_gt_atTop 0] with n hn
  -- discrete 2D Itô formula: the boundary term cancels, leaving the three differences
  have hpt : ∀ ω, Isum n ω - (f T (B T ω) - f 0 (B 0 ω) - It ω - (1 / 2) * Ixx ω)
      = -(Tsum n ω - It ω) - (1 / 2) * (QVw n ω - Ixx ω) - Rem n ω := by
    intro ω
    have hd := discrete_ito_formula_2d n (fun k ↦ (unifPart T n k : ℝ))
      (fun k ↦ B (unifPart T n k) ω) f f_t f_x f_xx
    have hnn : unifPart T n n = T := by
      have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [unifPart, div_self hne, one_mul]
    have hz : unifPart T n 0 = 0 := by simp [unifPart]
    rw [hnn, hz, NNReal.coe_zero] at hd
    simp only [hIsum, hTsum, hQVw, hRem]
    linarith [hd]
  calc ∫ ω, (Isum n ω - (f T (B T ω) - f 0 (B 0 ω) - It ω - (1 / 2) * Ixx ω)) ^ 2 ∂μ
      = ∫ ω, (-(Tsum n ω - It ω) - (1 / 2) * (QVw n ω - Ixx ω) - Rem n ω) ^ 2 ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω ↦ ?_)
        show (Isum n ω - (f T (B T ω) - f 0 (B 0 ω) - It ω - 1 / 2 * Ixx ω)) ^ 2
          = (-(Tsum n ω - It ω) - 1 / 2 * (QVw n ω - Ixx ω) - Rem n ω) ^ 2
        rw [hpt ω]
    _ ≤ ∫ ω, (3 * (Tsum n ω - It ω) ^ 2 + (3 / 4) * (QVw n ω - Ixx ω) ^ 2
          + 3 * Rem n ω ^ 2) ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg _)
          ((((hInt_t n).const_mul 3).add ((hInt_x n).const_mul (3 / 4))).add
            ((hInt_r n).const_mul 3))
          (Eventually.of_forall fun ω ↦ ?_)
        nlinarith [sq_nonneg ((Tsum n ω - It ω) - (1 / 2) * (QVw n ω - Ixx ω)),
          sq_nonneg ((Tsum n ω - It ω) - Rem n ω),
          sq_nonneg ((1 / 2) * (QVw n ω - Ixx ω) - Rem n ω)]
    _ = 3 * ∫ ω, (Tsum n ω - It ω) ^ 2 ∂μ + (3 / 4) * ∫ ω, (QVw n ω - Ixx ω) ^ 2 ∂μ
          + 3 * ∫ ω, Rem n ω ^ 2 ∂μ := by
        have hAB : Integrable (fun ω ↦ 3 * (Tsum n ω - It ω) ^ 2
            + (3 / 4) * (QVw n ω - Ixx ω) ^ 2) μ :=
          ((hInt_t n).const_mul 3).add ((hInt_x n).const_mul (3 / 4))
        rw [integral_add hAB ((hInt_r n).const_mul 3),
          integral_add ((hInt_t n).const_mul 3) ((hInt_x n).const_mul (3 / 4)),
          integral_const_mul, integral_const_mul, integral_const_mul]

/-- **CLM-identified time-dependent Itô formula in `L²`** — the classical
`df = f_x dB + (f_t + ½f_xx) dt` in integrated form. For `f(t, x)` with the
`C^{1,2}`-with-bounds package and jointly continuous bounded `f_x`, there is an Itô-`L²`
integrand `gfx` (the trim-`L²` realization of `s ↦ f_x(s, B_s)`) with

  `f(T, B_T) − f(0, B_0) =ᵐ[μ] itoIntegralCLM_T gfx + ∫₀ᵀ (f_t + ½f_xx)(s, B_s) ds`. -/
theorem ito_formula_td_L2_bddDeriv_explicit
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 ↦ B s ω))
    (T : ℝ≥0) {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
    (hf_tt : ∀ t x, HasDerivAt (fun s ↦ f_t s x) (f_tt t x) t)
    (hf_tx : ∀ t x, HasDerivAt (fun u ↦ f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
    (hf_xxx : ∀ t x, HasDerivAt (fun u ↦ f_xx t u) (f_xxx t x) x)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)
    {Ct C1 C2 Ctt Ctx Cxxx : ℝ}
    (hbd_t : ∀ t x, |f_t t x| ≤ Ct) (hbd_x : ∀ t x, |f_x t x| ≤ C1)
    (hbd_xx : ∀ t x, |f_xx t x| ≤ C2)
    (hbd_tt : ∀ t x, |f_tt t x| ≤ Ctt) (hbd_tx : ∀ t x, |f_tx t x| ≤ Ctx)
    (hbd_xxx : ∀ t x, |f_xxx t x| ≤ Cxxx) :
    ∃ gfx : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (⇑gfx =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun z ↦ f_x z.1 (B z.1 z.2)) ∧
      (fun ω ↦ f T (B T ω) - f 0 (B 0 ω)) =ᵐ[μ]
        (fun ω ↦ (itoIntegralCLM_T hB T hBmeas gfx) ω
          + ∫ s in Set.Ioc 0 T,
              (f_t s (B s ω) + (1 / 2) * f_xx s (B s ω)) ∂ItoIntegralL2.timeMeasure) := by
  classical
  have hCt0 : 0 ≤ Ct := le_trans (abs_nonneg _) (hbd_t 0 0)
  have hC20 : 0 ≤ C2 := le_trans (abs_nonneg _) (hbd_xx 0 0)
  have hf_tm : ∀ c : ℝ, Measurable (f_t c) := fun c ↦
    (continuous_iff_continuousAt.mpr fun x ↦ (hf_tx c x).continuousAt).measurable
  have hf_xxm : ∀ c : ℝ, Measurable (f_xx c) := fun c ↦
    (continuous_iff_continuousAt.mpr fun x ↦ (hf_xxx c x).continuousAt).measurable
  have hfx_meas : ∀ c : ℝ, Measurable (f_x c) := fun c ↦
    (hf_x_cont.comp (continuous_const.prodMk continuous_id)).measurable
  have hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2 :=
    continuous_uncurry_of_bdd_partials hf_tt hf_tx hbd_tt hbd_tx
  have hwt_cont : ∀ ω, Continuous fun s : ℝ≥0 ↦ f_t s (B s ω) := fun ω ↦
    hf_t_cont.comp ((NNReal.continuous_coe).prodMk (hBcont ω))
  have hwxx_cont : ∀ ω, Continuous fun s : ℝ≥0 ↦ f_xx s (B s ω) := fun ω ↦
    hf_xx_cont.comp ((NNReal.continuous_coe).prodMk (hBcont ω))
  -- the bridge: `gfx` is the trim-`L²` realization of `s ↦ f_x(s, B_s)`
  obtain ⟨gfx, hgfx_eq, hgfx⟩ :=
    itoIntegralCLM_T_of_bdd_cont_td hB hBmeas hBcont hf_x_cont hbd_x T
  refine ⟨gfx, hgfx_eq, ?_⟩
  set I : Ω → ℝ := fun ω ↦ f T (B T ω) - f 0 (B 0 ω)
    - ∫ s in Set.Ioc 0 T, f_t s (B s ω) ∂ItoIntegralL2.timeMeasure
    - (1 / 2) * ∫ s in Set.Ioc 0 T, f_xx s (B s ω) ∂ItoIntegralL2.timeMeasure with hI
  -- every section of `f` is `C₁`-Lipschitz, so `f(t, B_t)` is dominated by an `L²` function
  have hlip : ∀ t x : ℝ, |f t x| ≤ |f t 0| + C1 * |x| := fun t x ↦ by
    have h := abs_sub_le_of_hasDerivAt (g := fun u ↦ f t u) (g' := fun u ↦ f_x t u)
      (fun u ↦ hf_x t u) (fun u ↦ hbd_x t u) 0 x
    rw [sub_zero] at h
    have h2 : |f t x| - |f t 0| ≤ |f t x - f t 0| := abs_sub_abs_le_abs_sub _ _
    linarith
  have hfB : ∀ t : ℝ≥0, MemLp (fun ω ↦ f t (B t ω)) 2 μ := fun t ↦ by
    have hft_cont : Continuous (f (t : ℝ)) :=
      continuous_iff_continuousAt.mpr fun x ↦ (hf_x (t : ℝ) x).continuousAt
    refine MemLp.mono ((memLp_const (μ := μ) |f (t : ℝ) 0|).add
        ((memLp_eval hB t).norm.const_mul C1))
      ((hft_cont.measurable.comp (hBmeas t)).aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ ?_)
    calc ‖f (t : ℝ) (B t ω)‖ = |f (t : ℝ) (B t ω)| := Real.norm_eq_abs _
      _ ≤ |f (t : ℝ) 0| + C1 * ‖B t ω‖ := by rw [Real.norm_eq_abs]; exact hlip _ _
      _ ≤ ‖|f (t : ℝ) 0| + C1 * ‖B t ω‖‖ := le_abs_self _
  have hIt_memLp : MemLp (fun ω ↦
      ∫ s in Set.Ioc 0 T, f_t s (B s ω) ∂ItoIntegralL2.timeMeasure) 2 μ :=
    memLp_pathIntegral_process (μ := μ)
      (fun s ↦ (hf_tm s).comp (hBmeas s)) hwt_cont hCt0 (fun s ω ↦ hbd_t _ _) T
  have hIxx_memLp : MemLp (fun ω ↦
      ∫ s in Set.Ioc 0 T, f_xx s (B s ω) ∂ItoIntegralL2.timeMeasure) 2 μ :=
    memLp_pathIntegral_process (μ := μ)
      (fun s ↦ (hf_xxm s).comp (hBmeas s)) hwxx_cont hC20 (fun s ω ↦ hbd_xx _ _) T
  have hI_memLp : MemLp I 2 μ :=
    (((hfB T).sub (hfB 0)).sub hIt_memLp).sub (hIxx_memLp.const_mul (1 / 2))
  -- the named-limit core: the Riemann–Itô sums converge in `L²` to `I`; lift to `Lp`
  have hcore := ito_formula_td_L2 hB hBmeas hBcont T hf_t hf_tt hf_tx hf_x hf_xx
    hf_xxx hf_xx_cont hbd_t hbd_xx hbd_tt hbd_tx hbd_xxx
  have hcoreI : Tendsto (fun n ↦
      ∫ ω, (riemannφTD hBmeas f_x T n ω - I ω) ^ 2 ∂μ) atTop (𝓝 0) := hcore
  have hcore_Lp : Tendsto (fun n ↦ (memLp_riemannφTD hB hBmeas hfx_meas hbd_x T n).toLp
      (riemannφTD hBmeas f_x T n)) atTop (𝓝 (hI_memLp.toLp I)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (tendsto_norm_toLp_sub' (fun n ↦ memLp_riemannφTD hB hBmeas hfx_meas hbd_x T n)
        hI_memLp hcoreI)
  -- both are the `L²` limit of the same sums ⇒ they coincide
  have huniq : hI_memLp.toLp I = itoIntegralCLM_T hB T hBmeas gfx :=
    tendsto_nhds_unique hcore_Lp hgfx
  have hae : I =ᵐ[μ] (itoIntegralCLM_T hB T hBmeas gfx) := by
    rw [← huniq]; exact (hI_memLp.coeFn_toLp).symm
  filter_upwards [hae] with ω hω
  rw [hI] at hω
  simp only at hω
  -- recombine the two `ds`-integrals into the classical drift `∫ (f_t + ½f_xx) ds`
  haveI : IsFiniteMeasure (ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 T)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          ItoIntegralL2.timeMeasure_Ioc]
        exact ENNReal.ofReal_lt_top⟩
  have h1 : Integrable (fun s : ℝ≥0 ↦ f_t s (B s ω))
      (ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 T)) := by
    refine Integrable.mono' (integrable_const Ct)
      (hwt_cont ω).measurable.aestronglyMeasurable (ae_of_all _ fun s ↦ ?_)
    rw [Real.norm_eq_abs]; exact hbd_t _ _
  have h2 : Integrable (fun s : ℝ≥0 ↦ (1 / 2) * f_xx s (B s ω))
      (ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 T)) := by
    refine Integrable.mono' (integrable_const ((1 / 2) * C2))
      ((hwxx_cont ω).measurable.aestronglyMeasurable.const_mul _) (ae_of_all _ fun s ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact mul_le_mul_of_nonneg_left (hbd_xx _ _) (by norm_num)
  have hsplit : ∫ s in Set.Ioc 0 T,
        (f_t s (B s ω) + (1 / 2) * f_xx s (B s ω)) ∂ItoIntegralL2.timeMeasure
      = (∫ s in Set.Ioc 0 T, f_t s (B s ω) ∂ItoIntegralL2.timeMeasure)
        + (1 / 2) * ∫ s in Set.Ioc 0 T, f_xx s (B s ω) ∂ItoIntegralL2.timeMeasure := by
    rw [integral_add h1 h2, integral_const_mul]
  show f T (B T ω) - f 0 (B 0 ω) = (itoIntegralCLM_T hB T hBmeas gfx) ω
    + ∫ s in Set.Ioc 0 T,
        (f_t s (B s ω) + (1 / 2) * f_xx s (B s ω)) ∂ItoIntegralL2.timeMeasure
  rw [hsplit]
  linarith [hω]

/-- **CLM-identified time-dependent Itô formula in `L²`** (witness-existential form). The
bare-existential wrapper of `ito_formula_td_L2_bddDeriv_explicit`: drops the explicit
identification `gfx =ᵐ [f_x(·, B_·)]` of the Itô integrand, retained for the downstream
consumers (`ItoFormulaLocalized.cutoff_bddDeriv`, the corpus `7.1.2`) that only need the
integrated identity. -/
theorem ito_formula_td_L2_bddDeriv
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 ↦ B s ω))
    (T : ℝ≥0) {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
    (hf_tt : ∀ t x, HasDerivAt (fun s ↦ f_t s x) (f_tt t x) t)
    (hf_tx : ∀ t x, HasDerivAt (fun u ↦ f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
    (hf_xxx : ∀ t x, HasDerivAt (fun u ↦ f_xx t u) (f_xxx t x) x)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)
    {Ct C1 C2 Ctt Ctx Cxxx : ℝ}
    (hbd_t : ∀ t x, |f_t t x| ≤ Ct) (hbd_x : ∀ t x, |f_x t x| ≤ C1)
    (hbd_xx : ∀ t x, |f_xx t x| ≤ C2)
    (hbd_tt : ∀ t x, |f_tt t x| ≤ Ctt) (hbd_tx : ∀ t x, |f_tx t x| ≤ Ctx)
    (hbd_xxx : ∀ t x, |f_xxx t x| ≤ Cxxx) :
    ∃ gfx : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω ↦ f T (B T ω) - f 0 (B 0 ω)) =ᵐ[μ]
        (fun ω ↦ (itoIntegralCLM_T hB T hBmeas gfx) ω
          + ∫ s in Set.Ioc 0 T,
              (f_t s (B s ω) + (1 / 2) * f_xx s (B s ω)) ∂ItoIntegralL2.timeMeasure) :=
  let ⟨gfx, _, hgfx⟩ := ito_formula_td_L2_bddDeriv_explicit hB hBmeas hBcont T hf_t hf_tt hf_tx
    hf_x hf_xx hf_xxx hf_x_cont hf_xx_cont hbd_t hbd_x hbd_xx hbd_tt hbd_tx hbd_xxx
  ⟨gfx, hgfx⟩

end MathFin
