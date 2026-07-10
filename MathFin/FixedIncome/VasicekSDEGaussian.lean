/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import BrownianMotion.Gaussian.BrownianMotion
public import MathFin.Foundations.WienerIntegralGaussian
public import MathFin.FixedIncome.VasicekSDE

/-!
# Vasicek terminal distribution, derived from the SDE (phase: Itô→pricing bridge)

`FixedIncome/VasicekSDE.lean` *posited* the terminal law of the Vasicek short
rate `r_t ~ N(mean, var)` as closed-form `def`s, in the `BSCallHyp` style, with
the SDE→law derivation explicitly open ("gated on the continuous Itô integral").

This file **derives** that law. The Vasicek SDE `dr_t = κ(θ − r_t)dt + σ dB_t`
has solution

  `r_t = r₀ e^{−κt} + θ(1 − e^{−κt}) + σ ∫₀ᵗ e^{−κ(t−s)} dB_s`,

whose stochastic term is the Wiener integral of the **deterministic** integrand
`e^{−κ(t−s)}`. By `wienerIntegralLp_hasLaw_gaussian`
(`Foundations/WienerIntegralGaussian.lean`) that integral is Gaussian, centred,
with variance its `L²`-norm `∫₀ᵗ e^{−2κ(t−s)} ds = (1 − e^{−2κt})/(2κ)` — exactly
`vasicekSDEVariance σ κ t / σ²`. The affine map `x ↦ mean + σ x` then sends the
law to `gaussianReal (vasicekSDEMean) (vasicekSDEVariance)`.

This is the **first consumer of the deterministic-integrand Itô tower in the
FixedIncome layer** — the analytic Wiener/Itô machinery becomes load-bearing in
a pricing module, closing the two-tower gap for the Vasicek short rate.

## Main results

* `vasicekDiffusionTerm`: the genuine stochastic term `σ ∫₀ᵗ e^{−κ(t−s)} dB_s`.
* `vasicekKernel_integral_sq`: `∫₀ᵀ (e^{−κ(T−s)})² ds = (1 − e^{−2κT})/(2κ)`.
* `vasicekShortRate_hasLaw_gaussian`: the genuine terminal short rate
  `mean + σ ∫₀ᵀ e^{−κ(T−s)} dB_s` has law `N(vasicekSDEMean, vasicekSDEVariance)`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The Vasicek diffusion kernel `e^{−κ(T−s)}` as an `L²` integrand -/

/-- The Vasicek diffusion kernel `s ↦ e^{−κ(T−s)}`. -/
noncomputable def vasicekKernel (κ T : ℝ) : ℝ → ℝ := fun s ↦ Real.exp (-(κ * (T - s)))

/-- The restricted volume measure on `(0, T]` is finite. -/
private instance vasicek_finite_restrict (T : ℝ≥0) :
    IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc];
      exact ENNReal.ofReal_lt_top⟩

/-- The kernel is in `L²((0, T])` (continuous, bounded by `1` on the support
for `κ ≥ 0`). -/
lemma vasicekKernel_memLp (κ : ℝ) (hκ : 0 ≤ κ) (T : ℝ≥0) :
    MemLp (vasicekKernel κ T) 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
  refine (memLp_top_of_bound (by unfold vasicekKernel; fun_prop) 1 ?_).mono_exponent le_top
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ ?_)
  intro s hs
  rw [vasicekKernel, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_one_iff.mpr ?_
  have hTs : 0 ≤ (T : ℝ) - s := by linarith [hs.2]
  nlinarith [mul_nonneg hκ hTs]

/-- The kernel as an element of `L²((0, T])`. -/
noncomputable def vasicekKernelLp (κ : ℝ) (hκ : 0 ≤ κ) (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  (vasicekKernel_memLp κ hκ T).toLp _

/-! ### The kernel's `L²`-norm is the Vasicek variance (the deterministic integral) -/

/-- **The Riemann integral fixing the variance**:
`∫₀ᵀ (e^{−κ(T−s)})² ds = (1 − e^{−2κT})/(2κ)`, by the FTC with antiderivative
`s ↦ e^{−2κ(T−s)}/(2κ)`. -/
lemma vasicekKernel_integral_sq (κ : ℝ) (hκ : κ ≠ 0) (T : ℝ≥0) :
    ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekKernel κ T s) ^ 2 ∂volume
      = (1 - Real.exp (-(2 * κ * T))) / (2 * κ) := by
  have hsq : ∀ s : ℝ, (vasicekKernel κ T s) ^ 2 = Real.exp (-(2 * κ * ((T : ℝ) - s))) := by
    intro s
    rw [vasicekKernel, sq, ← Real.exp_add]
    congr 1
    ring
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (T : ℝ))]
  rw [show (fun s ↦ (vasicekKernel κ T s) ^ 2)
        = (fun s ↦ Real.exp (-(2 * κ * ((T : ℝ) - s)))) from funext hsq]
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) (T : ℝ),
      HasDerivAt (fun s ↦ Real.exp (-(2 * κ * ((T : ℝ) - s))) / (2 * κ))
        (Real.exp (-(2 * κ * ((T : ℝ) - s)))) s := by
    intro s _
    have h1 : HasDerivAt (fun s ↦ -(2 * κ * ((T : ℝ) - s)))
        (2 * κ) s := by
      have : HasDerivAt (fun s ↦ -(2 * κ * ((T : ℝ) - s)))
          (-(2 * κ * (-1))) s := by
        apply HasDerivAt.neg
        apply HasDerivAt.const_mul
        simpa using (hasDerivAt_id s).const_sub (T : ℝ)
      simpa using this
    have h2 := (Real.hasDerivAt_exp _).comp s h1
    have h3 := h2.div_const (2 * κ)
    rwa [mul_div_assoc, div_self (mul_ne_zero two_ne_zero hκ), mul_one] at h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]
  rw [show (2 : ℝ) * κ * ((T : ℝ) - 0) = 2 * κ * T by ring]
  ring

/-! ### The genuine terminal short rate and its derived Gaussian law -/

/-- The genuine Vasicek diffusion term `σ ∫₀ᵀ e^{−κ(T−s)} dB_s`. -/
noncomputable def vasicekDiffusionTerm (hB : IsPreBrownianReal B μ) (κ σ : ℝ)
    (hκ : 0 ≤ κ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  σ * (wienerIntegralLp B hB T (vasicekKernelLp κ hκ T) ω)

/-- **Vasicek terminal law, derived.** The genuine short rate
`r_T = vasicekSDEMean + σ ∫₀ᵀ e^{−κ(T−s)} dB_s` (the SDE solution) has the
Gaussian law `N(vasicekSDEMean, vasicekSDEVariance)` — the closed form `VasicekSDE.lean`
posited is now a theorem. -/
theorem vasicekShortRate_hasLaw_gaussian (hB : IsPreBrownianReal B μ)
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    HasLaw (fun ω ↦ vasicekSDEMean r₀ θ κ (T : ℝ)
        + σ * (wienerIntegralLp B hB T (vasicekKernelLp κ hκ.le T) ω))
      (gaussianReal (vasicekSDEMean r₀ θ κ (T : ℝ)) (vasicekSDEVariance σ κ (T : ℝ)).toNNReal) μ := by
  -- The Wiener integral of the kernel is Gaussian, centred, variance = ∫ kernel².
  have hW : HasLaw (fun ω ↦ wienerIntegralLp B hB T (vasicekKernelLp κ hκ.le T) ω)
      (gaussianReal 0 (∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
        (vasicekKernelLp κ hκ.le T s) ^ 2 ∂volume).toNNReal) μ :=
    wienerIntegralLp_hasLaw_gaussian hB T _
  -- Replace the L² representative's integral by the kernel's (a.e. equal).
  have hInt : (∫ s in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekKernelLp κ hκ.le T s) ^ 2 ∂volume)
      = (1 - Real.exp (-(2 * κ * T))) / (2 * κ) := by
    rw [show (∫ s in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekKernelLp κ hκ.le T s) ^ 2 ∂volume)
          = ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekKernel κ T s) ^ 2 ∂volume by
        refine integral_congr_ae ?_
        filter_upwards [(vasicekKernel_memLp κ hκ.le T).coeFn_toLp] with s hs
        rw [vasicekKernelLp, hs]]
    exact vasicekKernel_integral_sq κ hκ.ne' T
  rw [hInt] at hW
  -- Scale by σ then shift by the mean; the affine map sends N(0, ∫kernel²) to N(mean, σ²·∫kernel²).
  have hexp_le : Real.exp (-(2 * κ * (T : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hκ.le, NNReal.coe_nonneg T])
  have hden : (0 : ℝ) < 2 * κ := by linarith
  have hkernel_nonneg : (0 : ℝ) ≤ (1 - Real.exp (-(2 * κ * (T : ℝ)))) / (2 * κ) :=
    div_nonneg (by linarith) hden.le
  have hvar_nonneg : (0 : ℝ) ≤ vasicekSDEVariance σ κ (T : ℝ) := by
    unfold vasicekSDEVariance
    exact div_nonneg (mul_nonneg (sq_nonneg σ) (by linarith)) hden.le
  have hShift := gaussianReal_const_add (gaussianReal_const_mul hW σ)
    (vasicekSDEMean r₀ θ κ (T : ℝ))
  convert hShift using 2
  · ring
  · refine NNReal.coe_injective ?_
    rw [Real.coe_toNNReal _ hvar_nonneg, NNReal.coe_mul, NNReal.coe_mk,
      Real.coe_toNNReal _ hkernel_nonneg]
    unfold vasicekSDEVariance
    ring

end MathFin
