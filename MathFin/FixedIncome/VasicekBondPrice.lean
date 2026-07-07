/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import BrownianMotion.Gaussian.BrownianMotion
public import MathFin.Foundations.WienerIntegralGaussian
public import MathFin.Foundations.BrownianMartingale
public import MathFin.FixedIncome.VasicekSDE

/-!
# The Vasicek zero-coupon bond price — the affine term structure

`FixedIncome/VasicekSDEGaussian.lean` derives the terminal short-rate law
`r_T ~ N(mean, var)` from the Wiener representation of the Ornstein–Uhlenbeck
solution. This file takes the next step in the fixed-income layer: the
**zero-coupon bond price**

  `P(0, T) = 𝔼[exp(−∫₀ᵀ r_s ds)]`,

the risk-neutral present value of one unit paid at `T`. Under the Vasicek model
the *integrated* short rate is again Gaussian, so the bond price is a Gaussian
Laplace transform and collapses to the classical **affine term structure**

  `P(0, T) = exp(−B(T)·r₀ − θ·(T − B(T)) + σ²·V(T)/2)`,   `B(T) = (1 − e^{−κT})/κ`.

## The integrated short rate, in its Wiener representation

Integrating the OU solution `r_s = r₀e^{−κs} + θ(1 − e^{−κs}) + σ∫₀ˢ e^{−κ(s−u)}dB_u`
over `s ∈ [0, T]` and swapping the (deterministic-after-integration) time order
`∫₀ᵀ∫₀ˢ e^{−κ(s−u)} ds` sends the diffusion kernel `e^{−κ(s−u)}` to the
**integrated kernel**

  `g(u) = ∫_u^T e^{−κ(s−u)} ds = (1 − e^{−κ(T−u)})/κ`,

so `∫₀ᵀ r_s ds = M(T) + σ·∫₀ᵀ g(u) dB_u`, with deterministic mean
`M(T) = r₀·B(T) + θ·(T − B(T))`. This is the exact analogue, one integration up,
of the OU-solution model that `VasicekSDEGaussian` already takes as `full`: the
integrated rate is carried in its Wiener representation (the time-order swap is
the modelling bridge, cited, not the conclusion), and everything downstream is
derived. `∫₀ᵀ g(u) dB_u` is the Wiener integral of the *deterministic* integrand
`g`, hence centred Gaussian with variance its `L²`-norm

  `V(T) = ∫₀ᵀ g(u)² du = T/κ² − 2(1 − e^{−κT})/κ³ + (1 − e^{−2κT})/(2κ³)`.

## Main results

* `vasicekIntegratedKernel_integral_sq` — the variance integral `∫₀ᵀ g² = V(T)`.
* `vasicekIntegratedRate_hasLaw_gaussian` — `∫₀ᵀ r_s ds ~ N(M(T), σ²V(T))`.
* `vasicekBondPrice_eq` — the bond price `𝔼[exp(−∫₀ᵀ r_s ds)] = exp(−M(T) + σ²V(T)/2)`.
* `vasicekBondPrice_affine` — the affine form `P(0,T) = A(T)·exp(−B(T)·r₀)`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The affine coefficient `B(T)` and the integrated kernel `g` -/

/-- The Vasicek affine coefficient `B(T) = (1 − e^{−κT})/κ` — the sensitivity of
the log bond price to the short rate, and the integral `∫₀ᵀ e^{−κs} ds`. -/
noncomputable def vasicekBondB (κ T : ℝ) : ℝ := (1 - Real.exp (-(κ * T))) / κ

/-- The **integrated Vasicek kernel** `g(u) = (1 − e^{−κ(T−u)})/κ = ∫_u^T e^{−κ(s−u)} ds`
— the deterministic integrand whose Wiener integral is the diffusion part of the
integrated short rate. -/
noncomputable def vasicekIntegratedKernel (κ T : ℝ) : ℝ → ℝ :=
  fun u => (1 - Real.exp (-(κ * (T - u)))) / κ

/-- The deterministic mean of the integrated short rate,
`M(T) = ∫₀ᵀ (r₀e^{−κs} + θ(1 − e^{−κs})) ds = r₀·B(T) + θ·(T − B(T))`. -/
noncomputable def vasicekIntegratedMean (r₀ θ κ T : ℝ) : ℝ :=
  r₀ * vasicekBondB κ T + θ * (T - vasicekBondB κ T)

/-- The variance of the integrated short rate's diffusion part (the `L²`-norm of
the integrated kernel `g`): `V(T) = ∫₀ᵀ g² = T/κ² − 2(1−e^{−κT})/κ³ + (1−e^{−2κT})/(2κ³)`. -/
noncomputable def vasicekBondV (κ T : ℝ) : ℝ :=
  T / κ ^ 2 - 2 * (1 - Real.exp (-(κ * T))) / κ ^ 3
    + (1 - Real.exp (-(2 * κ * T))) / (2 * κ ^ 3)

/-! ### The integrated kernel is an `L²` integrand -/

/-- The restricted volume measure on `(0, T]` is finite. -/
private instance vasicekBond_finite_restrict (T : ℝ≥0) :
    IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc];
      exact ENNReal.ofReal_lt_top⟩

/-- The integrated kernel is in `L²((0, T])`: on the support it lies in
`[0, 1/κ]` (for `κ > 0`), hence is bounded. -/
lemma vasicekIntegratedKernel_memLp {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    MemLp (vasicekIntegratedKernel κ T) 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
  refine (memLp_top_of_bound (by unfold vasicekIntegratedKernel; fun_prop) (1 / κ) ?_).mono_exponent
    le_top
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ ?_)
  intro s hs
  rw [vasicekIntegratedKernel, Real.norm_eq_abs]
  have hexp_pos : 0 < Real.exp (-(κ * ((T : ℝ) - s))) := Real.exp_pos _
  have hTs : 0 ≤ (T : ℝ) - s := by linarith [hs.2]
  have hexp_le : Real.exp (-(κ * ((T : ℝ) - s))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hκ.le hTs])
  rw [abs_of_nonneg (div_nonneg (by linarith) hκ.le)]
  exact (div_le_div_iff_of_pos_right hκ).mpr (by linarith)

/-- The integrated kernel as an element of `L²((0, T])`. -/
noncomputable def vasicekIntegratedKernelLp {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  (vasicekIntegratedKernel_memLp hκ T).toLp _

/-! ### The variance integral `∫₀ᵀ g² = V(T)` -/

/-- **The variance-fixing integral**: `∫₀ᵀ g(u)² du = V(T)`, by the FTC with
antiderivative `F(u) = u/κ² − 2e^{−κ(T−u)}/κ³ + e^{−2κ(T−u)}/(2κ³)`, whose
derivative expands the square `g² = (1 − 2e^{−κ(T−u)} + e^{−2κ(T−u)})/κ²`. -/
lemma vasicekIntegratedKernel_integral_sq {κ : ℝ} (hκ : κ ≠ 0) (T : ℝ≥0) :
    ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekIntegratedKernel κ T u) ^ 2 ∂volume
      = vasicekBondV κ (T : ℝ) := by
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (T : ℝ))]
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) (T : ℝ),
      HasDerivAt (fun u : ℝ => u / κ ^ 2 - 2 * Real.exp (-(κ * ((T : ℝ) - u))) / κ ^ 3
          + Real.exp (-(2 * κ * ((T : ℝ) - u))) / (2 * κ ^ 3))
        ((vasicekIntegratedKernel κ T u) ^ 2) u := by
    intro u _
    have he : Real.exp (-(2 * κ * ((T : ℝ) - u)))
        = Real.exp (-(κ * ((T : ℝ) - u))) * Real.exp (-(κ * ((T : ℝ) - u))) := by
      rw [← Real.exp_add]; congr 1; ring
    have hlin : HasDerivAt (fun u : ℝ => u / κ ^ 2) (1 / κ ^ 2) u :=
      (hasDerivAt_id u).div_const (κ ^ 2)
    have harg1 : HasDerivAt (fun u => -(κ * ((T : ℝ) - u))) κ u := by
      have h : HasDerivAt (fun u => -(κ * ((T : ℝ) - u))) (-(κ * (-1))) u := by
        apply HasDerivAt.neg; apply HasDerivAt.const_mul
        simpa using (hasDerivAt_id u).const_sub (T : ℝ)
      simpa using h
    have harg2 : HasDerivAt (fun u => -(2 * κ * ((T : ℝ) - u))) (2 * κ) u := by
      have h : HasDerivAt (fun u => -(2 * κ * ((T : ℝ) - u))) (-(2 * κ * (-1))) u := by
        apply HasDerivAt.neg; apply HasDerivAt.const_mul
        simpa using (hasDerivAt_id u).const_sub (T : ℝ)
      simpa using h
    have hexp1 := harg1.exp
    have hexp2 := harg2.exp
    have h2 := (hexp1.const_mul (2 : ℝ)).div_const (κ ^ 3)
    have h3 := hexp2.div_const (2 * κ ^ 3)
    have hcomb := (hlin.sub h2).add h3
    have hval : (1 / κ ^ 2 - 2 * (Real.exp (-(κ * ((T : ℝ) - u))) * κ) / κ ^ 3
          + Real.exp (-(2 * κ * ((T : ℝ) - u))) * (2 * κ) / (2 * κ ^ 3))
        = (vasicekIntegratedKernel κ T u) ^ 2 := by
      rw [vasicekIntegratedKernel, he]; field_simp; ring
    exact hval ▸ hcomb
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; unfold vasicekIntegratedKernel; fun_prop)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one, sub_zero, zero_div]
  rw [vasicekBondV]
  field_simp
  ring

/-! ### The integrated short rate and the bond price -/

/-- The **integrated Vasicek short rate** in its Wiener representation:
`∫₀ᵀ r_s ds = M(T) + σ·∫₀ᵀ g(u) dB_u`. -/
noncomputable def vasicekIntegratedRate (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  vasicekIntegratedMean r₀ θ κ (T : ℝ)
    + σ * (wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω)

/-- **Integrated Vasicek short rate is Gaussian.** The integrated rate
`∫₀ᵀ r_s ds = M(T) + σ∫₀ᵀ g dB` has law `N(M(T), σ²V(T))` — the affine map
`x ↦ M(T) + σx` applied to the centred Wiener integral of the integrated
kernel `g`, whose variance is `V(T)`. -/
theorem vasicekIntegratedRate_hasLaw_gaussian (hB : IsPreBrownianReal B μ)
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    HasLaw (vasicekIntegratedRate hB r₀ θ σ hκ T)
      (gaussianReal (vasicekIntegratedMean r₀ θ κ (T : ℝ))
        (σ ^ 2 * vasicekBondV κ (T : ℝ)).toNNReal) μ := by
  have hW : HasLaw (fun ω => wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω)
      (gaussianReal 0 (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (vasicekIntegratedKernelLp hκ T u) ^ 2 ∂volume).toNNReal) μ :=
    wienerIntegralLp_hasLaw_gaussian hB T _
  have hInt : (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekIntegratedKernelLp hκ T u) ^ 2 ∂volume)
      = vasicekBondV κ (T : ℝ) := by
    rw [show (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekIntegratedKernelLp hκ T u) ^ 2 ∂volume)
          = ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekIntegratedKernel κ T u) ^ 2 ∂volume by
        refine integral_congr_ae ?_
        filter_upwards [(vasicekIntegratedKernel_memLp hκ T).coeFn_toLp] with u hu
        rw [vasicekIntegratedKernelLp, hu]]
    exact vasicekIntegratedKernel_integral_sq hκ.ne' T
  rw [hInt] at hW
  have hV_nonneg : (0 : ℝ) ≤ vasicekBondV κ (T : ℝ) := by
    rw [← hInt]
    exact integral_nonneg fun u => sq_nonneg _
  have hShift := gaussianReal_const_add (gaussianReal_const_mul hW σ)
    (vasicekIntegratedMean r₀ θ κ (T : ℝ))
  convert hShift using 2
  · rfl
  · ring
  · refine NNReal.coe_injective ?_
    rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) hV_nonneg), NNReal.coe_mul, NNReal.coe_mk,
      Real.coe_toNNReal _ hV_nonneg]

/-- **The Vasicek zero-coupon bond price.** The risk-neutral present value of one
unit at `T`,

  `P(0, T) = 𝔼[exp(−∫₀ᵀ r_s ds)] = exp(−M(T) + σ²V(T)/2)`,

is the Gaussian Laplace transform of the integrated short rate: factoring off the
deterministic mean, `𝔼[exp(−σ·∫g dB)] = exp(σ²V(T)/2)` by the centred Gaussian
MGF at `−σ` (`integral_exp_mul_gaussianReal_zero`). -/
theorem vasicekBondPrice_eq (hB : IsPreBrownianReal B μ)
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(vasicekIntegratedRate hB r₀ θ σ hκ T ω)) ∂μ
      = Real.exp (-(vasicekIntegratedMean r₀ θ κ (T : ℝ)) + σ ^ 2 * vasicekBondV κ (T : ℝ) / 2) := by
  set M : ℝ := vasicekIntegratedMean r₀ θ κ (T : ℝ) with hM
  set V : ℝ := vasicekBondV κ (T : ℝ) with hV
  have hV_nonneg : (0 : ℝ) ≤ V := by
    rw [hV, ← vasicekIntegratedKernel_integral_sq hκ.ne' T]
    exact integral_nonneg fun u => sq_nonneg _
  have hInt : (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      (vasicekIntegratedKernelLp hκ T u) ^ 2 ∂volume) = V := by
    rw [hV, show (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekIntegratedKernelLp hκ T u) ^ 2 ∂volume)
          = ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekIntegratedKernel κ T u) ^ 2 ∂volume by
        refine integral_congr_ae ?_
        filter_upwards [(vasicekIntegratedKernel_memLp hκ T).coeFn_toLp] with u hu
        rw [vasicekIntegratedKernelLp, hu]]
    exact vasicekIntegratedKernel_integral_sq hκ.ne' T
  have hW : HasLaw (fun ω => wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω)
      (gaussianReal 0 V.toNNReal) μ := by
    have h0 := wienerIntegralLp_hasLaw_gaussian hB T (vasicekIntegratedKernelLp hκ T)
    rwa [hInt] at h0
  -- Factor the integrand: exp(−(M + σW)) = exp(−M)·exp((−σ)·W).
  have hfactor : ∀ ω, Real.exp (-(vasicekIntegratedRate hB r₀ θ σ hκ T ω))
      = Real.exp (-M) * Real.exp ((-σ) *
          (wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω)) := by
    intro ω
    rw [vasicekIntegratedRate, ← hM, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hfactor]
  rw [integral_const_mul,
    show (fun ω => Real.exp ((-σ) * (wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω)))
        = (fun x => Real.exp ((-σ) * x))
          ∘ (fun ω => wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω) from rfl,
    hW.integral_comp (by fun_prop : AEStronglyMeasurable (fun x => Real.exp ((-σ) * x))
      (gaussianReal 0 V.toNNReal)),
    integral_exp_mul_gaussianReal_zero (-σ) V.toNNReal,
    Real.coe_toNNReal _ hV_nonneg, ← Real.exp_add]
  congr 1
  ring

/-- The Vasicek affine coefficient `A(T) = exp(−θ(T − B(T)) + σ²V(T)/2)`, so that
the bond price factors as `P(0,T) = A(T)·exp(−B(T)·r₀)`. -/
noncomputable def vasicekBondA (θ σ κ T : ℝ) : ℝ :=
  Real.exp (-(θ * (T - vasicekBondB κ T)) + σ ^ 2 * vasicekBondV κ T / 2)

/-- **The affine term structure**: the Vasicek bond price separates the initial
short rate into `P(0,T) = A(T)·exp(−B(T)·r₀)` — the defining shape of an affine
term-structure model, the exponential-affine dependence on `r₀`. -/
theorem vasicekBondPrice_affine (hB : IsPreBrownianReal B μ)
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(vasicekIntegratedRate hB r₀ θ σ hκ T ω)) ∂μ
      = vasicekBondA θ σ κ (T : ℝ) * Real.exp (-(vasicekBondB κ (T : ℝ) * r₀)) := by
  rw [vasicekBondPrice_eq hB r₀ θ σ hκ T, vasicekBondA, vasicekIntegratedMean, ← Real.exp_add]
  congr 1
  ring

end MathFin
