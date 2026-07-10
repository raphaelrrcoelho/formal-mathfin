/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import BrownianMotion.Gaussian.BrownianMotion
public import MathFin.Foundations.WienerIntegralIndicator

/-!
# The geometric-average Asian option: the two-date effective variance

`BlackScholes/AsianInequality.lean` bounds the geometric-average Asian payoff above by the
arithmetic one (AM–GM). This file supplies the distributional content that turns the
geometric average into a *priceable* lognormal: for a Black–Scholes GBM
`S_u = S₀·exp((r − σ²/2)u + σ B_u)` sampled at two dates `s ≤ t`, the geometric average
`√(S_s·S_t)` is lognormal, because its log-driver — the **average of the Brownian values**
`(B_s + B_t)/2` — is Gaussian with the covariance-sum variance

  `Var((B_s + B_t)/2) = (s + 2·min(s,t) + t)/4 = (3s + t)/4`   (for `s ≤ t`).

The derivation reads the average of Brownian values as a single **Wiener integral of a
deterministic step kernel**: `(B_s + B_t)/2 = ∫ ½(𝟙_{(0,s]} + 𝟙_{(0,t]}) dB` (using
`wienerIntegralLp_stepIndicator`, `∫𝟙_{(0,u]} dB = B_u`), so
`Foundations/WienerIntegralGaussian.wienerIntegralLp_hasLaw_gaussian` gives it a centred
Gaussian law whose variance is the `L²`-norm of the kernel — evaluated on the Ω-side through
the Brownian covariance `∫ B_s·B_t = min(s,t)` (`integral_mul_eval`). This is the same
"sum of Brownian values as a Wiener integral of a step kernel" route the Vasicek bond price
takes for the *integrated* rate; here the kernel is a sum of indicators rather than the
integrated OU exponential.

## Main results

* `asianGeom_driver_hasLaw` — `(B_s + B_t)/2 ~ N(0, (3s+t)/4)` for `s ≤ t`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **Zero start**: `B_0 = 0` a.s., since `∫ (B_0)² = min(0,0) = 0`. -/
private lemma brownian_start_zero (hB : IsPreBrownianReal B μ) : B 0 =ᵐ[μ] 0 := by
  have hmem : MemLp (B 0) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval 0).memLp_two
  have hint : Integrable (fun ω ↦ B 0 ω * B 0 ω) μ := hmem.integrable_mul hmem
  have hsq : ∫ ω, B 0 ω * B 0 ω ∂μ = 0 := by
    rw [integral_mul_eval hB 0 0]; simp
  have h0 : (fun ω ↦ B 0 ω * B 0 ω) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω ↦ mul_self_nonneg _) hint).mp hsq
  filter_upwards [h0] with ω hω
  exact mul_self_eq_zero.mp hω

/-- **The two-date geometric-Asian log-driver is Gaussian.** For a pre-Brownian motion `B`
and sampling dates `s ≤ t ≤ T`, the average of the Brownian values `(B_s + B_t)/2` — the
Gaussian part of the log geometric average `log √(S_s·S_t)` — has the centred Gaussian law
`N(0, (3s+t)/4)`, the variance coming from the Brownian covariance `∫ B_s·B_t = min(s,t)`. -/
theorem asianGeom_driver_hasLaw (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) (hsT : s ≤ T) (htT : t ≤ T) :
    HasLaw (fun ω ↦ (B s ω + B t ω) / 2)
      (gaussianReal 0 ((3 * (s : ℝ) + t) / 4).toNNReal) μ := by
  -- The two step indices `(0, s]` and `(0, t]`, and the kernel `f = ½·𝟙_{(0,s]} + ½·𝟙_{(0,t]}`.
  set is : StepIndex T := ⟨(0, s), ⟨zero_le, hsT⟩⟩
  set it : StepIndex T := ⟨(0, t), ⟨zero_le, htT⟩⟩
  set f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
    (1 / 2 : ℝ) • stepIndicatorLp T is + (1 / 2 : ℝ) • stepIndicatorLp T it with hf
  -- Its Wiener integral is `½·wInc(0,s] + ½·wInc(0,t]`.
  have hf_eq : wienerIntegralLp B hB T f
      = (1 / 2 : ℝ) • wienerIncrementLp B hB is + (1 / 2 : ℝ) • wienerIncrementLp B hB it := by
    rw [hf, map_add, map_smul, map_smul, wienerIntegralLp_stepIndicator,
      wienerIntegralLp_stepIndicator]
  -- The increment `coeFn`s: `wInc(0,u] = B_u − B_0` a.e.
  have e1 : (wienerIncrementLp B hB is : Ω → ℝ) =ᵐ[μ] fun ω ↦ B s ω - B 0 ω :=
    (memLp_increment_two hB is).coeFn_toLp
  have e2 : (wienerIncrementLp B hB it : Ω → ℝ) =ᵐ[μ] fun ω ↦ B t ω - B 0 ω :=
    (memLp_increment_two hB it).coeFn_toLp
  -- The Wiener integral's `coeFn` is `½(B_s − B_0) + ½(B_t − B_0)` a.e.
  have hcoe : (fun ω ↦ wienerIntegralLp B hB T f ω)
      =ᵐ[μ] fun ω ↦ (1 / 2 : ℝ) * (B s ω - B 0 ω) + (1 / 2 : ℝ) * (B t ω - B 0 ω) := by
    rw [hf_eq]
    have ha := Lp.coeFn_add ((1 / 2 : ℝ) • wienerIncrementLp B hB is)
      ((1 / 2 : ℝ) • wienerIncrementLp B hB it)
    have hcs := Lp.coeFn_smul (1 / 2 : ℝ) (wienerIncrementLp B hB is)
    have hct := Lp.coeFn_smul (1 / 2 : ℝ) (wienerIncrementLp B hB it)
    filter_upwards [ha, hcs, hct, e1, e2] with ω ha hcs hct he1 he2
    rw [ha]
    simp only [Pi.add_apply, hcs, hct, Pi.smul_apply, smul_eq_mul, he1, he2]
  -- Which is `(B_s + B_t)/2` a.e. (zero start `B_0 = 0`).
  have hae : (fun ω ↦ wienerIntegralLp B hB T f ω) =ᵐ[μ] fun ω ↦ (B s ω + B t ω) / 2 := by
    filter_upwards [hcoe, brownian_start_zero hB] with ω hc hz
    simp only [Pi.zero_apply] at hz
    rw [hc, hz]; ring
  -- The variance `∫ f² = (3s+t)/4`, computed on the Ω-side via `∫ B_u·B_v = min(u,v)`.
  have hms : MemLp (B s) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hmt : MemLp (B t) 2 μ := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have i1 : Integrable (fun ω ↦ (1 / 4 : ℝ) * (B s ω * B s ω)) μ :=
    (hms.integrable_mul hms).const_mul _
  have i2 : Integrable (fun ω ↦ (1 / 2 : ℝ) * (B s ω * B t ω)) μ :=
    (hms.integrable_mul hmt).const_mul _
  have i3 : Integrable (fun ω ↦ (1 / 4 : ℝ) * (B t ω * B t ω)) μ :=
    (hmt.integrable_mul hmt).const_mul _
  have i12 : Integrable (fun ω ↦ (1 / 4 : ℝ) * (B s ω * B s ω)
      + (1 / 2 : ℝ) * (B s ω * B t ω)) μ := i1.add i2
  have hvar : (∫ x in Set.Ioc (0 : ℝ) (T : ℝ), (f x) ^ 2 ∂volume) = (3 * (s : ℝ) + t) / 4 := by
    rw [← wienerIntegralLp_integral_sq hB T f]
    have hsq_ae : (fun ω ↦ (wienerIntegralLp B hB T f ω) ^ 2)
        =ᵐ[μ] fun ω ↦ (1 / 4 : ℝ) * (B s ω * B s ω) + (1 / 2 : ℝ) * (B s ω * B t ω)
            + (1 / 4 : ℝ) * (B t ω * B t ω) := by
      filter_upwards [hae] with ω hω
      rw [hω]; ring
    rw [integral_congr_ae hsq_ae, integral_add i12 i3, integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_mul_eval hB s s, integral_mul_eval hB s t, integral_mul_eval hB t t]
    simp only [min_self, min_eq_left hst]
    ring
  -- Assemble the Gaussian law and transfer along the a.e. equality.
  have h0 := wienerIntegralLp_hasLaw_gaussian hB T f
  rw [hvar] at h0
  exact ⟨h0.aemeasurable.congr hae, (Measure.map_congr hae).symm.trans h0.map_eq⟩

end MathFin
