/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.ExchangeOption
public import MathFin.Foundations.GaussianGirsanov

/-!
# Grounding the Margrabe `BSCallHyp` from a joint two-GBM model

`margrabe_price_via_call` (in `ExchangeOption.lean`) prices the exchange option
by *assuming* `BSCallHyp Q (S¹₀/S²₀) 1 0 σ T Z` — the ratio `R = S¹/S²` is
risk-neutral lognormal at the effective volatility `σ`. This file **derives**
that hypothesis from a joint gaussian model of the two assets' drivers, exactly
as leap 1 (`GaussianGirsanov.lean`) derives the 1-D `BSCallHyp` for a single
asset. It is the Margrabe-analog of leap 1.

The key observation: `BSCallHyp` requires only that the ratio's *effective
driver* is standard normal. For a jointly-gaussian pair `(W₁, W₂)` of unit-
variance drivers with correlation `ρ`, the normalized log-spread driver

  `W := (σ₁·W₁ − σ₂·W₂) / σ_eff`,   `σ_eff² = σ₁² + σ₂² − 2ρσ₁σ₂`,

is `N(0,1)` — a linear combination of a gaussian vector, with variance pinned
to `1` by `margrabe_effective_variance` (covariance bilinearity). Once that
single effective driver is standard normal, leap 1's
`BSCallHyp.exists_of_physical` supplies the (numeraire-change) measure `Q` and
the hypothesis itself. So the two-asset grounding *reduces to* the one-asset
Girsanov, with the gaussian-vector reduction as the only new ingredient — this
is also what makes `Foundations/BivariateGaussian`'s machinery load-bearing.

## Main results

* `normalizedSpread_hasLaw_std` — the normalized log-spread driver
  `(σ₁W₁ − σ₂W₂)/σ_eff` is `N(0,1)` (bivariate → univariate reduction).
* `margrabe_bsCallHyp_of_gaussian` — there exists a probability measure `Q`
  (an explicit Esscher tilt — the numeraire change) and a standard-normal
  driver under which `BSCallHyp` holds for the ratio at the effective vol.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Bivariate → univariate reduction.** For a jointly-gaussian pair
`(W₁, W₂)` of standard-normal drivers with correlation `ρ`, the normalized
log-spread driver `(σ₁·W₁ − σ₂·W₂)/σ_eff` is standard normal, where
`σ_eff² = σ₁² + σ₂² − 2ρσ₁σ₂ > 0`. The variance is pinned to `1` by covariance
bilinearity (`margrabe_effective_variance`); gaussianity is preserved under the
linear map. -/
theorem normalizedSpread_hasLaw_std
    {W₁ W₂ : Ω → ℝ} {σ₁ σ₂ ρ σeff : ℝ}
    (hjoint : HasGaussianLaw (fun ω => (W₁ ω, W₂ ω)) P)
    (hW₁meas : Measurable W₁) (hW₂meas : Measurable W₂)
    (hW₁ : HasLaw W₁ (gaussianReal 0 1) P) (hW₂ : HasLaw W₂ (gaussianReal 0 1) P)
    (hcov : cov[W₁, W₂; P] = ρ) (hσeff : 0 < σeff)
    (hσeff_sq : σeff ^ 2 = σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂) :
    HasLaw (fun ω => (σ₁ * W₁ ω - σ₂ * W₂ ω) / σeff) (gaussianReal 0 1) P := by
  set W : Ω → ℝ := fun ω => (σ₁ * W₁ ω - σ₂ * W₂ ω) / σeff with hW_def
  have hWmeas : Measurable W := ((hW₁meas.const_mul σ₁).sub (hW₂meas.const_mul σ₂)).div_const _
  -- `W` is a continuous-linear image of the gaussian vector, hence gaussian.
  have hWgl : HasGaussianLaw W P := by
    let L : ℝ × ℝ →L[ℝ] ℝ :=
      (σeff⁻¹ • (σ₁ • ContinuousLinearMap.fst ℝ ℝ ℝ - σ₂ • ContinuousLinearMap.snd ℝ ℝ ℝ))
    have hcomp : W = L ∘ (fun ω => (W₁ ω, W₂ ω)) := by
      funext ω
      simp only [hW_def, L, FunLike.coe_smul, FunLike.coe_sub,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Function.comp_apply,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
    rw [hcomp]
    exact hjoint.map_of_measurable L L.continuous.measurable
  -- Mean zero and variance one.
  have hmem₁ : MemLp W₁ 2 P := (hW₁.hasGaussianLaw).memLp_two
  have hmem₂ : MemLp W₂ 2 P := (hW₂.hasGaussianLaw).memLp_two
  have hint₁ : Integrable W₁ P := hmem₁.integrable (by norm_num)
  have hint₂ : Integrable W₂ P := hmem₂.integrable (by norm_num)
  have hmean₁ : ∫ ω, W₁ ω ∂P = 0 := by rw [hW₁.integral_eq, integral_id_gaussianReal]
  have hmean₂ : ∫ ω, W₂ ω ∂P = 0 := by rw [hW₂.integral_eq, integral_id_gaussianReal]
  have hvar₁ : Var[W₁; P] = 1 := by rw [hW₁.variance_eq, variance_id_gaussianReal]; norm_num
  have hvar₂ : Var[W₂; P] = 1 := by rw [hW₂.variance_eq, variance_id_gaussianReal]; norm_num
  have hWmean : ∫ ω, W ω ∂P = 0 := by
    simp only [hW_def]
    rw [integral_div, integral_sub (hint₁.const_mul σ₁) (hint₂.const_mul σ₂),
        integral_const_mul, integral_const_mul, hmean₁, hmean₂]
    simp
  -- Var[W] = (1/σeff²)·Var[σ₁W₁ − σ₂W₂] = (1/σeff²)·σeff² = 1.
  have hmemL₁ : MemLp (fun ω => σ₁ * W₁ ω) 2 P := hmem₁.const_mul σ₁
  have hmemL₂ : MemLp (fun ω => σ₂ * W₂ ω) 2 P := hmem₂.const_mul σ₂
  have hvarspread : Var[fun ω => σ₁ * W₁ ω - σ₂ * W₂ ω; P] = σeff ^ 2 := by
    have hV₁ : Var[fun ω => σ₁ * W₁ ω; P] = σ₁ ^ 2 * 1 := by rw [variance_const_mul, hvar₁]
    have hV₂ : Var[fun ω => σ₂ * W₂ ω; P] = σ₂ ^ 2 * 1 := by rw [variance_const_mul, hvar₂]
    have hC : cov[fun ω => σ₁ * W₁ ω, fun ω => σ₂ * W₂ ω; P] = ρ * σ₁ * σ₂ * 1 := by
      rw [covariance_const_mul_left, covariance_const_mul_right, hcov]; ring
    have hv := margrabe_effective_variance (T := 1) hmemL₁ hmemL₂ hV₁ hV₂ hC
    rw [mul_one] at hv
    rw [hσeff_sq]
    exact hv
  have hWvar : Var[W; P] = 1 := by
    have hWeq : W = fun ω => σeff⁻¹ * (σ₁ * W₁ ω - σ₂ * W₂ ω) := by
      funext ω; simp only [hW_def]; rw [div_eq_inv_mul]
    rw [hWeq, variance_const_mul, hvarspread]
    field_simp
  -- Pin the law from gaussianity + (mean, variance).
  refine ⟨hWmeas.aemeasurable, ?_⟩
  have hg : IsGaussian (P.map W) := hWgl.isGaussian_map
  have hmap_mean : (P.map W)[id] = 0 := by
    rw [integral_map hWmeas.aemeasurable aestronglyMeasurable_id]
    simpa using hWmean
  have hmap_var : Var[id; P.map W] = 1 := by
    rw [variance_map aemeasurable_id hWmeas.aemeasurable]
    simpa using hWvar
  rw [hg.eq_gaussianReal (P.map W), hmap_mean, hmap_var, Real.toNNReal_one]

/-- **Margrabe `BSCallHyp` grounding** (the Margrabe-analog of leap 1). From a
joint gaussian model of the two unit-variance drivers `(W₁, W₂)` with
correlation `ρ`, there exists a probability measure `Q` (an explicit Esscher
tilt — the `S²`-numeraire change of measure) and a standard-normal driver `Z`
under which `BSCallHyp` holds for the ratio `S¹₀/S²₀` at strike `1`, zero rate,
and the effective volatility `σ_eff = √(σ₁² + σ₂² − 2ρσ₁σ₂)`.
`margrabe_price_of_gaussian` (below) composes this with `margrabe_price_via_call`
to price the exchange option with no assumed risk-neutral hypothesis. -/
theorem margrabe_bsCallHyp_of_gaussian
    {W₁ W₂ : Ω → ℝ} {σ₁ σ₂ ρ σeff S1 S2 T c : ℝ}
    (hjoint : HasGaussianLaw (fun ω => (W₁ ω, W₂ ω)) P)
    (hW₁meas : Measurable W₁) (hW₂meas : Measurable W₂)
    (hW₁ : HasLaw W₁ (gaussianReal 0 1) P) (hW₂ : HasLaw W₂ (gaussianReal 0 1) P)
    (hcov : cov[W₁, W₂; P] = ρ)
    (hS1 : 0 < S1) (hS2 : 0 < S2) (hσeff : 0 < σeff) (hT : 0 < T)
    (hσeff_sq : σeff ^ 2 = σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂) :
    ∃ (Q : Measure Ω) (hQ : IsProbabilityMeasure Q) (Z : Ω → ℝ),
      @BSCallHyp _ _ Q hQ (S1 / S2) 1 0 σeff T Z := by
  have hW : HasLaw (fun ω => (σ₁ * W₁ ω - σ₂ * W₂ ω) / σeff) (gaussianReal 0 1) P :=
    normalizedSpread_hasLaw_std hjoint hW₁meas hW₂meas hW₁ hW₂ hcov hσeff hσeff_sq
  have hWmeas : Measurable (fun ω => (σ₁ * W₁ ω - σ₂ * W₂ ω) / σeff) :=
    ((hW₁meas.const_mul σ₁).sub (hW₂meas.const_mul σ₂)).div_const _
  obtain ⟨Q, hQ, _, hbs⟩ :=
    BSCallHyp.exists_of_physical c (div_pos hS1 hS2) one_pos hσeff hT hWmeas hW
  exact ⟨Q, hQ, _, hbs⟩

/-- **End-to-end Margrabe price from a joint gaussian model** (no assumed
risk-neutral hypothesis). Composes `margrabe_bsCallHyp_of_gaussian` (which
*derives* the ratio's `BSCallHyp`) with `margrabe_price_via_call`. -/
theorem margrabe_price_of_gaussian
    {W₁ W₂ : Ω → ℝ} {σ₁ σ₂ ρ σeff S1 S2 T c : ℝ}
    (hjoint : HasGaussianLaw (fun ω => (W₁ ω, W₂ ω)) P)
    (hW₁meas : Measurable W₁) (hW₂meas : Measurable W₂)
    (hW₁ : HasLaw W₁ (gaussianReal 0 1) P) (hW₂ : HasLaw W₂ (gaussianReal 0 1) P)
    (hcov : cov[W₁, W₂; P] = ρ)
    (hS1 : 0 < S1) (hS2 : 0 < S2) (hσeff : 0 < σeff) (hT : 0 < T)
    (hσeff_sq : σeff ^ 2 = σ₁ ^ 2 + σ₂ ^ 2 - 2 * ρ * σ₁ * σ₂) :
    ∃ (Q : Measure Ω) (_ : IsProbabilityMeasure Q) (Z : Ω → ℝ),
      S2 * ∫ ω, max (bsTerminal (S1 / S2) 0 σeff T (Z ω) - 1) 0 ∂Q
        = margrabePrice S1 S2 σeff T := by
  obtain ⟨Q, hQ, Z, hbs⟩ :=
    margrabe_bsCallHyp_of_gaussian (c := c) hjoint hW₁meas hW₂meas hW₁ hW₂ hcov
      hS1 hS2 hσeff hT hσeff_sq
  haveI := hQ
  exact ⟨Q, hQ, Z, margrabe_price_via_call hS2 hbs⟩

end MathFin
