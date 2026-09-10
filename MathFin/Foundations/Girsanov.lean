/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ChangeOfMeasure
public import MathFin.Foundations.BrownianMartingale

/-!
# Continuous-time Girsanov for Black–Scholes — the EMM as an explicit change of measure

The equivalent martingale measure of the Black–Scholes model, **constructed** as a
Girsanov density change of the physical measure — not recognised after the fact. Under
the physical measure `P` the stock has drift `μ`,
`S_t = S_0 · exp((μ − σ²/2)t + σ X_t)`, so the discounted price is
`D_t = e^{−rt} S_t = S_0 · exp((μ − r − σ²/2)t + σ X_t)`, a `P`-submartingale (drift
`μ − r ≠ 0`). Tilting by the **Girsanov density** with constant market price of risk
`θ = (μ − r)/σ`,

  `Z_t = exp(−θ X_t − ½θ² t)`   (the Wald exponential at `α = −θ`),
  `Q = P.withDensity Z_T`,

turns the discounted price into a `Q`-**martingale** on `[0, T]`: `Q` is the EMM.

The proof is the abstract Bayes engine `changeOfMeasure_setIntegral_eq` supplied with two
Wald exponentials — `Z` itself (`α = −θ`) and the product `Z · D = S_0 · exp((σ−θ)X_t −
½(σ−θ)² t)` (`α = σ − θ`, using `μ − r = σθ`), both `P`-martingales by
`IsFilteredPreBrownian.waldExponential_isMartingale`. The one genuinely new estimate is
the mixed-time integrability of `D_u · Z_T`: by AM–GM, `exp(σX_u)·exp(−θX_T) ≤
exp(2σX_u) + exp(−2θX_T)`, each a Gaussian-MGF term (`integrable_exp_mul_of_hasLaw`).

This wires the **I ↔ II seam** (pricing ↔ Itô/Brownian tower) on the martingale side:
the risk-neutral measure is an explicit density change of the physical one, retiring the
Wald shortcut of `discountedGBM_isMartingale` (which took `Q = P` from the start). The
*distributional* Girsanov (the drift-corrected `B^θ_t = B_t + ∫₀ᵗ θ_s ds` is a `Q`-Brownian
motion, `gir-thm-9.1.8`) is strictly stronger, and it now ships: `GirsanovConstantTheta`
for constant `θ`, `GirsanovAdaptedTheta` for bounded continuous adapted `θ`, and
`GirsanovPredictableTheta` for bounded predictable `θ` — all without an adapted-integrand
Itô formula, via the Bayes engine plus the characteristic-function characterization.

## Main result

* `MathFin.bs_discounted_isQMartingale`
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- **Black–Scholes EMM via Girsanov.** With physical drift `μ`, rate `r`, volatility
`σ ≠ 0`, and market price of risk `θ = (μ − r)/σ`, the discounted stock price
`D_t = S_0 · exp((μ − r − σ²/2)t + σ X_t)` is a martingale on `[0, T]` under the tilted
measure `Q = P.withDensity (exp(−θ X_T − ½θ² T))`: for `s ≤ t ≤ T` and `A ∈ 𝓕_s`, the
`Q`-integrals of `D_t` and `D_s` over `A` agree. `Q` is the equivalent martingale measure,
exhibited as an explicit Girsanov change of measure. -/
theorem bs_discounted_isQMartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (S_0 r μ σ : ℝ) (hσ : σ ≠ 0) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, (S_0 * Real.exp ((μ - r - σ ^ 2 / 2) * (t : ℝ) + σ * X t ω))
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal
          (Real.exp (-((μ - r) / σ) * X T ω - ((μ - r) / σ) ^ 2 * (T : ℝ) / 2)))
      = ∫ ω in A, (S_0 * Real.exp ((μ - r - σ ^ 2 / 2) * (s : ℝ) + σ * X s ω))
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal
          (Real.exp (-((μ - r) / σ) * X T ω - ((μ - r) / σ) ^ 2 * (T : ℝ) / 2))) := by
  set θ := (μ - r) / σ with hθdef
  set Z : ℝ≥0 → Ω → ℝ := fun u ω ↦ Real.exp (-θ * X u ω - θ ^ 2 * (u : ℝ) / 2) with hZdef
  set D : ℝ≥0 → Ω → ℝ := fun u ω ↦ S_0 * Real.exp ((μ - r - σ ^ 2 / 2) * (u : ℝ) + σ * X u ω)
    with hDdef
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦ ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  -- Density `Z_T` is measurable and nonnegative.
  have hZmeasT : Measurable (Z T) := by
    rw [hZdef]; exact Real.measurable_exp.comp (((hmeasX T).const_mul (-θ)).sub_const _)
  have hZpos : ∀ ω, 0 ≤ Z T ω := fun ω ↦ le_of_lt (Real.exp_pos _)
  -- `D` is adapted (continuous function of the adapted `X_u`).
  have hDsm : ∀ u, StronglyMeasurable[𝓕 u] (D u) := by
    intro u
    rw [hDdef]
    exact (Real.continuous_exp.comp_stronglyMeasurable
      (((hX.stronglyAdapted u).const_mul σ).const_add _)).const_mul S_0
  -- `Z` is a `P`-martingale: the Wald exponential at `α = −θ`.
  have hZ : Martingale Z 𝓕 P := by
    have key : Z = fun u ω ↦ Real.exp (-θ * X u ω - (-θ) ^ 2 * (u : ℝ) / 2) := by
      funext u ω; rw [hZdef, neg_sq]
    rw [key]; exact IsFilteredPreBrownian.waldExponential_isMartingale (-θ)
  -- `Z · D = S_0 · Wald(σ − θ)` is a `P`-martingale (uses `μ − r = σθ`).
  have hZD : Martingale (fun u ω ↦ Z u ω * D u ω) 𝓕 P := by
    have hθσ : σ * θ = μ - r := by rw [hθdef]; field_simp
    have key : (fun u ω ↦ Z u ω * D u ω)
        = S_0 • fun (u : ℝ≥0) ω ↦ Real.exp ((σ - θ) * X u ω - (σ - θ) ^ 2 * (u : ℝ) / 2) := by
      funext u ω
      simp only [hZdef, hDdef, Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      rw [show μ - r = σ * θ from hθσ.symm]; ring
    rw [key]; exact (IsFilteredPreBrownian.waldExponential_isMartingale (σ - θ)).smul S_0
  -- Mixed-time integrability of `D_u · Z_T` via AM–GM.
  have hmix : ∀ u, u ≤ T → Integrable (fun ω ↦ D u ω * Z T ω) P := by
    intro u _
    simp only [hZdef, hDdef]
    have hcore : Integrable (fun ω ↦ Real.exp (σ * X u ω) * Real.exp (-θ * X T ω)) P := by
      have hbnd : Integrable
          (fun ω ↦ Real.exp (2 * σ * X u ω) + Real.exp (-2 * θ * X T ω)) P :=
        (integrable_exp_mul_of_hasLaw (hX.hasLaw_eval u) (2 * σ)).add
          (integrable_exp_mul_of_hasLaw (hX.hasLaw_eval T) (-2 * θ))
      refine Integrable.mono' hbnd ?_ ?_
      · exact ((Real.measurable_exp.comp ((hmeasX u).const_mul σ)).mul
          (Real.measurable_exp.comp ((hmeasX T).const_mul (-θ)))).aestronglyMeasurable
      · filter_upwards with ω
        rw [Real.norm_of_nonneg (by positivity)]
        have ea : Real.exp (2 * σ * X u ω) = Real.exp (σ * X u ω) ^ 2 := by
          rw [pow_two, ← Real.exp_add]; congr 1; ring
        have eb : Real.exp (-2 * θ * X T ω) = Real.exp (-θ * X T ω) ^ 2 := by
          rw [pow_two, ← Real.exp_add]; congr 1; ring
        rw [ea, eb]
        nlinarith [sq_nonneg (Real.exp (σ * X u ω) - Real.exp (-θ * X T ω)),
          (Real.exp_pos (σ * X u ω)).le, (Real.exp_pos (-θ * X T ω)).le,
          mul_pos (Real.exp_pos (σ * X u ω)) (Real.exp_pos (-θ * X T ω))]
    have hrw : (fun ω ↦
        (S_0 * Real.exp ((μ - r - σ ^ 2 / 2) * (u : ℝ) + σ * X u ω)) *
        Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
        = fun ω ↦ (S_0 * Real.exp ((μ - r - σ ^ 2 / 2) * (u : ℝ)) *
            Real.exp (-(θ ^ 2 * (T : ℝ) / 2))) *
            (Real.exp (σ * X u ω) * Real.exp (-θ * X T ω)) := by
      funext ω
      rw [Real.exp_add ((μ - r - σ ^ 2 / 2) * (u : ℝ)) (σ * X u ω),
        show -θ * X T ω - θ ^ 2 * (T : ℝ) / 2
          = (-θ * X T ω) + (-(θ ^ 2 * (T : ℝ) / 2)) from by ring, Real.exp_add]
      ring
    rw [hrw]; exact hcore.const_mul _
  exact changeOfMeasure_setIntegral_eq T hZmeasT hZpos hDsm hZ hZD hmix hst htT hA

end MathFin
