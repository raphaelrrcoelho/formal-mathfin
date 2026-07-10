/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.SDEExistence
public import MathFin.Foundations.DriftProcessModification

/-! # The strong solution as a pathwise process (SDE existence, the pathwise bridge)

`SDEExistence` produced the strong solution of `dX = b(X)dt + σ(X)dB` as the **abstract**
fixed point `picardSolution ∈ E = Lp ℝ 2 (trimMeasure_T T)` of the Picard map
`Φ(X) = η + driftProcessAssembled(b∘X) + itoProcessAssembled(σ∘X)`. That fixed point is an
`L²` equivalence class on the space–time product; on its own it is not yet a *pathwise* object.

This file slices the fixed-point equation `X = Φ(X)` — which holds in `E` — into a genuine
**pathwise decomposition** of the solution's sample paths:
`X_t(ω) = η(ω) + (drift limit)_t(ω) + (Itô modification)_t(ω)` for almost every `(t, ω)`.

The two analytic terms become honest pathwise processes:
* the **drift** `driftProcessAssembled(b∘X)` — an abstract `extendOfNorm` operator — has `coeFn`
  a.e. equal to the pointwise `limUnder` process `driftContinuousMod(b∘X)`
  (`driftProcessAssembled_coeFn`, the pathwise-realization crux of `DriftProcessModification`),
  itself the a.e. limit of the honest elementary Lebesgue integrals `∫₀ᵗ b(Xⁿ_s) ds`;
* the **Itô** `itoProcessAssembled(σ∘X)` is *by construction* the continuous modification
  `itoContinuousMod(σ∘X)` (`ItoProcessPredictable`), the pathwise `(σ∘X) ● B`.

So the `E`-fixed point genuinely *is* a pathwise strong solution: `sde_pathwise_decomposition`.

The remaining refinement — rewriting `driftContinuousMod(b∘X)_t(ω)` as the single Lebesgue integral
`∫₀ᵗ b(X_s(ω)) ds` (a per-`ω` interval Cauchy–Schwarz limit of `driftSimpleProcess_eq_setIntegral`)
— is a presentational upgrade of the drift term, not a strengthening of the existence statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace SDEExistence
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral
  ItoIntegralProcessContinuousModification

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- **The strong solution as a pathwise process (the pathwise bridge).** The abstract `E`-fixed point
`picardSolution` decomposes, almost everywhere on the space–time product, into its initial condition,
a pathwise drift, and a pathwise Itô term:
`X_t(ω) = η(ω) + driftContinuousMod(b∘X)_t(ω) + itoContinuousMod(σ∘X)_t(ω)`.
Both analytic terms are genuine pathwise objects — the drift is the a.e. limit of the honest elementary
Lebesgue integrals `∫₀ᵗ b(Xⁿ_s) ds` (`driftProcessAssembled_coeFn`), the Itô term is the continuous
modification `(σ∘X) ● B` (`itoProcessAssembled` is *defined* from `itoContinuousMod`). The fixed-point
equation `X = Φ(X)` holds in `E`; taking `coeFn` through `Lp.coeFn_add` and the two realization
identities slices it into this pathwise form. -/
theorem sde_pathwise_decomposition (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hc : (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ < 1) :
    ⇑(picardSolution hB T hBmeas hBcont hb hσ η_E hc)
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
      fun z ↦ ⇑η_E z
        + Function.uncurry (driftContinuousMod T hBmeas
            (lipComp T hBmeas b Lb hb (picardSolution hB T hBmeas hBcont hb hσ η_E hc))) z
        + Function.uncurry (itoContinuousMod T hBmeas
            (lipComp T hBmeas σ Lσ hσ (picardSolution hB T hBmeas hBcont hb hσ η_E hc))) z := by
  set X := picardSolution hB T hBmeas hBcont hb hσ η_E hc with hXdef
  -- X is a fixed point of the Picard map, which is definitionally the sum of the three terms
  have hfix : picardMap hB T hBmeas hBcont hb hσ η_E X = X :=
    (picardMap_contractingWith hB T hBmeas hBcont hb hσ η_E hc).fixedPoint_isFixedPt
  have hX : X = η_E + driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb X)
                    + itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ X) :=
    hfix.symm
  -- the two pathwise-realization identities
  have hdrift := driftProcessAssembled_coeFn (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb X)
  have hito : ⇑(itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ X))
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
        Function.uncurry (itoContinuousMod T hBmeas (lipComp T hBmeas σ Lσ hσ X)) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ X)).coeFn_toLp
  -- slice the fixed-point equation through coeFn (rewrite only the standalone ⇑X, not the X in lipComp)
  filter_upwards [Lp.coeFn_add
      (η_E + driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb X))
      (itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ X)),
    Lp.coeFn_add η_E (driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb X)),
    hdrift, hito] with z h1 h2 hd hi
  conv_lhs => rw [hX]
  simp only [h1, h2, hd, hi, Pi.add_apply]

/-- **The pathwise solution's drift term is the honest Lebesgue integral.** For every `t ≤ T`, the drift
term `driftContinuousMod(b∘X)` of `sde_pathwise_decomposition` is, almost surely, the genuine time
integral `∫₀ᵗ (b∘X)_s(ω) ds` — `driftContinuousMod_eq_setIntegral` applied to the coefficient
composition `b∘X = lipComp b X`. This closes the honest-remainder gap: the drift term of the strong
solution is not merely an abstract limit but the recognizable SDE integral `∫₀ᵗ b(X_s(ω)) ds`. -/
theorem sde_pathwise_drift_eq_setIntegral (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hc : (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ < 1) {t : ℝ≥0} (ht : t ≤ T) :
    ∀ᵐ ω ∂μ, driftContinuousMod T hBmeas
        (lipComp T hBmeas b Lb hb (picardSolution hB T hBmeas hBcont hb hσ η_E hc)) t ω
      = ∫ s in Set.Ioc (0 : ℝ≥0) t,
        ⇑(lipComp T hBmeas b Lb hb (picardSolution hB T hBmeas hBcont hb hσ η_E hc)) (s, ω) ∂timeMeasure :=
  driftContinuousMod_eq_setIntegral T hBmeas _ ht

end SDEExistence
end MathFin
