/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Equivalent probability measure from a positive normalised density

A measurable, strictly-positive, `P`-integrable density `g` with `∫ g ∂P = 1` defines an
**equivalent probability measure** `P.withDensity (fun ω => ENNReal.ofReal (g ω))`: it is a
probability measure (total mass `∫ g = 1`) and mutually absolutely continuous with `P`
(`withDensity` is always `≪ P`, and `P ≪` it because the density is a.e. nonzero).

This is the change-of-measure ritual shared by the equivalent-martingale-measure constructions
in the one-period FTAP files (`FTAPOnePeriod.lean`, `FTAPOnePeriodVector.lean`): each builds its
fair density (a logistic Esscher weight, or a `(1+‖Y‖)⁻¹` tempering for the `L¹` reduction),
normalises it, and then needs exactly these three facts.
-/

@[expose] public section

namespace MathFin

open MeasureTheory

/-- A measurable, strictly-positive, `P`-integrable density `g` with `∫ g ∂P = 1` makes
`Q = P.withDensity (fun ω => ENNReal.ofReal (g ω))` a probability measure equivalent to `P`:
`IsProbabilityMeasure Q`, `Q ≪ P`, and `P ≪ Q`. -/
theorem isEquivProbMeasure_withDensity {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    {g : Ω → ℝ} (hmeas : Measurable g) (hpos : ∀ ω, 0 < g ω) (hint : Integrable g P)
    (hsum : ∫ ω, g ω ∂P = 1) :
    IsProbabilityMeasure (P.withDensity (fun ω => ENNReal.ofReal (g ω))) ∧
      P.withDensity (fun ω => ENNReal.ofReal (g ω)) ≪ P ∧
      P ≪ P.withDensity (fun ω => ENNReal.ofReal (g ω)) := by
  have hofReal_meas : Measurable (fun ω => ENNReal.ofReal (g ω)) :=
    ENNReal.measurable_ofReal.comp hmeas
  refine ⟨⟨?_⟩, withDensity_absolutelyContinuous _ _,
    withDensity_absolutelyContinuous' hofReal_meas.aemeasurable
      (Filter.Eventually.of_forall fun ω => ?_)⟩
  · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun ω => (hpos ω).le), hsum, ENNReal.ofReal_one]
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hpos ω

end MathFin
