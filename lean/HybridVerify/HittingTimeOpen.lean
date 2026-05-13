/-
  HybridVerify.HittingTimeOpen
  Proposition 4.3.6: hitting time of an open set by a continuous adapted
  process is a stopping time.
-/
import Mathlib
import BrownianMotion.Choquet.Debut

namespace HybridVerify

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Hypotheses for Proposition 4.3.6.

    The continuous-time process is indexed by `ℝ≥0` (so we have `OrderBot`,
    `PolishSpace`, `BorelSpace`, etc. instances) and the filtration
    satisfies the *usual conditions* (`IsComplete P` + `IsRightContinuous`)
    required by Degenne's `isStoppingTime_hittingAfter'`. -/
structure HittingTimeOpenHyp
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) (A : Set ℝ)
    : Prop where
  is_open_A : IsOpen A
  continuous_paths : ∀ ω, Continuous fun t => X t ω
  strongly_adapted : StronglyAdapted 𝓕 X

/-- Proposition 4.3.6: for a continuous strongly-adapted process and an
    open set `A`, the hitting time `hittingAfter X A 0` is a stopping time.
    Wrap of Degenne `isStoppingTime_hittingAfter'` (Choquet/Debut.lean). -/
theorem HittingTimeOpenHyp.is_stopping_time
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete P] [𝓕.IsRightContinuous]
    {X : ℝ≥0 → Ω → ℝ} {A : Set ℝ}
    (h : HittingTimeOpenHyp P 𝓕 X A) :
    IsStoppingTime 𝓕 (hittingAfter X A 0) :=
  isStoppingTime_hittingAfter' P
    (h.strongly_adapted.progMeasurable_of_continuous h.continuous_paths)
    h.is_open_A.measurableSet 0

end HybridVerify
