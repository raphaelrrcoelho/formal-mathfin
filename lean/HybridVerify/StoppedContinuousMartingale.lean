/-
  HybridVerify.StoppedContinuousMartingale
  Theorem 4.3.7: stopped continuous-time martingale is a martingale.
-/
import Mathlib
import BrownianMotion.StochasticIntegral.LocalMartingale

namespace HybridVerify

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Hypotheses for Theorem 4.3.7. -/
structure StoppedContinuousMartingaleHyp
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (M : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) : Prop where
  martingale : Martingale M 𝓕 P
  right_continuous_paths : ∀ ω, Function.IsRightContinuous (M · ω)
  stopping_time : IsStoppingTime 𝓕 τ

/-- Theorem 4.3.7 wrap of Degenne `Martingale.stoppedProcess_indicator`. -/
theorem StoppedContinuousMartingaleHyp.is_martingale
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (h : StoppedContinuousMartingaleHyp P 𝓕 M τ) :
    Martingale (stoppedProcess (fun i ↦ {ω | ⊥ < τ ω}.indicator (M i)) τ) 𝓕 P :=
  h.martingale.stoppedProcess_indicator h.right_continuous_paths h.stopping_time

end HybridVerify
