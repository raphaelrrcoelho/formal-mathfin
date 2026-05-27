/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.FixedIncome.Credit
import QuantFin.Foundations.ExponentialDiscount

/-!
# Time-varying hazard credit curve

Extension of `Credit.lean` to a deterministic time-varying hazard `h : ℝ → ℝ`.
The cumulative hazard is `H(t) = ∫₀^t h(u) du` and survival is

  `S(t) = exp(-H(t))`.

When `h` is constant we recover the constant-hazard model. When `h` is
integrable the term-structure of credit spreads is the time-averaged hazard:

  `c(T) = -log(S(T)) / T = H(T) / T = (1/T) · ∫₀^T h(u) du`.

Results:

* `cumHazard`: `∫₀^t h(u) du`.
* `hazardSurvival`: `exp(-cumHazard h t)`.
* `hazardSurvival_at_zero`: `S(0) = 1`.
* `hazardSurvival_pos`: positive.
* `cumHazard_const`: `H(t) = h₀ · t` for constant `h`.
* `hazardSurvival_eq_const_survival`: matches `survivalProbability` for
  constant `h`.
* `creditSpread_eq_time_avg_hazard`: `c(T) = H(T) / T`.
-/

namespace QuantFin

open Real MeasureTheory intervalIntegral

/-- Cumulative hazard `H(t) = ∫₀^t h(u) du` for a deterministic hazard
function `h`. -/
noncomputable def cumHazard (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  cumulativeIntensity h t

/-- Survival probability with time-varying hazard `S(t) = exp(-H(t))` — the credit
instance of the shared `survivalFromIntensity` (`Foundations/ExponentialDiscount`).
The same calculus as `Actuarial.survivalFromForce`. -/
noncomputable def hazardSurvival (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  survivalFromIntensity h t

/-- `S(0) = 1`. -/
lemma hazardSurvival_at_zero (h : ℝ → ℝ) : hazardSurvival h 0 = 1 := by
  unfold hazardSurvival survivalFromIntensity cumulativeIntensity
  rw [integral_same, neg_zero, Real.exp_zero]

/-- Hazard survival is strictly positive (an instance of the
`ExponentialDiscount` principle `discount_pos`; holds regardless of hazard
sign / integrability). -/
lemma hazardSurvival_pos (h : ℝ → ℝ) (t : ℝ) : 0 < hazardSurvival h t :=
  discount_pos _

/-- **Hazard intensity as the negative log-derivative of survival** — the
recovery direction `h(t) = −d/dt log S(t)`. For continuous `h`, the
cumulative hazard `H(t) = ∫₀^t h` has derivative `h(t)` by the FTC, and the
`ExponentialDiscount` principle `rate_eq_neg_log_deriv` gives the
log-derivative form against `S = hazardSurvival h`. Mirrors
`force_eq_neg_log_deriv_survival` in `Actuarial/Mortality.lean` — the credit
and actuarial recoveries are the same identity. -/
theorem hazard_eq_neg_log_deriv_survival {h : ℝ → ℝ} (t : ℝ)
    (hh : Continuous h) :
    HasDerivAt (fun s => -(Real.log (hazardSurvival h s))) (h t) t := by
  have hH : HasDerivAt (cumHazard h) (h t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hh.intervalIntegrable 0 t)
      (hh.stronglyMeasurableAtFilter _ _)
      hh.continuousAt
  simpa only [hazardSurvival, survivalFromIntensity, cumHazard] using rate_eq_neg_log_deriv hH

/-- For a constant hazard `h_0`, `H(t) = h_0 · t`. -/
lemma cumHazard_const (h_0 t : ℝ) :
    cumHazard (fun _ => h_0) t = h_0 * t := by
  unfold cumHazard cumulativeIntensity
  rw [intervalIntegral.integral_const]
  simp [mul_comm]

/-- The time-varying model collapses to the constant-hazard `survivalProbability`
under `t = 0` and constant hazard. -/
lemma hazardSurvival_eq_const_survival (h_0 T : ℝ) :
    hazardSurvival (fun _ => h_0) T = survivalProbability h_0 0 T := by
  unfold hazardSurvival survivalFromIntensity survivalProbability
  rw [show cumulativeIntensity (fun _ => h_0) T = h_0 * T from cumHazard_const h_0 T]
  congr 1; ring

/-- **Credit spread as time-averaged hazard**: for `T > 0`,
`c(T) = -log(S(T)) / T = H(T) / T = (1/T) · ∫₀^T h(u) du`. -/
lemma creditSpread_eq_time_avg_hazard {h : ℝ → ℝ} {T : ℝ} (_hT : 0 < T) :
    -Real.log (hazardSurvival h T) / T = cumHazard h T / T := by
  unfold hazardSurvival survivalFromIntensity cumHazard
  rw [Real.log_exp, neg_neg]

end QuantFin
