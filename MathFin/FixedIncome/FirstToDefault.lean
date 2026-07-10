/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.ExpMin
public import MathFin.FixedIncome.Credit

/-!
# First-to-default: the basket intensity is the sum of single-name intensities

In the reduced-form (intensity-based) credit model, each name `i` in a basket
defaults at an exponential time `τ_i ∼ Exp(rates i)` — the constant-hazard
survival law derived in `Foundations/PoissonInterarrival.lean` and assumed
calibrated per name. A *first-to-default* (FtD) instrument references the
basket's first default time `min_i τ_i`.

This file is the finance reading of `Foundations/ExpMin.minimum_survival`
(minimum of jointly independent exponentials is exponential at the summed
rate): it rewrites that probability statement in the credit vocabulary of
`FixedIncome/Credit.lean` and draws the desk-level consequence.

* `firstToDefault_survival` — the basket survival probability *is*
  `survivalProbability (∑ i, rates i) 0 t`: the FtD time has constant hazard
  `∑ rates`, i.e. **basket intensity = sum of single-name intensities**
  (under independence).
* `firstToDefault_spread_eq_sum_hazards` — consequently the FtD credit
  spread, read directly off the measure of the survival event, equals
  `∑ i, rates i`. Since single-name spreads equal single-name hazards
  (`creditSpread_eq_hazard`), the fair FtD spread is the *sum of the
  single-name spreads* — and with a common recovery `R` both sides scale by
  `(1 − R)` (`cdsFairSpread`), so FtD CDS premia are additive across
  independent names. Independence is the extremal case: default correlation
  only lowers the FtD spread below this sum.

The probabilistic content (joint independence → product of survivals →
exponential at the summed rate) lives upstream in `ExpMin.lean`; this file
deliberately adds *no* new measure theory, only the load-bearing bridge from
that law to the credit-pricing layer.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {n : ℕ} {rates : Fin n → ℝ} {τ : Fin n → Ω → ℝ}

/-- **First-to-default survival law.** For jointly independent exponential
default times `τ_i ∼ Exp(rates i)`, the probability that no name has
defaulted by `t` is the constant-hazard survival probability at the summed
intensity: `P(min_i τ_i > t) = survivalProbability (∑ i, rates i) 0 t`. -/
theorem firstToDefault_survival
    (hrates_pos : ∀ i, 0 < rates i)
    (hexp_law : ∀ i, Measure.map (τ i) μ = expMeasure (rates i))
    (hindep : iIndepFun τ μ)
    (hmeas : ∀ i, Measurable (τ i))
    (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      (fun i : Fin n ↦ τ i ω)} =
        ENNReal.ofReal (survivalProbability (∑ i, rates i) 0 t) := by
  rw [minimum_survival hrates_pos hexp_law hindep hmeas hn ht]
  unfold survivalProbability
  rw [sub_zero]

/-- **First-to-default spread additivity.** The FtD credit spread — read
directly off the measure of the basket survival event — equals the sum of
the single-name hazard rates. By `creditSpread_eq_hazard` each summand is
the corresponding single-name spread, so under independence the fair
first-to-default spread is the sum of the single-name spreads. -/
theorem firstToDefault_spread_eq_sum_hazards
    (hrates_pos : ∀ i, 0 < rates i)
    (hexp_law : ∀ i, Measure.map (τ i) μ = expMeasure (rates i))
    (hindep : iIndepFun τ μ)
    (hmeas : ∀ i, Measurable (τ i))
    (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    -Real.log ((μ {ω | t < Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (fun i : Fin n ↦ τ i ω)}).toReal) / t
      = ∑ i, rates i := by
  rw [firstToDefault_survival hrates_pos hexp_law hindep hmeas hn ht.le,
    ENNReal.toReal_ofReal (survival_pos _ _ _).le]
  simpa [sub_zero] using
    creditSpread_eq_hazard (h := ∑ i, rates i) (t := 0) (T := t) ht

end MathFin
