/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# The exponential-discount / cumulative-rate principle

Five apparently distinct quantities in this library share *one* structural
identity:

  *quantity*  =  `exp(−H(t))`,        where `H(t) = ∫₀^t rate(u) du`.

The instances:

| object                | rate `r(u)`                    | quantity                                      |
|-----------------------|--------------------------------|-----------------------------------------------|
| Zero-coupon bond      | risk-free rate `r`             | `P(t) = exp(−r·(T−t))`                        |
| Hazard credit         | hazard intensity `h`           | `S(t) = exp(−h·(T−t))`                        |
| Survival w/ curve     | hazard function `h(u)`         | `S(t) = exp(−∫₀^t h(u) du)`  (`HazardCurve`)  |
| Force of mortality    | force `μ(u)`                   | survival = `exp(−∫₀^t μ(u) du)` (`Mortality`) |
| Vasicek deterministic | drift toward `θ`               | `r(t) = θ + (r₀−θ)·exp(−κt)` (no integral)    |

## The dual identity: rate as negative-log-derivative

Given a *quantity* `Q(t) = exp(−H(t))`, the rate can be *recovered*:

  `−d/dt log Q(t) = d/dt H(t) = rate(t)`.

This is the conceptual content of every "rate from term-structure" formula:

* **Forward rate from spot rate**: `f(T) = −d/dT log P(T)` where
  `P(T) = exp(−T · R(T))`. (`ForwardRate.lean`)
* **Force of mortality from survival**: `μ(t) = −d/dt log S(t)`. (`Mortality.lean`)
* **Hazard intensity from survival**: `h(t) = −d/dt log S(t)`. (`HazardCurve.lean`)

The proof is one step: `log(exp(x)) = x` (Mathlib `Real.log_exp`). The
derivative-of-`H` hypothesis carries through unchanged. We record this
identity as `rate_eq_neg_log_deriv` below.

## Results

* `rate_eq_neg_log_deriv`: if `H` has derivative `H'(t)` at `t`, then
  `-d/dt log(exp(-H(t))) = H'(t)` at `t`. This is the universal
  "rate from quantity" recovery.
* `discount_pos`: `exp(-H) > 0` always (so all five discount/survival
  quantities are positive).
* `discount_strictAnti`: `H₁ < H₂ ⇒ exp(-H₂) < exp(-H₁)` (discounting
  decreases in cumulative rate).
-/

namespace QuantFin

open Real MeasureTheory intervalIntegral

/-- **The universal rate-recovery identity**: if `H` is differentiable at
`t` with derivative `H'`, then `−d/dt log(exp(−H(t))) = H'(t)` at `t`.

This is the conceptual reason `forward rate = −d/dT log P` (`ZCB`, `ForwardRate`),
`force of mortality = −d/dt log S` (`Mortality`), and `hazard = −d/dt log S`
(`HazardCurve`) are all *the same identity*: each computes the rate from
the discount/survival, the difference is only in what `H` represents.

The proof: `log(exp(−H s)) = −H s` (logs and exps are inverses), so
`−log(exp(−H s)) = H s`, and the derivative of the LHS equals `H'(t)` by
hypothesis. -/
theorem rate_eq_neg_log_deriv {H : ℝ → ℝ} {H' t : ℝ}
    (hH : HasDerivAt H H' t) :
    HasDerivAt (fun s => -(Real.log (Real.exp (-H s)))) H' t := by
  have h_eq : (fun s : ℝ => -(Real.log (Real.exp (-H s)))) = H := by
    funext s; rw [Real.log_exp, neg_neg]
  rw [h_eq]
  exact hH

/-- Universal discount/survival positivity: `0 < exp(−H)` for any `H`.

Underpins `survival_pos` (constant-hazard credit), `hazardSurvival_pos`
(time-varying hazard), `survivalFromForce_pos` (mortality), and the
implicit positivity of the BS discount factor `exp(−rT)`. -/
lemma discount_pos (H : ℝ) : 0 < Real.exp (-H) := Real.exp_pos _

/-- Universal discount monotonicity: `H₁ < H₂ ⇒ exp(−H₂) < exp(−H₁)`.

Underpins `survival_strictAnti_of_pos_hazard`, the strict ordering of ZCB
prices at distinct rates, and the strict-positive-correlation tightening
of variance bounds. -/
lemma discount_strictAnti {H₁ H₂ : ℝ} (h : H₁ < H₂) :
    Real.exp (-H₂) < Real.exp (-H₁) :=
  Real.exp_lt_exp.mpr (by linarith)

/-- **Cumulative intensity** `∫₀ᵗ r(u) du` — the domain-neutral cumulative of a
rate/intensity/force. The single definition that the actuarial cumulative force
(`Mortality.forceCumulative`) and the credit cumulative hazard
(`FixedIncome.HazardCurve.cumHazard`) share. -/
noncomputable def cumulativeIntensity (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, r u

/-- **Survival from an intensity** `S(t) = exp(−∫₀ᵗ r(u) du)` — the domain-neutral
survival function. The single definition shared by the actuarial survival
(`Mortality.survivalFromForce`) and the credit survival
(`FixedIncome.HazardCurve.hazardSurvival`): one calculus, two domains. -/
noncomputable def survivalFromIntensity (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(cumulativeIntensity r t))

end QuantFin
