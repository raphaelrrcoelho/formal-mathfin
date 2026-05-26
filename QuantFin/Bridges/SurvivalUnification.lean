/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.Actuarial.Mortality
import QuantFin.FixedIncome.HazardCurve

/-!
# Survival unification bridge — actuarial mortality ≡ credit hazard

The actuarial survival function from a force of mortality and the credit survival
function from a hazard rate are the **same object**: both are `exp(−∫₀ᵗ ·)`. Mortality,
credit hazard, and exponential discounting are three faces of one calculus
(Jarrow–Turnbull 1995 imported survival analysis into credit risk). This is known
finance; the artifact is the machine-checked cross-domain identity.

* `survivalFromForce_eq_hazardSurvival` — the two survival functions coincide.
* `gompertz_cumHazard` — a Gompertz-shaped intensity as a credit hazard curve, reusing
  the actuarial `gompertz_cumulative_force`.
-/

namespace QuantFin

/-- **Survival unification.** The actuarial `survivalFromForce` (from a force of mortality)
and the credit `hazardSurvival` (from a hazard rate) coincide — both unfold to
`exp(−∫₀ᵗ ·)`. -/
theorem survivalFromForce_eq_hazardSurvival (μ : ℝ → ℝ) (t : ℝ) :
    survivalFromForce μ t = hazardSurvival μ t := rfl

/-- **Gompertz law as a credit hazard curve.** A Gompertz-shaped intensity
`h(u) = B·e^{c·u}` has cumulative hazard `(B/c)·(e^{c·t} − 1)` — the same closed form as
the actuarial cumulative force of mortality. -/
theorem gompertz_cumHazard (B c t : ℝ) (hc : c ≠ 0) :
    cumHazard (fun u => B * Real.exp (c * u)) t = (B / c) * (Real.exp (c * t) - 1) := by
  unfold cumHazard
  exact gompertz_cumulative_force B c t hc

end QuantFin
