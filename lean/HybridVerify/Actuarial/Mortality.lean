/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Force of mortality and survival functions

The classical actuarial setup. Let `S : ℝ → ℝ` denote a survival function
(`S(t) = P(T > t)` where `T` is the time of death). The **force of mortality**
at age `t` is

  `μ(t) := -S'(t) / S(t) = -d/dt log S(t)`,

so survival reconstructs from the force as

  `S(t) = exp(-∫₀^t μ(u) du)`.

Under a **Gompertz** mortality law `μ(t) = B · e^{c·t}`:

  `∫₀^t μ(u) du = (B/c) · (e^{c·t} - 1)`,

so `S(t) = exp(-(B/c)·(e^{c·t} - 1))`. The structural identity in this file is
the FTC connection between cumulative force and survival.

We mirror `FixedIncome/HazardCurve.lean` (which formalizes the same exponential
identity for credit hazard) — the actuarial and credit terminologies share the
same calculus.

Results:

* `forceCumulative`: `∫₀^t μ(u) du`.
* `survivalFromForce`: `S(t) := exp(-forceCumulative μ t)`.
* `survivalFromForce_at_zero`: `S(0) = 1`.
* `survivalFromForce_pos`: positivity.
* `gompertz_cumulative_force`: closed form `(B/c)·(e^{c·t} − 1)` for Gompertz.
-/

namespace HybridVerify

open Real MeasureTheory intervalIntegral

/-- Cumulative force of mortality `∫₀^t μ(u) du`. -/
noncomputable def forceCumulative (μ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, μ u

/-- Survival probability from the force of mortality:
`S(t) = exp(-∫₀^t μ(u) du)`. -/
noncomputable def survivalFromForce (μ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(forceCumulative μ t))

/-- `S(0) = 1` (no mortality before age `0`). -/
lemma survivalFromForce_at_zero (μ : ℝ → ℝ) :
    survivalFromForce μ 0 = 1 := by
  unfold survivalFromForce forceCumulative
  rw [integral_same, neg_zero, Real.exp_zero]

/-- Survival is strictly positive. -/
lemma survivalFromForce_pos (μ : ℝ → ℝ) (t : ℝ) :
    0 < survivalFromForce μ t := Real.exp_pos _

/-- **Gompertz cumulative force** in closed form:
`∫₀^t B · e^{c u} du = (B/c) · (e^{c t} − 1)` for `c ≠ 0`. -/
theorem gompertz_cumulative_force (B c t : ℝ) (hc : c ≠ 0) :
    ∫ u in (0:ℝ)..t, B * Real.exp (c * u) =
      (B / c) * (Real.exp (c * t) - 1) := by
  -- Antiderivative: (B/c) e^{c u}. Use FTC for HasDerivAt.
  have h_anti : ∀ u, HasDerivAt (fun u => (B / c) * Real.exp (c * u))
                      (B * Real.exp (c * u)) u := by
    intro u
    have h_cu : HasDerivAt (fun u : ℝ => c * u) c u := by
      have := (hasDerivAt_id u).const_mul c
      simpa using this
    have h_exp : HasDerivAt (fun u => Real.exp (c * u))
                  (Real.exp (c * u) * c) u := h_cu.exp
    have h := h_exp.const_mul (B / c)
    convert h using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => h_anti u)
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [Real.exp_zero, mul_comm]
  ring

end HybridVerify
