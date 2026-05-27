/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Foundations.ExponentialDiscount

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

namespace QuantFin

open Real MeasureTheory intervalIntegral

/-- Cumulative force of mortality `∫₀^t μ(u) du` — the mortality instance of the
shared `cumulativeIntensity` (`Foundations/ExponentialDiscount`). -/
noncomputable def forceCumulative (μ : ℝ → ℝ) (t : ℝ) : ℝ :=
  cumulativeIntensity μ t

/-- Survival probability from the force of mortality `S(t) = exp(-∫₀^t μ(u) du)` —
the mortality instance of the shared `survivalFromIntensity`. -/
noncomputable def survivalFromForce (μ : ℝ → ℝ) (t : ℝ) : ℝ :=
  survivalFromIntensity μ t

/-- `S(0) = 1` (no mortality before age `0`). -/
lemma survivalFromForce_at_zero (μ : ℝ → ℝ) :
    survivalFromForce μ 0 = 1 := by
  unfold survivalFromForce survivalFromIntensity cumulativeIntensity
  rw [integral_same, neg_zero, Real.exp_zero]

/-- Survival is strictly positive (an instance of the `ExponentialDiscount`
principle `discount_pos`). -/
lemma survivalFromForce_pos (μ : ℝ → ℝ) (t : ℝ) :
    0 < survivalFromForce μ t := discount_pos _

/-- **Force of mortality as the negative log-derivative of survival** — the
recovery direction `μ(t) = −d/dt log S(t)` that the classical definition
`μ(t) = −S'(t)/S(t)` encodes. For continuous `μ`, the cumulative force
`H(t) = ∫₀^t μ` has derivative `μ(t)` by the FTC, and the
`ExponentialDiscount` principle `rate_eq_neg_log_deriv` then gives the
log-derivative form against `S = survivalFromForce μ`. -/
theorem force_eq_neg_log_deriv_survival {μ : ℝ → ℝ} (t : ℝ)
    (hμ : Continuous μ) :
    HasDerivAt (fun s => -(Real.log (survivalFromForce μ s))) (μ t) t := by
  have hH : HasDerivAt (forceCumulative μ) (μ t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hμ.intervalIntegrable 0 t)
      (hμ.stronglyMeasurableAtFilter _ _)
      hμ.continuousAt
  simpa only [survivalFromForce, survivalFromIntensity, forceCumulative] using
    rate_eq_neg_log_deriv hH

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
  simp [Real.exp_zero]
  ring

/-! ## Compound Poisson MGF (folded from `CompoundPoisson.lean`)

For `N ~ Poisson(λ)` with iid claim sizes `X_i` of MGF `M_X`, the compound
Poisson aggregate `S = ∑_{i=1}^N X_i` has MGF `exp(λ · (M_X(t) − 1))`.
The algebraic core is `e^{−λ} · e^{λ M} = e^{λ(M − 1)}`. The Lundberg
adjustment coefficient solves `λ · (M(R) − 1) − c · R = 0`. -/

/-- **Compound Poisson MGF algebraic core**: `e^{−λ} · e^{λ M} = e^{λ(M − 1)}`. -/
theorem compoundPoisson_mgf_identity (lam M : ℝ) :
    Real.exp (-lam) * Real.exp (lam * M) = Real.exp (lam * (M - 1)) := by
  rw [← Real.exp_add]
  congr 1; ring

/-- **Lundberg adjustment-coefficient equation**: `λ · (M(R) − 1) − c · R = 0`. -/
def isLundbergAdjustmentCoefficient (lam c R : ℝ) (M : ℝ → ℝ) : Prop :=
  lam * (M R - 1) - c * R = 0

/-- **Trivial root at zero**: `R = 0` always satisfies the adjustment equation
when `M 0 = 1` (which holds for any MGF). -/
theorem lundberg_zero_at_zero (lam c : ℝ) (M : ℝ → ℝ) (hM0 : M 0 = 1) :
    isLundbergAdjustmentCoefficient lam c 0 M := by
  unfold isLundbergAdjustmentCoefficient
  rw [hM0]
  ring

end QuantFin
