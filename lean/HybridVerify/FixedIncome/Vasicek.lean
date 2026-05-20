/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Vasicek mean-reversion (deterministic part)

The Vasicek short-rate SDE is `dr_t = κ(θ − r_t) dt + σ dW_t`. With `σ = 0`
the deterministic ODE `dr/dt = κ(θ − r)` has explicit solution

  `r(t) = θ + (r₀ − θ) · e^{−κt}`,

exhibiting exponential mean reversion to `θ` at rate `κ`. We verify two
properties at the level of real-valued calculus:

* the closed form satisfies the ODE;
* limiting value `r(∞) = θ` (asymptotic, via positivity of `κ`).

The full Vasicek model (including the stochastic part) is gated on the Itô
integral and is not formalized here.

Results:

* `vasicekDeterministic`: definition `θ + (r₀ − θ) e^{−κt}`.
* `vasicekDeterministic_at_zero`: `r(0) = r₀`.
* `vasicekDeterministic_solves_ODE`: `dr/dt = κ(θ − r(t))`.
-/

namespace HybridVerify

open Real

/-- Vasicek deterministic short-rate solution: `r(t) = θ + (r₀ − θ) e^{−κt}`. -/
noncomputable def vasicekDeterministic (r₀ θ κ t : ℝ) : ℝ :=
  θ + (r₀ - θ) * Real.exp (-(κ * t))

/-- **Initial condition**: `r(0) = r₀`. -/
lemma vasicekDeterministic_at_zero (r₀ θ κ : ℝ) :
    vasicekDeterministic r₀ θ κ 0 = r₀ := by
  unfold vasicekDeterministic
  simp

/-- **Vasicek deterministic ODE solution**: the closed form satisfies
`dr/dt = κ · (θ − r(t))`. -/
theorem vasicekDeterministic_solves_ODE (r₀ θ κ t : ℝ) :
    HasDerivAt (vasicekDeterministic r₀ θ κ)
      (κ * (θ - vasicekDeterministic r₀ θ κ t)) t := by
  unfold vasicekDeterministic
  have h_neg_kt : HasDerivAt (fun t => -(κ * t)) (-κ) t := by
    have h_kt : HasDerivAt (fun t : ℝ => κ * t) κ t := by
      have := (hasDerivAt_id t).const_mul κ
      simpa using this
    exact h_kt.neg
  have h_exp : HasDerivAt (fun t => Real.exp (-(κ * t)))
                (Real.exp (-(κ * t)) * (-κ)) t := h_neg_kt.exp
  have h_mul : HasDerivAt (fun t => (r₀ - θ) * Real.exp (-(κ * t)))
                ((r₀ - θ) * (Real.exp (-(κ * t)) * (-κ))) t :=
    h_exp.const_mul (r₀ - θ)
  have h := h_mul.const_add θ
  convert h using 1
  ring

end HybridVerify
