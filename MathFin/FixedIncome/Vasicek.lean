/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Vasicek mean-reversion (deterministic part)

The Vasicek short-rate SDE is `dr_t = κ(θ − r_t) dt + σ dW_t`. With `σ = 0`
the deterministic ODE `dr/dt = κ(θ − r)` has explicit solution

  `r(t) = θ + (r₀ − θ) · e^{−κt}`,

exhibiting exponential mean reversion to `θ` at rate `κ`. We verify two
properties at the level of real-valued calculus:

* the closed form satisfies the ODE;
* limiting value `r(∞) = θ` (asymptotic, via positivity of `κ`).

The full Vasicek model including the stochastic part — the SDE closed-form
`r_t ~ N(r_0 e^{−κt} + θ(1−e^{−κt}), σ²(1−e^{−2κt})/(2κ))` — is *stated* (in the
`BSCallHyp` terminal-distribution style) in `MathFin/FixedIncome/VasicekSDE.lean`.
There the variance `σ²(1−e^{−2κt})/(2κ)` is the L² norm that the simple-process
Itô isometry *would* assign to the deterministic integrand `e^{−κ(t−s)}`; the
SDE→distribution derivation itself is not yet formalized (it is gated on the
continuous Itô integral). This file covers only the deterministic
(mean-reversion ODE) part.

## The half-life

The Vasicek/OU mean-reversion has a characteristic *half-life*
`t_{1/2} = log 2 / κ`: the time at which the gap from the mean has closed
to half its initial value. Independent of `r₀` and `θ`; only the rate `κ`
matters. (Folded from the former `MeanReversionHalfLife.lean`.)

Results:

* `vasicekDeterministic`: definition `θ + (r₀ − θ) e^{−κt}`.
* `vasicekDeterministic_at_zero`: `r(0) = r₀`.
* `vasicekDeterministic_solves_ODE`: `dr/dt = κ(θ − r(t))`.
* `vasicekDeterministic_tendsto_mean`: `r(t) → θ` as `t → ∞` (for `κ > 0`).
* `meanReversionHalfLife`: `log 2 / κ`.
* `vasicekDeterministic_at_halfLife`: at `t = log 2 / κ`, the gap is half
  the initial gap.
-/

@[expose] public section

namespace MathFin

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
  convert h using 1 <;> first | rfl | ring | field_simp

/-- **Long-run mean reversion**: `r(t) → θ` as `t → ∞`, for `κ > 0`. The gap
`(r₀ − θ) e^{−κt}` decays exponentially: `κt → ∞`, so `e^{−κt} → 0`. -/
theorem vasicekDeterministic_tendsto_mean (r₀ θ κ : ℝ) (hκ : 0 < κ) :
    Filter.Tendsto (vasicekDeterministic r₀ θ κ) Filter.atTop (nhds θ) := by
  have h1 : Filter.Tendsto (fun t : ℝ => κ * t) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hκ Filter.tendsto_id
  have h2 : Filter.Tendsto (fun t : ℝ => Real.exp (-(κ * t)))
      Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  unfold vasicekDeterministic
  simpa using (h2.const_mul (r₀ - θ)).const_add θ

/-! ## Half-life (folded from `MeanReversionHalfLife.lean`) -/

/-- **Half-life** of mean-reverting decay at rate `κ`: the time at which the
gap from the long-run mean is half its initial value. Depends only on `κ`. -/
noncomputable def meanReversionHalfLife (κ : ℝ) : ℝ := Real.log 2 / κ

/-- **At the half-life**, the Vasicek deterministic trajectory has closed
exactly half the gap from `θ`: `r(t₁ₐ) − θ = (r₀ − θ) / 2`. -/
theorem vasicekDeterministic_at_halfLife (r₀ θ κ : ℝ) (hκ : 0 < κ) :
    vasicekDeterministic r₀ θ κ (meanReversionHalfLife κ) - θ =
      (r₀ - θ) / 2 := by
  unfold vasicekDeterministic meanReversionHalfLife
  have hκ_ne : κ ≠ 0 := hκ.ne'
  have h_inner : κ * (Real.log 2 / κ) = Real.log 2 := by field_simp
  have h_exp : Real.exp (-(κ * (Real.log 2 / κ))) = 1 / 2 := by
    rw [h_inner, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  rw [h_exp]
  ring

end MathFin
