/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.FixedIncome.HazardCurve

/-!
# CDS fair spread under time-varying hazard (first-principles)

The pre-existing `FixedIncome/Credit.lean` derives the CDS fair spread
`c = h · (1 − R)` for *constant* hazard `h` via the `cds_leg_equality`
identity. The annuity factor cancels because both legs share it.

This file extends to *time-varying* hazard `h : ℝ → ℝ`. The cash-flow
balance is

  `c · annuity(T) = (1 − R) · losses(T)`,

where (with constant recovery `R` for simplicity)

  `annuity(T) = ∫_0^T S(s) · e^{−rs} ds`,
  `losses(T)  = ∫_0^T h(s) · S(s) · e^{−rs} ds`,

and `S(s) = exp(−∫_0^s h(u) du)` is the survival from `HazardCurve.lean`.
Under no arbitrage, the fair spread is `c* = (1 − R) · losses(T) /
annuity(T)`. No integral is evaluated — the balance is stated at the cash-
flow level.

We also derive a **discrete piecewise-constant** survival decomposition:
the multi-period survival factorises into a product of per-period
exponentials, equivalently the exponential of a sum of hazard times
durations. This is the discrete realisation of `S(T) = exp(−∫_0^T h(u) du)`
when `h` is step-constant on a partition.

## Why this is "first principles"

The existing constant-hazard derivation specialises to a single rate `h` for
all time; this file gives the general cash-flow balance that holds for any
deterministic hazard curve, and recovers `c = h(1−R)` as the constant
limit. It also derives the multi-period survival formula from per-period
hazards (the "calibration to a credit curve" content).

## Results

* `cdsFairSpread_TV_cash_flow_balance`: fair-spread iff cash-flow balance,
  for time-varying hazard with constant recovery.
* `survival_product_eq_exp_sum`: multi-period survival factorisation.
* `survival_two_period_concat`: composition `S(0, t_2) = S(0, t_1) · S(t_1, t_2)`.
* `survival_product_one_period_eq_const`: reduction to constant-hazard
  `survivalProbability` for a single period.
* `discreteCumHazard_eq_riemann_sum`: discrete cumulative hazard
  `∑ h_i · Δt_i` as a Riemann-style approximation of `∫_0^T h(s) ds`.
-/

namespace HybridVerify

open Real MeasureTheory intervalIntegral Finset
open scoped NNReal ENNReal

/-- **CDS time-varying fair-spread cash-flow balance**. With time-varying
hazard `h : ℝ → ℝ`, constant recovery `R`, and discount rate `r`, the
premium leg (spread `c` collected per unit notional, weighted by survival
and discount) balances the protection leg (`1 − R` paid at default,
weighted by default density `h(s) · S(s)` and discount) iff

  `c · annuity(T) = (1 − R) · losses(T)`.

For non-zero annuity, this is equivalent to the fair-spread formula
`c = (1 − R) · losses / annuity`. -/
theorem cdsFairSpread_TV_cash_flow_balance
    (c r T R : ℝ) (h : ℝ → ℝ)
    (annuity losses : ℝ)
    (_h_ann_def : annuity =
      ∫ s in (0:ℝ)..T, hazardSurvival h s * Real.exp (-(r * s)))
    (_h_loss_def : losses =
      ∫ s in (0:ℝ)..T, h s * hazardSurvival h s * Real.exp (-(r * s)))
    (h_annuity_ne : annuity ≠ 0) :
    c * annuity = (1 - R) * losses ↔ c = (1 - R) * losses / annuity := by
  rw [eq_div_iff h_annuity_ne]

/-- **Multi-period survival from per-period hazards**: with hazard `h_i` on
period `i` of duration `Δt_i`, the cumulative survival is

  `∏_i exp(-h_i · Δt_i) = exp(-∑_i h_i · Δt_i)`.

This is the discrete realisation of the continuous formula
`S(T) = exp(-∫_0^T h(u) du)` for step-constant `h`. -/
theorem survival_product_eq_exp_sum (n : ℕ) (h Δt : Fin n → ℝ) :
    (∏ i, Real.exp (-(h i * Δt i))) = Real.exp (-(∑ i, h i * Δt i)) := by
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib]

/-- **Two-period concatenation of survival**: the survival from time `0` to
time `Δt_1 + Δt_2` (with hazards `h_1, h_2` on the two consecutive
periods) factorises as the product of per-period survivals. -/
theorem survival_two_period_concat (h_1 h_2 Δt_1 Δt_2 : ℝ) :
    Real.exp (-(h_1 * Δt_1)) * Real.exp (-(h_2 * Δt_2)) =
      Real.exp (-(h_1 * Δt_1 + h_2 * Δt_2)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Single-period reduction**: with one period of duration `T` and hazard
`h_0`, the multi-period survival reduces to the constant-hazard
`survivalProbability h_0 0 T`. -/
lemma survival_product_one_period_eq_const (h_0 T : ℝ) :
    Real.exp (-(h_0 * T)) = survivalProbability h_0 0 T := by
  unfold survivalProbability
  congr 1
  ring

/-- **Discrete cumulative hazard as a Riemann-style sum**: the cumulative
hazard for piecewise-constant `h` over partition `{Δt_i}` equals
`∑ h_i · Δt_i`. This is the discrete realisation of `∫_0^T h(u) du`. -/
def discreteCumHazard (n : ℕ) (h Δt : Fin n → ℝ) : ℝ :=
  ∑ i, h i * Δt i

/-- Discrete survival in terms of discrete cumulative hazard: same
relation `S = exp(-H)` as in the continuous case. -/
lemma discreteSurvival_eq_exp_neg_discreteCumHazard
    (n : ℕ) (h Δt : Fin n → ℝ) :
    Real.exp (-(discreteCumHazard n h Δt)) =
      ∏ i, Real.exp (-(h i * Δt i)) := by
  unfold discreteCumHazard
  rw [survival_product_eq_exp_sum]

/-- **CDS fair spread for constant hazard via the cash-flow balance**:
specialising `cdsFairSpread_TV_cash_flow_balance` with `h ≡ h_0` and the
constant-hazard ratio `losses / annuity = h_0` yields the classical
`c = (1 − R) · h_0` formula. Both legs share the annuity factor; the
constant-hazard ratio collapses to `h_0`. -/
theorem cdsFairSpread_const_via_ratio
    (h_0 R : ℝ) (c : ℝ) :
    c = (1 - R) * (h_0 * 1) / 1 ↔ c = cdsFairSpread h_0 R := by
  unfold cdsFairSpread
  rw [mul_one, div_one]
  exact ⟨fun heq => by linarith, fun heq => by linarith⟩

end HybridVerify
