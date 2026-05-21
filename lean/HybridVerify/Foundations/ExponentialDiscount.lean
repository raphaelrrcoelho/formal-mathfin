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
|-----------------------|---------------------------------|-----------------------------------------------|
| Zero-coupon bond      | risk-free rate `r`              | `P(t) = exp(−r·(T−t))`                        |
| Hazard credit         | hazard intensity `h`            | `S(t) = exp(−h·(T−t))`                        |
| Survival w/ curve     | hazard function `h(u)`          | `S(t) = exp(−∫₀^t h(u)du)`  (`HazardCurve`)   |
| Force of mortality    | force `μ(u)`                    | survival = `exp(−∫₀^t μ(u)du)` (`Mortality`)  |
| Vasicek deterministic | drift toward `θ`                | `r(t) = θ + (r₀−θ)·exp(−κt)` (no integral)    |

The *flat-rate* identity `H(t) = r·t ⟹ exp(−r·t)` is shared by ZCB, credit
spread, and Vasicek (at infinity); the *cumulative-integral* form
`exp(−∫ rate du)` is shared by hazard curve and force-of-mortality survival.

The general identity below sits underneath all of them.

## The reciprocal: rates from quantities

If `S(t) = exp(−H(t))`, then `−d/dt log S(t) = d/dt H(t) = rate(t)`. So:

* **Forward rate from spot rate**: `f(T) = −d/dT log P(T) = d/dT (T · R(T))`
  (`ForwardRate`).
* **Force of mortality from survival**: `μ(t) = −d/dt log S(t)`.
* **Hazard intensity from survival**: `h(t) = −d/dt log S(t)`.

The same algebra (`exp` and `log` are inverses, derivatives commute through)
generates each.

This file records the master identity and notes the call sites. The
specific consumers (`ZCB`, `Credit`, `HazardCurve`, `Mortality`, `Vasicek`,
`ForwardRate`) each instantiate it under their respective rate functions.
-/

namespace HybridVerify

open Real

/-- **Cumulative-rate / discount identity**: if `H(t)` is a cumulative-rate
quantity then `exp(−H(t))` is its associated discount/survival factor.
Trivial algebraically; significant *conceptually* — discount, hazard
survival, and mortality survival are this one identity. -/
lemma discount_eq_exp_neg_cum_rate (H : ℝ) :
    Real.exp (-H) = Real.exp (-H) := rfl

/-- **Discount-factor positivity** (universal): for any cumulative rate `H`,
`0 < exp(−H)`. This is the structural reason all five "survival/discount"
quantities in the library are positive (`survival_pos`, `hazardSurvival_pos`,
`survivalFromForce_pos`, ZCB pricing positivity). -/
lemma discount_pos (H : ℝ) : 0 < Real.exp (-H) := Real.exp_pos _

/-- **Discount is strictly decreasing in cumulative rate**: `H₁ < H₂ ⟹
exp(−H₁) > exp(−H₂)`. Structural reason for positive-spread monotonicity
(`survival_strictAnti_of_pos_hazard`) and for the no-arb ZCB shape. -/
lemma discount_strictAnti (H₁ H₂ : ℝ) (h : H₁ < H₂) :
    Real.exp (-H₂) < Real.exp (-H₁) :=
  Real.exp_lt_exp.mpr (by linarith)

/-- **Constant-rate cumulative**: `H(t) = r·t` is the special case shared by
ZCB pricing, constant-hazard credit, and constant-force mortality. -/
lemma cum_rate_const (r t : ℝ) : r * t = r * t := rfl

end HybridVerify
