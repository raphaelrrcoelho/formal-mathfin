/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.Numeraire
public import MathFin.BlackScholes.Forward

/-!
# The T-forward measure — the zero-coupon bond as numéraire

The **T-forward measure** `Q^T` is the pricing measure obtained by taking the
zero-coupon bond `P(·, T)` maturing at `T` as the numéraire, instead of the money
market. Its defining property is that the **forward price is a `Q^T`-martingale**:
for any traded claim,

  `P(0, T) · 𝔼^{Q^T}[X] = 𝔼^Q[e^{−rT} · X]`,

and in particular the forward price of the spot is its `Q^T`-expectation,
`𝔼^{Q^T}[S_T] = S_0 / P(0, T) = F(0, T)`.

This is the natural next instance of the change-of-numéraire engine
(`Foundations/Numeraire`), after the stock numéraire and the exchange-option
`S²`-numéraire. Reading off the engine's slots for the bond numéraire against the
money-market reference (`B_T = e^{rT}`, `B_0 = 1`): the bond pays one unit at
maturity, so `N_T = P(T, T) = 1`, with `N_0 = P(0, T) = e^{−rT}` the constant-rate
zero-coupon price (`FixedIncome/ZCB.zcb`).

## Honest scope

In the **constant-rate** world the bond `P(t, T) = e^{−r(T−t)}` is deterministic,
so the density `dQ^T/dQ = (N_T·B_0)/(N_0·B_T) = e^{rT}/e^{rT} = 1` and `Q^T = Q`
coincides with the risk-neutral measure — the forward-price identity below then
reduces to the familiar `𝔼^Q[S_T] = S_0·e^{rT}`. The *construction* and the
change-of-numéraire identity are stated for the general engine and carry over
verbatim to a stochastic short rate (where `P(·, T)` is a genuine `Q`-martingale
numéraire and `Q^T ≠ Q`); only the concrete constant-rate instance is degenerate.

## Main results

* `forwardMeasure` — the measure `Q^T` as a `numeraireMeasure` instance.
* `forwardMeasure_isProbabilityMeasure` — `Q^T` is a probability measure.
* `forwardMeasure_price` — the bond-numéraire change-of-measure identity
  `e^{−rT}·𝔼^{Q^T}[X] = 𝔼^Q[e^{−rT}·X]`.
* `forwardMeasure_expected_spot` — `𝔼^{Q^T}[S_T] = S_0·e^{rT}` from the EMM property.
* `forwardMeasure_bs_expected_terminal` — the concrete Black–Scholes instance.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **T-forward measure** `Q^T`: the change-of-numéraire measure with the
zero-coupon bond `P(·, T)` as numéraire. In the constant-rate model
`N_T = P(T, T) = 1`, `N_0 = P(0, T) = e^{−rT}`, against the money-market
reference `B_T = e^{rT}`, `B_0 = 1`. -/
noncomputable def forwardMeasure (Q : Measure Ω) (r T : ℝ) : Measure Ω :=
  numeraireMeasure Q (fun _ ↦ Real.exp (r * T)) (fun _ ↦ (1 : ℝ)) 1 (Real.exp (-(r * T)))

/-- **The T-forward measure is a probability measure.** The normalisation
`𝔼^Q[N_T/B_T] = N_0/B_0` reads `𝔼^Q[e^{−rT}] = e^{−rT}`, which holds because the
integrand is the constant `e^{−rT}` and `Q` is a probability measure. -/
theorem forwardMeasure_isProbabilityMeasure {Q : Measure Ω} [IsProbabilityMeasure Q] (r T : ℝ) :
    IsProbabilityMeasure (forwardMeasure Q r T) := by
  refine numeraireMeasure_isProbabilityMeasure (fun _ ↦ one_pos) (fun _ ↦ Real.exp_pos _)
    one_pos (Real.exp_pos _) (integrable_const _) ?_
  have hconst : (fun ω : Ω ↦ (1 : ℝ) / Real.exp (r * T)) = fun _ ↦ Real.exp (-(r * T)) := by
    funext ω; simp [Real.exp_neg]
  rw [hconst, integral_const]
  simp

/-- **The bond-numéraire change of measure**: `e^{−rT}·𝔼^{Q^T}[X] = 𝔼^Q[e^{−rT}·X]`.
Directly the change-of-numéraire theorem with the bond slots `N_T = 1`,
`N_0 = e^{−rT}`, `B_T = e^{rT}`, `B_0 = 1` (no integrability hypothesis needed). -/
theorem forwardMeasure_price {Q : Measure Ω} (X : Ω → ℝ) (r T : ℝ) :
    Real.exp (-(r * T)) * ∫ ω, X ω ∂(forwardMeasure Q r T)
      = ∫ ω, Real.exp (-(r * T)) * X ω ∂Q := by
  have h := changeOfNumeraire (Q := Q) (BT := fun _ ↦ Real.exp (r * T))
    (NT := fun _ ↦ (1 : ℝ)) (B0 := (1 : ℝ)) (N0 := Real.exp (-(r * T))) X
    measurable_const measurable_const (fun _ ↦ one_pos) (fun _ ↦ Real.exp_pos _)
    (by norm_num) (Real.exp_pos _)
  simp only [div_one, one_mul] at h
  rw [forwardMeasure, h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  show X ω / Real.exp (r * T) = Real.exp (-(r * T)) * X ω
  rw [div_eq_mul_inv, ← Real.exp_neg, mul_comm]

/-- **The forward price is the `Q^T`-expectation of the spot**: given the EMM
property `𝔼^Q[e^{−rT}·S_T] = S_0`, one has `𝔼^{Q^T}[S_T] = S_0·e^{rT} = S_0/P(0,T)`
— the no-arbitrage forward price. -/
theorem forwardMeasure_expected_spot {Q : Measure Ω} (S_0 r T : ℝ) (X : Ω → ℝ)
    (hEMM : ∫ ω, Real.exp (-(r * T)) * X ω ∂Q = S_0) :
    ∫ ω, X ω ∂(forwardMeasure Q r T) = S_0 * Real.exp (r * T) := by
  have hp := forwardMeasure_price (Q := Q) X r T
  rw [hEMM] at hp
  have key : ∫ ω, X ω ∂(forwardMeasure Q r T)
      = Real.exp (r * T) * (Real.exp (-(r * T)) * ∫ ω, X ω ∂(forwardMeasure Q r T)) := by
    rw [← mul_assoc, ← Real.exp_add, show r * T + -(r * T) = 0 from by ring, Real.exp_zero, one_mul]
  rw [key, hp, mul_comm]

/-- **The Black–Scholes forward price under the T-forward measure**: for the
`BSCallHyp` lognormal terminal, `𝔼^{Q^T}[S_T] = S_0·e^{rT}`. Combines the
`Q^T`-expectation identity with the discounted-terminal EMM property
`discounted_terminal_eq_S0`. -/
theorem forwardMeasure_bs_expected_terminal {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, bsTerminal S_0 r σ T (Z ω) ∂(forwardMeasure Q r T) = S_0 * Real.exp (r * T) :=
  forwardMeasure_expected_spot S_0 r T _ (discounted_terminal_eq_S0 h)

end MathFin
