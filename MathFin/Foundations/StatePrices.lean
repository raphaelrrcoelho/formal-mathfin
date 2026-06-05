/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Arrow-Debreu state prices and the linear pricing functional

In a finite-state market with states `i ∈ s` (a `Finset`), an **Arrow-Debreu
state price** `q i` is the price today of a contingent claim paying `$1` in
state `i` and `$0` elsewhere.

Properties under no-arbitrage:

* **Non-negativity**: `0 ≤ q i` for every state.
* **Discount consistency**: `∑ q i = e^{−rT}` (price of the unit-payoff bond).
* **Linear pricing**: for any claim `X : ι → ℝ`,
  `V_0(X) = ∑ q i · X i`.

The state prices are an equivalent description of the **risk-neutral measure**:
`q i = e^{−rT} · ν i`, where `ν i = Q(state i)`. Equivalently, in discrete time
the FTAP gives existence of either equivalent description.

This is the **discrete-state core** of risk-neutral pricing: every formula in
the library (BS, Black-76, binomial) is `V_0 = ∑ q_i · X_i` in disguise, with
specific `q` given by the model.

## Results

* `statePricePricing`: definition `V_0 = ∑ q_i · X_i`.
* `statePricePricing_zero`: `V_0(0) = 0`.
* `statePricePricing_one`: `V_0(1) = ∑ q_i` (unit-payoff price = ∑ state prices).
* `statePricePricing_const`: `V_0(c · 1) = c · ∑ q_i` (unit-payoff times constant).
* `statePricePricing_add`: linearity in `X`.
* `statePricePricing_smul`: scalar homogeneity in `X`.
* `statePricePricing_eq_riskNeutral`: relation to risk-neutral expectation
  `q_i = e^{−rT} · ν_i ⟹ V_0(X) = e^{−rT} · E^ν[X]`.
* `statePricePricing_nonneg`: payoff non-negative + state prices non-negative ⟹
  price non-negative (no-arb monotonicity).
-/

@[expose] public section

namespace MathFin

open Finset

variable {ι : Type*}

/-- **Linear pricing functional** from Arrow-Debreu state prices:
`V_0(X) = ∑ q_i · X_i`. -/
noncomputable def statePricePricing (s : Finset ι) (q : ι → ℝ) (X : ι → ℝ) : ℝ :=
  ∑ i ∈ s, q i * X i

/-- **Zero payoff has zero price**. -/
lemma statePricePricing_zero (s : Finset ι) (q : ι → ℝ) :
    statePricePricing s q (fun _ => 0) = 0 := by
  unfold statePricePricing
  simp

/-- **Unit-payoff price = sum of state prices**: `V_0(1) = ∑ q_i`. By
no-arb this is the zero-coupon bond price `e^{−rT}` (consistency condition). -/
lemma statePricePricing_one (s : Finset ι) (q : ι → ℝ) :
    statePricePricing s q (fun _ => 1) = ∑ i ∈ s, q i := by
  unfold statePricePricing
  simp

/-- **Scalar payoff**: `V_0(c · 1) = c · ∑ q_i`. -/
lemma statePricePricing_const (s : Finset ι) (q : ι → ℝ) (c : ℝ) :
    statePricePricing s q (fun _ => c) = c * ∑ i ∈ s, q i := by
  unfold statePricePricing
  rw [show (fun i => q i * c) = (fun i => c * q i) from funext (fun i => by ring)]
  rw [← Finset.mul_sum]


/-- **Linearity in payoff** (sum): `V_0(X + Y) = V_0(X) + V_0(Y)`. -/
lemma statePricePricing_add (s : Finset ι) (q X Y : ι → ℝ) :
    statePricePricing s q (fun i => X i + Y i) =
      statePricePricing s q X + statePricePricing s q Y := by
  unfold statePricePricing
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **Scalar homogeneity in payoff**: `V_0(c · X) = c · V_0(X)`. -/
lemma statePricePricing_smul (s : Finset ι) (q X : ι → ℝ) (c : ℝ) :
    statePricePricing s q (fun i => c * X i) = c * statePricePricing s q X := by
  unfold statePricePricing
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **Risk-neutral consistency**: if `q i = e^{−rT} · ν i`, then state-price
pricing equals discounted risk-neutral expectation:
`V_0(X) = e^{−rT} · E^ν[X] = e^{−rT} · ∑ ν_i · X_i`. -/
theorem statePricePricing_eq_riskNeutral
    (s : Finset ι) (ν X : ι → ℝ) (rT : ℝ) :
    statePricePricing s (fun i => Real.exp (-rT) * ν i) X =
      Real.exp (-rT) * ∑ i ∈ s, ν i * X i := by
  unfold statePricePricing
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **No-arbitrage monotonicity**: under non-negative state prices and a
non-negative payoff, the price is non-negative. -/
theorem statePricePricing_nonneg
    (s : Finset ι) (q X : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hX : ∀ i ∈ s, 0 ≤ X i) :
    0 ≤ statePricePricing s q X := by
  unfold statePricePricing
  apply Finset.sum_nonneg
  intros i hi
  exact mul_nonneg (hq i hi) (hX i hi)

end MathFin
