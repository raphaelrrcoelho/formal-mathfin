/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

-- pointers: MathFin/FixedIncome/ForwardRate.lean, MathFin/FixedIncome/ZCB.lean
-- main-module: MathFin/FixedIncome/FRA.lean
-- benchmark: benchmarks/mathematical_finance.json
-- benchmark-id: mf-fi-fra
-- source-issue: 67

/-!
# Forward-rate agreement: value and the fair simple forward rate

A forward-rate agreement (FRA) over the accrual period `[T₁, T₂]` with year
fraction `δ = T₂ − T₁` locks a fixed rate `K` against the realised simple rate.
Writing `P₁ = P(0,T₁)` and `P₂ = P(0,T₂)` for the two zero-coupon discount
factors (positive reals from the `ZCB` curve), the **simple forward rate** is

  `F = (P₁ / P₂ − 1) / δ`,

the strike that makes the forward loan self-financing. This module records the
three elementary discount-factor identities of an FRA (`P₂ > 0`, `δ ≠ 0`):

* **No-arbitrage forward rate** — `F` reproduces the replication relation
  `P₁ = P₂ · (1 + δ · F)` (buy the `T₁`-bond, roll at `F` out to `T₂`).
* **FRA value in discount factors** — the time-0 value `V = δ · P₂ · (F − K)`
  is the floating leg minus the fixed leg, `V = (P₁ − P₂) − δ · K · P₂`.
* **Fair FRA rate** — the value vanishes exactly at the strike `K = F`.

Purely `field_simp` / `ring` algebra over the discount factors; the discrete
counterpart of the instantaneous `forwardRate` in `ForwardRate.lean`.
-/

@[expose] public section

namespace MathFin

/-- **FRA value and the fair simple forward rate.** For zero-coupon discount
factors `P₁ = P(0,T₁)`, `P₂ = P(0,T₂)` (with `P₂ > 0`, accrual `δ ≠ 0`) and the
simple forward rate `F = (P₁/P₂ − 1)/δ`:

* `P₁ = P₂ · (1 + δ · F)` — `F` is the no-arbitrage forward rate;
* `δ · P₂ · (F − K) = (P₁ − P₂) − δ · K · P₂` — the FRA value is the floating
  leg minus the fixed leg;
* `δ · P₂ · (F − K) = 0 ↔ K = F` — the value vanishes exactly at the fair rate. -/
theorem fra_value_and_fair_rate
    {P₁ P₂ δ K F : ℝ} (hP₂ : 0 < P₂) (hδ : δ ≠ 0)
    (hF : F = (P₁ / P₂ - 1) / δ) :
    P₁ = P₂ * (1 + δ * F) ∧
    δ * P₂ * (F - K) = (P₁ - P₂) - δ * K * P₂ ∧
    (δ * P₂ * (F - K) = 0 ↔ K = F) := by
  have hδF : δ * F = P₁ / P₂ - 1 := by
    rw [hF]
    field_simp [hδ]
  have hP₁_div : P₁ / P₂ = 1 + δ * F := by linarith
  have hP₁_eq : P₁ = P₂ * (1 + δ * F) := by
    calc
      P₁ = P₂ * (P₁ / P₂) := by field_simp [hP₂.ne.symm]
      _ = P₂ * (1 + δ * F) := by rw [hP₁_div]
  have h_eq : δ * P₂ * F = P₁ - P₂ := by linarith
  have h_part2 : δ * P₂ * (F - K) = (P₁ - P₂) - δ * K * P₂ := by
    calc
      δ * P₂ * (F - K) = (δ * P₂ * F) - (δ * P₂ * K) := by ring
      _ = (P₁ - P₂) - (δ * P₂ * K) := by rw [h_eq]
      _ = (P₁ - P₂) - δ * K * P₂ := by ring
  have h_part3 : (δ * P₂ * (F - K) = 0 ↔ K = F) := by
    have h_nonzero : δ * P₂ ≠ 0 := mul_ne_zero hδ (by linarith)
    constructor
    · intro h
      rcases eq_zero_or_eq_zero_of_mul_eq_zero h with (hδP₂ | hFK)
      · exfalso; exact h_nonzero hδP₂
      · linarith
    · intro h; rw [h]; ring
  exact And.intro hP₁_eq (And.intro h_part2 h_part3)

end MathFin
