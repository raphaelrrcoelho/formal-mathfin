/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# The fundamental superhedging bound

In a finite-state market with excess-return matrix `z : Fin M → Fin N → ℝ` (`M` assets, `N` states),
every equivalent martingale measure prices a claim at most its super-replication cost:
`∑ qₙ Yₙ ≤ x` for any EMM `q` and any cost-`x` portfolio `θ` that dominates `Y` in every state. Hence
the EMM prices of a claim lie below its superhedging price — the dual side of the no-arbitrage pricing
interval, and the pricing-side companion of the coherent-risk representation.

The full superhedging *duality* (superhedging price *equals* the supremum of EMM prices) is the reverse,
separation-based direction; it requires closedness of the super-replication cone `{W | ∃ θ, W ≤ θ·z}` (a
polyhedral / Farkas fact not available in Mathlib at this pin) and is recorded as a follow-up.

## Main results
* `MathFin.EMMSet`, `MathFin.SuperReplicates`
* `MathFin.emm_le_superReplication` — the fundamental bound
-/

@[expose] public section

namespace MathFin


variable {M N : ℕ}

/-- The set of equivalent martingale measures for an excess-return matrix `z`: probability vectors
under which every asset's excess return is fair (prices to zero). -/
def EMMSet (z : Fin M → Fin N → ℝ) : Set (Fin N → ℝ) :=
  {q | (∀ n, 0 ≤ q n) ∧ (∑ n, q n = 1) ∧ ∀ m, ∑ n, q n * z m n = 0}

/-- `(x, θ)` super-replicates the claim `Y`: cost `x` plus the portfolio `θ` dominates `Y` in every
state. -/
def SuperReplicates (z : Fin M → Fin N → ℝ) (Y : Fin N → ℝ) (x : ℝ) (θ : Fin M → ℝ) : Prop :=
  ∀ n, Y n ≤ x + ∑ m, θ m * z m n

/-- **The fundamental superhedging bound.** Every EMM price of a claim is at most every
super-replication cost: under any martingale measure, the claim's expected value cannot exceed the
cost of any portfolio that dominates it. The dual side of the no-arbitrage pricing interval. -/
theorem emm_le_superReplication (z : Fin M → Fin N → ℝ) (Y : Fin N → ℝ)
    {q : Fin N → ℝ} (hq : q ∈ EMMSet z) {x : ℝ} {θ : Fin M → ℝ}
    (hsr : SuperReplicates z Y x θ) :
    ∑ n, q n * Y n ≤ x := by
  obtain ⟨hq_nn, hq_sum, hq_mart⟩ := hq
  have hcross : ∑ n, q n * (∑ m, θ m * z m n) = 0 := by
    have hswap : ∑ n, q n * (∑ m, θ m * z m n) = ∑ m, θ m * (∑ n, q n * z m n) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
    rw [hswap]
    exact Finset.sum_eq_zero fun m _ => by rw [hq_mart m, mul_zero]
  calc ∑ n, q n * Y n
      ≤ ∑ n, q n * (x + ∑ m, θ m * z m n) :=
        Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hsr n) (hq_nn n)
    _ = x := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hq_sum, one_mul, hcross, add_zero]

end MathFin
