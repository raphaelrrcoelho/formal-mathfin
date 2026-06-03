/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Binomial martingale representation (completeness of the binomial market)

On the binomial tree — coin-flip paths `ω : ℕ → Bool`, with the **risk-neutral one-step
condition** `q·X_{n+1}(…,U) + (1 − q)·X_{n+1}(…,D) = X_n` (the explicit form of the conditional
expectation w.r.t. the binomial filtration) — every martingale `M` is the discrete stochastic
integral of a **predictable** strategy `H` against the discounted asset `S`:

  `M_N(ω) = M_0(ω) + ∑_{k<N} H_k(ω)·(S_{k+1}(ω) − S_k(ω))`     (`binomial_martingale_representation`).

This is the **martingale representation theorem** in discrete time — the second pillar of the
fundamental theorem of asset pricing (completeness: every contingent claim is replicable). The
hedge ratio is the node-wise *delta* `H_n = ΔM_{n+1} / ΔS_{n+1}` (the change in `M` over the
change in `S` across the two children of a node); it is predictable because it is fixed *before*
the `(n+1)`-th flip is revealed.

The argument is purely algebraic and pathwise — no measure theory. The one-step identity
(`repr_one_step`) is the node-wise delta hedge, and the multi-period form telescopes. It is the
discrete companion of the abstract martingale-transform converse
(`Foundations/MartingaleTransform.lean`).
-/

namespace MathFin

/-- A real function of an infinite coin-flip path is **`n`-adapted** when it depends only on the
first `n` flips `ω 0, …, ω (n−1)`. -/
def PathAdaptedAt (n : ℕ) (X : (ℕ → Bool) → ℝ) : Prop :=
  ∀ ω ω' : ℕ → Bool, (∀ i, i < n → ω i = ω' i) → X ω = X ω'

variable {q : ℝ} {M S : ℕ → (ℕ → Bool) → ℝ}

/-- The **node-wise hedge ratio** (discrete delta): the change in `M` over the change in `S`
across the up/down children of the level-`n` node carrying path `ω`. -/
noncomputable def hedgeRatio (M S : ℕ → (ℕ → Bool) → ℝ) (n : ℕ) (ω : ℕ → Bool) : ℝ :=
  (M (n + 1) (Function.update ω n true) - M (n + 1) (Function.update ω n false)) /
    (S (n + 1) (Function.update ω n true) - S (n + 1) (Function.update ω n false))

/-- **One-step representation (the node-wise delta hedge).** Under the risk-neutral one-step
condition for `M` and `S` and non-degeneracy of `S`'s branching, the one-period change in `M`
equals the hedge ratio times the one-period change in `S`, on every path. -/
theorem repr_one_step
    (hM_mart : ∀ n ω, q * M (n + 1) (Function.update ω n true)
        + (1 - q) * M (n + 1) (Function.update ω n false) = M n ω)
    (hS_mart : ∀ n ω, q * S (n + 1) (Function.update ω n true)
        + (1 - q) * S (n + 1) (Function.update ω n false) = S n ω)
    (hS_nondeg : ∀ n ω, S (n + 1) (Function.update ω n true)
        ≠ S (n + 1) (Function.update ω n false))
    (n : ℕ) (ω : ℕ → Bool) :
    M (n + 1) ω - M n ω = hedgeRatio M S n ω * (S (n + 1) ω - S n ω) := by
  have hne : S (n + 1) (Function.update ω n true) - S (n + 1) (Function.update ω n false) ≠ 0 :=
    sub_ne_zero.mpr (hS_nondeg n ω)
  rw [hedgeRatio, ← hM_mart n ω, ← hS_mart n ω]
  by_cases hb : ω n = true
  · have hωeq : Function.update ω n true = ω := by
      conv_rhs => rw [← Function.update_eq_self n ω]
      rw [hb]
    rw [hωeq] at hne ⊢
    field_simp
    ring
  · have hbf : ω n = false := by simpa using hb
    have hωeq : Function.update ω n false = ω := by
      conv_rhs => rw [← Function.update_eq_self n ω]
      rw [hbf]
    rw [hωeq] at hne ⊢
    field_simp
    ring

/-- **Binomial martingale representation theorem.** Under the risk-neutral one-step condition,
every martingale `M` is the discrete stochastic integral of the predictable hedge
`hedgeRatio M S` against the discounted asset `S`:
`M_N = M_0 + ∑_{k<N} H_k·(S_{k+1} − S_k)`, with `H` adapted (predictable). The binomial market is
complete — every claim is replicable by a self-financing strategy. -/
theorem binomial_martingale_representation
    (hM_adapt : ∀ n, PathAdaptedAt n (M n)) (hS_adapt : ∀ n, PathAdaptedAt n (S n))
    (hM_mart : ∀ n ω, q * M (n + 1) (Function.update ω n true)
        + (1 - q) * M (n + 1) (Function.update ω n false) = M n ω)
    (hS_mart : ∀ n ω, q * S (n + 1) (Function.update ω n true)
        + (1 - q) * S (n + 1) (Function.update ω n false) = S n ω)
    (hS_nondeg : ∀ n ω, S (n + 1) (Function.update ω n true)
        ≠ S (n + 1) (Function.update ω n false)) :
    ∃ H : ℕ → (ℕ → Bool) → ℝ, (∀ n, PathAdaptedAt n (H n)) ∧
      ∀ N ω, M N ω = M 0 ω + ∑ k ∈ Finset.range N, H k ω * (S (k + 1) ω - S k ω) := by
  refine ⟨hedgeRatio M S, ?_, ?_⟩
  · -- predictability: the hedge ratio depends only on the first `n` flips
    intro n ω ω' hω
    have key : ∀ b : Bool,
        M (n + 1) (Function.update ω n b) = M (n + 1) (Function.update ω' n b) ∧
        S (n + 1) (Function.update ω n b) = S (n + 1) (Function.update ω' n b) := by
      intro b
      have hagree : ∀ i, i < n + 1 → Function.update ω n b i = Function.update ω' n b i := by
        intro i hi
        rcases eq_or_ne i n with rfl | hi'
        · simp
        · rw [Function.update_of_ne hi', Function.update_of_ne hi']
          exact hω i (by omega)
      exact ⟨hM_adapt (n + 1) _ _ hagree, hS_adapt (n + 1) _ _ hagree⟩
    simp only [hedgeRatio]
    rw [(key true).1, (key true).2, (key false).1, (key false).2]
  · -- the representation telescopes from the one-step identity
    intro N ω
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih,
          ← repr_one_step hM_mart hS_mart hS_nondeg N ω]
      ring

end MathFin
