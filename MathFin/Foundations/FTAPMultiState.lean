/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.FTAPTwoState

/-!
# Multi-state FTAP backward direction (phase 42, hypothesis-form)

The pre-existing `Foundations/FTAPTwoState.lean` (phase 37) gives the
**both-directions** Fundamental Theorem of Asset Pricing in the
**one-period, one-asset, two-state** market. This file extends the
**forward direction** (EMM ⟹ no arbitrage) to **arbitrary finite-state
markets with multiple assets**, and parameterises the **backward
direction** by a separating-functional hypothesis.

## Setup

* `s : Fin N` — states of the world.
* `m : Fin M` — assets (excess-return vectors).
* `z : Fin M → Fin N → ℝ` — excess-return matrix; `z k i` is the
  excess return of asset `k` in state `i`.
* Portfolio: `θ : Fin M → ℝ` — exposure to each asset.
* Portfolio payoff in state `i`: `(Σ_k θ_k · z k i)`.

## Forward FTAP (proved)

`noArbitrage_of_emm_multi`: if there exists `q : Fin N → ℝ` with
`q_i > 0`, `Σ q_i = 1`, and `Σ q_i · z k i = 0` for every asset `k`,
then no portfolio yields a non-negative payoff with at least one
strictly positive state (no arbitrage). Standard linearity argument:
under EMM, every portfolio's `q`-weighted excess return is zero, but
non-negative components with one strictly positive ⟹ strictly positive
weighted sum, contradiction.

## Backward FTAP (hypothesis-form)

Requires Hahn-Banach separation in finite-dim (or Farkas' lemma). Stated
here parameterised by the existence of a separating positive
functional. Mathlib has `Mathlib.Analysis.NormedSpace.HahnBanach.Separation`
for normed spaces; specialising to finite-dim ℝ^N to produce an EMM
without the separation hypothesis is the open work item (call it
"Phase 42c"). For our scope: **the forward direction is fully proved
in arbitrary finite-state, and the backward direction is the
two-state case from Phase 37**.

## Results

* `HasEMM_multi_state`: EMM existence for an N-state market with M assets.
* `HasArbitrage_multi_state`: arbitrage definition.
* `noArbitrage_of_emm_multi`: forward FTAP for arbitrary finite state +
  finite assets.
-/

@[expose] public section

namespace MathFin

open Finset

/-- **EMM existence in a multi-state market** (`N` states, `M` assets):
there exists a strictly positive probability `q : Fin N → ℝ` with `Σ q
= 1` and `q`-weighted excess return zero for every asset. -/
def HasEMM_multi_state {N M : ℕ} (z : Fin M → Fin N → ℝ) : Prop :=
  ∃ q : Fin N → ℝ,
    (∀ i, 0 < q i) ∧
    (∑ i, q i) = 1 ∧
    ∀ k, (∑ i, q i * z k i) = 0

/-- **Arbitrage in a multi-state market**: a portfolio `θ : Fin M → ℝ`
with `θ`-weighted excess return non-negative in every state and
strictly positive in at least one state. -/
def HasArbitrage_multi_state {N M : ℕ} (z : Fin M → Fin N → ℝ) : Prop :=
  ∃ θ : Fin M → ℝ,
    (∀ i, 0 ≤ ∑ k, θ k * z k i) ∧
    (∃ i₀, 0 < ∑ k, θ k * z k i₀)

/-- **Forward FTAP, multi-state**: EMM ⟹ no arbitrage. Standard
linearity proof: under EMM, every portfolio's `q`-weighted excess
return is `Σ_i q_i · (Σ_k θ_k · z k i) = Σ_k θ_k · (Σ_i q_i · z k i) =
Σ_k θ_k · 0 = 0`. If the portfolio's payoff is non-negative in every
state and strictly positive in at least one, the `q`-weighted sum is
strictly positive (positive `q_i` times positive payoff at `i₀`),
contradiction. -/
theorem noArbitrage_of_emm_multi {N M : ℕ} (z : Fin M → Fin N → ℝ)
    (h_emm : HasEMM_multi_state z) :
    ¬ HasArbitrage_multi_state z := by
  obtain ⟨q, hq_pos, _hq_sum, h_q_z⟩ := h_emm
  rintro ⟨θ, h_nn, i₀, h_pos⟩
  -- Compute the q-weighted portfolio payoff and show it equals 0.
  have h_swap : ∑ i, q i * (∑ k, θ k * z k i) = ∑ k, θ k * (∑ i, q i * z k i) := by
    -- Distribute q i over inner ∑ k on LHS, θ k over inner ∑ i on RHS,
    -- then both sides are ∑ ∑ over indexes that swap via Finset.sum_comm.
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h_zero : ∑ i, q i * (∑ k, θ k * z k i) = 0 := by
    rw [h_swap]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [h_q_z k, mul_zero]
  -- But each term ≥ 0 and the i₀-term is > 0, so the sum is > 0. Contradiction.
  have h_term_nn : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      0 ≤ q i * (∑ k, θ k * z k i) :=
    fun i _ => mul_nonneg (hq_pos i).le (h_nn i)
  have h_term_pos : 0 < q i₀ * (∑ k, θ k * z k i₀) :=
    mul_pos (hq_pos i₀) h_pos
  have h_sum_pos : 0 < ∑ i, q i * (∑ k, θ k * z k i) :=
    Finset.sum_pos' h_term_nn ⟨i₀, Finset.mem_univ _, h_term_pos⟩
  linarith

/-- **Backward FTAP, multi-state** — hypothesis-form. If an EMM-like
candidate exists (a positive probability `q` satisfying the EMM
identities), it produces the EMM. The **construction of `q` from the
no-arbitrage condition** requires Hahn-Banach separation in finite-dim
(Farkas' lemma) and is left as the open Phase 42c. This adapter shows
the trivial direction: a candidate satisfying the EMM identities IS the
EMM, so the FTAP backward direction collapses to "find such a `q`". -/
theorem hasEMM_multi_of_candidate {N M : ℕ} (z : Fin M → Fin N → ℝ)
    (q : Fin N → ℝ)
    (hq_pos : ∀ i, 0 < q i)
    (hq_sum : (∑ i, q i) = 1)
    (hq_z : ∀ k, (∑ i, q i * z k i) = 0) :
    HasEMM_multi_state z :=
  ⟨q, hq_pos, hq_sum, hq_z⟩

end MathFin
