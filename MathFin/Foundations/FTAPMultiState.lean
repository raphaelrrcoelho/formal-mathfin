/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.FTAPTwoState
public import MathFin.Foundations.ConvexSeparation

/-!
# Multi-state FTAP (both directions)

The pre-existing `Foundations/FTAPTwoState.lean` (phase 37) gives the
Fundamental Theorem of Asset Pricing in the **one-period, one-asset,
two-state** market. This file extends it to **arbitrary finite-state
markets with multiple assets**, in **both directions**: the forward
direction (EMM ⟹ no arbitrage, phase 42) and the backward direction
(no arbitrage ⟹ EMM, 2026-06-25) — the latter constructs the EMM by
finite-dimensional geometric Hahn–Banach separation of the
attainable-payoff span from the standard simplex
(`exists_pos_dual_of_disjoint_stdSimplex`, `Foundations/ConvexSeparation.lean`).

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

## Backward FTAP (proved)

`hasEMM_multi_of_not_hasArbitrage`: no arbitrage ⟹ an EMM exists. The
attainable-payoff subspace `span {z k}` misses the standard simplex (that is
exactly no arbitrage), so the separating-dual kernel
`exists_pos_dual_of_disjoint_stdSimplex` (`Foundations/ConvexSeparation.lean`,
finite-dimensional geometric Hahn–Banach) produces a strictly-positive `q`
annihilating every asset's excess return; normalising `q` to a probability is
the EMM. Together with the forward direction this is the biconditional
`hasEMM_multi_iff_not_hasArbitrage`.

## Results

* `HasEMM_multi_state`: EMM existence for an N-state market with M assets.
* `HasArbitrage_multi_state`: arbitrage definition.
* `noArbitrage_of_emm_multi`: forward FTAP (EMM ⟹ no arbitrage).
* `hasEMM_multi_of_not_hasArbitrage`: backward FTAP (no arbitrage ⟹ EMM).
* `hasEMM_multi_iff_not_hasArbitrage`: the multi-state FTAP biconditional.
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
  exact h_sum_pos.ne' h_zero

/-- **Backward FTAP, multi-state**: no arbitrage ⟹ an EMM exists. The
attainable-payoff subspace `span {z k}` is disjoint from the standard simplex
(no arbitrage), so `exists_pos_dual_of_disjoint_stdSimplex` yields a
strictly-positive dual `q` with `∑ i, q i · z k i = 0` for every asset `k`;
normalising `q` to a probability is the equivalent martingale measure. -/
theorem hasEMM_multi_of_not_hasArbitrage {N M : ℕ} [NeZero N]
    (z : Fin M → Fin N → ℝ) (h : ¬ HasArbitrage_multi_state z) :
    HasEMM_multi_state z := by
  classical
  -- The attainable-payoff subspace.
  set V : Submodule ℝ (Fin N → ℝ) := Submodule.span ℝ (Set.range z) with hVdef
  -- No arbitrage ⇒ `V` misses the standard simplex.
  have hdisj : ∀ v ∈ V, v ∉ stdSimplex ℝ (Fin N) := by
    intro v hv hsimplex
    rw [hVdef, Submodule.mem_span_range_iff_exists_fun] at hv
    obtain ⟨c, hc⟩ := hv
    have hpayoff : ∀ i, (∑ k, c k * z k i) = v i := by
      intro i
      have h1 : (∑ k, c k • z k) i = v i := by rw [hc]
      rw [Finset.sum_apply] at h1
      simpa only [Pi.smul_apply, smul_eq_mul] using h1
    refine absurd ⟨c, fun i => ?_, ?_⟩ h
    · rw [hpayoff i]; exact hsimplex.1 i
    · obtain ⟨i₀, hi₀⟩ : ∃ i₀, 0 < v i₀ := by
        by_contra hcon
        simp only [not_exists, not_lt] at hcon
        have hle : ∑ i, v i ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
        rw [hsimplex.2] at hle; linarith
      exact ⟨i₀, by rw [hpayoff i₀]; exact hi₀⟩
  obtain ⟨q, hq_pos, hq_dual⟩ := exists_pos_dual_of_disjoint_stdSimplex V hdisj
  have hzk : ∀ k, (∑ i, q i * z k i) = 0 := fun k =>
    hq_dual (z k) (Submodule.subset_span ⟨k, rfl⟩)
  set Z : ℝ := ∑ i, q i with hZdef
  have hZ_pos : 0 < Z := Finset.sum_pos (fun i _ => hq_pos i) Finset.univ_nonempty
  refine ⟨fun i => q i / Z, fun i => div_pos (hq_pos i) hZ_pos, ?_, fun k => ?_⟩
  · rw [← Finset.sum_div, ← hZdef, div_self hZ_pos.ne']
  · have hcongr : ∀ i, (q i / Z) * z k i = (q i * z k i) / Z := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hcongr i), ← Finset.sum_div, hzk k, zero_div]

/-- **Multi-state FTAP biconditional**: an EMM exists iff there is no
arbitrage. -/
theorem hasEMM_multi_iff_not_hasArbitrage {N M : ℕ} [NeZero N]
    (z : Fin M → Fin N → ℝ) :
    HasEMM_multi_state z ↔ ¬ HasArbitrage_multi_state z :=
  ⟨noArbitrage_of_emm_multi z, hasEMM_multi_of_not_hasArbitrage z⟩

end MathFin
