/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Strike-direction convexity of the European call payoff

The European call payoff at maturity is `K ↦ max(S − K, 0)`. As a function of
the strike `K` at fixed terminal price `S`, this payoff has two structural
properties:

* **`Antitone`** in `K` (decreasing): higher strikes pay less.
* **`ConvexOn`** in `K` (convex, as the maximum of an affine function and zero).

Almost every static no-arbitrage relation between option prices traces back
to one of these. We collect them here as the canonical source.

## Why this matters

Bull-spread non-negativity, butterfly non-negativity, and Breeden-Litzenberger
PDF positivity are *not three theorems*; they are three faces of the same
fact:

* **Bull spread** `V(K₁) ≥ V(K₂)` for `K₁ ≤ K₂` — Antitone-payoff after
  risk-neutral expectation.
* **Butterfly** `V(K₁) − 2V(K₂) + V(K₃) ≥ 0` for `K₂ = (K₁+K₃)/2` —
  ConvexOn-payoff after risk-neutral expectation, discrete second-difference
  form.
* **Breeden-Litzenberger PDF positivity** `f(K) = e^{rT}·∂²_K V ≥ 0` —
  ConvexOn-payoff after risk-neutral expectation, infinitesimal form.

Risk-neutral expectation `E_Q[·]` is a positive linear operator. It preserves
both `Antitone` and `ConvexOn`. So the payoff properties become call-*price*
properties, and the static no-arb relations are corollaries.

## Why ConvexOn-payoff holds

`fun K => max (S − K) 0 = (S − ·) ⊔ 0`. The affine function `K ↦ S − K` is
convex (in fact affine, hence both convex and concave). The constant function
`0` is convex. The pointwise max of two convex functions is convex
(`ConvexOn.sup`). One line.

## Results

* `convexOn_sub_const_id`: `K ↦ a − K` is convex.
* `convexOn_call_payoff`: `K ↦ max(S − K, 0)` is convex in K.
* `antitone_call_payoff`: `K ↦ max(S − K, 0)` is antitone in K.

The downstream consumers (`Spreads.lean`, `Lookback.lean`,
`StrikeGreeks.lean`, `BreedenLitzenberger.lean`) all rest on these.
-/

namespace HybridVerify

open Set

/-- The affine function `K ↦ a − K` is convex on `Set.univ`. Affine
functions are simultaneously convex and concave; the inequality holds
with equality. -/
lemma convexOn_sub_const_id (a : ℝ) :
    ConvexOn ℝ Set.univ (fun K : ℝ => a - K) := by
  refine ⟨convex_univ, fun K₁ _ K₂ _ s t _ _ hst => ?_⟩
  show a - (s • K₁ + t • K₂) ≤ s • (a - K₁) + t • (a - K₂)
  simp only [smul_eq_mul]
  -- Equality (affine functions are tight): `s·a + t·a = a` via `s + t = 1`.
  have h_sa_ta : s * a + t * a = a := by linear_combination a * hst
  linarith

/-- **Call payoff is convex in the strike**: `K ↦ max(S − K, 0)` is convex.

This is the structural spine of static option-price no-arbitrage relations.
Butterfly non-negativity and Breeden-Litzenberger PDF positivity are
discrete and infinitesimal consequences (respectively) of this single fact,
after passing through risk-neutral expectation. -/
lemma convexOn_call_payoff (S : ℝ) :
    ConvexOn ℝ Set.univ (fun K : ℝ => max (S - K) 0) :=
  (convexOn_sub_const_id S).sup (convexOn_const (0 : ℝ) convex_univ)

/-- **Call payoff is antitone in the strike**: higher strikes pay less.

Equivalent to monotonicity of `max(·, 0)` composed with `K ↦ S − K` (which
is itself antitone). The single-line consequence of monotonicity of `max`. -/
lemma antitone_call_payoff (S : ℝ) :
    Antitone (fun K : ℝ => max (S - K) 0) :=
  fun _ _ h => max_le_max (by linarith) le_rfl

end HybridVerify
