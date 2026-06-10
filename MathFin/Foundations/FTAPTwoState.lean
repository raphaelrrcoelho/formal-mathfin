/-
This file is a **Lean 4 derivative work** based on Section 7 ("The
Fundamental Theorem of Asset Pricing") of:

  Tamás Nagy, "From Itô to Black–Scholes: A Machine-Verified Derivation in
  Lean 4", SSRN Working Paper 6336503, March 2026.
  <https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6336503>

Theorem 7.1 (forward FTAP `EMM ⟹ no arbitrage`), Theorem 7.2 (signs of
no-arb implies opposite-sign components), and Theorem 7.3 (explicit EMM
construction from sign data) are adapted from Nagy's Lean 4 snippets in
the paper, restricted to the one-period, one-asset, two-state case for
concreteness. The general finite-state forward direction is in our
existing `Foundations/NoArbitrageDerivations.lean`.

Author of this MathFin Lean 4 adaptation: Raphael Coelho.
Original Lean derivation: Tamás Nagy (SSRN 6336503, 2026).
Copyright (c) 2026 Raphael Coelho (this adaptation).
Mathematical content and original Lean code © Tamás Nagy 2026, used here
under academic fair use for derivative work with attribution.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# FTAP both directions, two-state market (phase 37, after Nagy 2026)

In a one-period, one-asset market with two states (`up`, `down`) and
excess-return vector `z = (z_up, z_down)`, the **Fundamental Theorem of
Asset Pricing** asserts

  **no arbitrage  ⟺  there exists an Equivalent Martingale Measure (EMM)**.

An EMM is a probability `q = (q_up, q_down)` with `q_up, q_down ∈ (0, 1)`,
`q_up + q_down = 1`, and `q_up · z_up + q_down · z_down = 0` (zero excess
return under `Q`).

**Arbitrage** is a portfolio `θ : ℝ` with `θ · z` componentwise non-
negative and strictly positive in at least one state.

## Results

* `HasEMM_two_state`: definition of EMM existence.
* `HasArbitrage_two_state`: definition of arbitrage.
* `noArbitrage_of_emm` (Nagy 7.1, forward): EMM exists ⟹ no arbitrage.
* `emmWeightUp` / `emmWeightDown`: the named canonical backward-FTAP
  weights `−z_down / (z_up − z_down)`, `z_up / (z_up − z_down)`.
* `emm_of_signs` (Nagy 7.3, backward construction): if `z_up > 0` and
  `z_down < 0`, the named weights form an EMM.
* `emm_of_signs_swapped` / `emm_of_trivial_market`: the mirrored sign
  regime, and the trivial market `z = 0` (EMM `(1/2, 1/2)`).

*Not formalized here*: Nagy 7.2 (no arbitrage and `z ≠ 0` ⟹ opposite
strict signs) and the packaged two-state iff. The backward *construction*
is the load-bearing half: `Foundations/PricingKernel` builds the
discounted state prices directly from the named weights.
-/

@[expose] public section

namespace MathFin

/-- **EMM existence in a two-state market**: there exists a strictly
positive probability `(q_up, q_down)` summing to `1` such that
`q_up · z_up + q_down · z_down = 0` (zero risk-neutral excess return). -/
def HasEMM_two_state (z_up z_down : ℝ) : Prop :=
  ∃ q_up q_down : ℝ,
    0 < q_up ∧ 0 < q_down ∧ q_up + q_down = 1 ∧
    q_up * z_up + q_down * z_down = 0

/-- **Arbitrage in a two-state market**: a portfolio `θ : ℝ` with `θ·z`
componentwise non-negative and strictly positive in at least one state. -/
def HasArbitrage_two_state (z_up z_down : ℝ) : Prop :=
  ∃ θ : ℝ, 0 ≤ θ * z_up ∧ 0 ≤ θ * z_down ∧
    (0 < θ * z_up ∨ 0 < θ * z_down)

/-- **Forward FTAP** (Nagy 2026, Theorem 7.1): if an EMM exists then
there is no arbitrage.

Proof: under EMM, any portfolio satisfies `q_up · (θ z_up) + q_down · (θ
z_down) = θ · 0 = 0`. If both terms are non-negative and one is strictly
positive, the EMM-weighted sum is strictly positive — contradiction. -/
theorem noArbitrage_of_emm (z_up z_down : ℝ)
    (h_emm : HasEMM_two_state z_up z_down) :
    ¬ HasArbitrage_two_state z_up z_down := by
  obtain ⟨q_up, q_down, hq_up_pos, hq_down_pos, _hq_sum, h_zero⟩ := h_emm
  rintro ⟨θ, h_up_nn, h_down_nn, h_one_pos⟩
  -- q_up * (θ * z_up) + q_down * (θ * z_down) = θ * (q_up * z_up + q_down * z_down) = 0
  have h_sum_zero :
      q_up * (θ * z_up) + q_down * (θ * z_down) = 0 := by
    have : q_up * (θ * z_up) + q_down * (θ * z_down) =
           θ * (q_up * z_up + q_down * z_down) := by ring
    rw [this, h_zero, mul_zero]
  -- But each term is ≥ 0 and at least one strictly > 0 ⟹ sum > 0. Contradiction.
  have h_up_term_nn : 0 ≤ q_up * (θ * z_up) := mul_nonneg hq_up_pos.le h_up_nn
  have h_down_term_nn : 0 ≤ q_down * (θ * z_down) := mul_nonneg hq_down_pos.le h_down_nn
  rcases h_one_pos with h_up_pos | h_down_pos
  · have h_up_term_pos : 0 < q_up * (θ * z_up) := mul_pos hq_up_pos h_up_pos
    linarith
  · have h_down_term_pos : 0 < q_down * (θ * z_down) := mul_pos hq_down_pos h_down_pos
    linarith

/-- **The canonical backward-FTAP up-state weight** (Nagy 2026, Theorem 7.3):
`q_up = −z_down / (z_up − z_down)`. Named — rather than left as an
existential witness inside `emm_of_signs` — so downstream constructions
(the discounted state prices of `Foundations/PricingKernel`) can consume
the weights themselves, making their FTAP lineage definitional. -/
noncomputable def emmWeightUp (z_up z_down : ℝ) : ℝ :=
  -z_down / (z_up - z_down)

/-- **The canonical backward-FTAP down-state weight**:
`q_down = z_up / (z_up − z_down)`. See `emmWeightUp`. -/
noncomputable def emmWeightDown (z_up z_down : ℝ) : ℝ :=
  z_up / (z_up - z_down)

/-- **Backward FTAP — EMM construction** (Nagy 2026, Theorem 7.3): if
`z_up > 0` and `z_down < 0`, the named weights
`emmWeightUp = −z_down / (z_up − z_down)`, `emmWeightDown = z_up / (z_up −
z_down)` form an EMM. -/
theorem emm_of_signs (z_up z_down : ℝ)
    (h_up_pos : 0 < z_up) (h_down_neg : z_down < 0) :
    HasEMM_two_state z_up z_down := by
  have h_diff_pos : 0 < z_up - z_down := by linarith
  refine ⟨emmWeightUp z_up z_down, emmWeightDown z_up z_down, ?_, ?_, ?_, ?_⟩ <;>
      simp only [emmWeightUp, emmWeightDown]
  · exact div_pos (neg_pos.mpr h_down_neg) h_diff_pos
  · exact div_pos h_up_pos h_diff_pos
  · field_simp
    ring
  · field_simp
    ring

/-- **Companion variant** of `emm_of_signs`: with `z_up < 0` and `z_down >
0`, the same construction (with roles reversed) yields an EMM. -/
theorem emm_of_signs_swapped (z_up z_down : ℝ)
    (h_up_neg : z_up < 0) (h_down_pos : 0 < z_down) :
    HasEMM_two_state z_up z_down := by
  have h_diff_pos : 0 < z_down - z_up := by linarith
  refine ⟨z_down / (z_down - z_up), -z_up / (z_down - z_up), ?_, ?_, ?_, ?_⟩
  · exact div_pos h_down_pos h_diff_pos
  · exact div_pos (neg_pos.mpr h_up_neg) h_diff_pos
  · field_simp; ring
  · field_simp; ring

/-- **Trivial market**: when `z_up = z_down = 0`, the uniform measure
`(1/2, 1/2)` is an EMM and there is no arbitrage. -/
theorem emm_of_trivial_market :
    HasEMM_two_state 0 0 :=
  ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

end MathFin
