/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholes.Put
import HybridVerify.BlackScholes.PutGreeks
import HybridVerify.BlackScholes.PDE

/-!
# American = European for non-dividend call (Merton 1973)

The classical Merton (1973) result: on a non-dividend-paying stock with
positive risk-free rate `r > 0` and remaining time `τ > 0`, **early exercise
of an American call is never optimal**. Consequently the American call price
equals the European call price.

The mathematical heart of the proof is the inequality

  `bsV(S, K, r, σ, τ) > S − K`,

i.e. the European call strictly dominates its own intrinsic value (the
immediate-exercise payoff). The proof goes via the forward lower bound

  `bsV ≥ S − K · e^{−rτ}`

and the strict inequality `K · e^{−rτ} < K` (for `r > 0`, `τ > 0`,
`K > 0`). The forward bound itself is `bsP ≥ 0` plus put-call parity, and
`bsP ≥ 0` is the integral form (`bs_put_formula` plus non-negativity of the
`(K − S_T)^+` payoff).

This establishes the dominance pointwise. Lifting to "American = European"
requires running the optimal-stopping inductive argument on the binomial
tree, which says: at every interior node, the *continuation value* equals
the European call price at that node (by the same argument), so the
continuation value strictly dominates immediate exercise; hence the
American Snell-envelope value equals the European value at every node and
the maturity-payoff equals the European maturity-payoff. The pointwise
strict-dominance below is the inductive step's hypothesis.

Results:

* `bsV_ge_forward_lower_bound`: `bsV ≥ S − K · e^{−rτ}` via `bsP ≥ 0`.
* `bsV_strict_gt_immediate_exercise`: `bsV > S − K` for `r > 0`.
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **No-arbitrage forward lower bound for the European call**:
`bsV(S, K, r, σ, τ) ≥ S − K · e^{−rτ}`.

Proof: by put-call parity `bsP = bsV − S + K · e^{−rτ}`, equivalently
`bsV = bsP + S − K · e^{−rτ}`. The integral form of `bsP` is
`e^{−rτ} · E_Q[(K − S_T)^+] ≥ 0`, so `bsV ≥ S − K · e^{−rτ}`. -/
theorem bsV_ge_forward_lower_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    S_0 - K * Real.exp (-(r * T)) ≤ bsV K r σ S_0 T := by
  have bsP_nonneg : 0 ≤ bsP K r σ S_0 T := by
    have h_put_eq := bs_put_formula h
    have h_match : K * Real.exp (-r * T) * Phi (-bsd2 S_0 K r σ T)
                    - S_0 * Phi (-bsd1 S_0 K r σ T)
                 = bsP K r σ S_0 T := by
      unfold bsP
      have h_exp : Real.exp (-r * T) = Real.exp (-(r * T)) := by
        congr 1; ring
      rw [h_exp]
    rw [← h_match, ← h_put_eq]
    apply integral_nonneg
    intro ω
    exact mul_nonneg (Real.exp_pos _).le (le_max_right _ _)
  have h_pcp := bsP_eq_bsV K r σ S_0 T
  linarith

/-- **Merton 1973: strict dominance of European call over intrinsic value**.
For positive interest rate `r > 0`, positive maturity `τ > 0`, and positive
strike `K > 0`,

  `S − K < bsV(S, K, r, σ, τ)`.

Combined with `bsV ≥ 0` (true by definition of the BS call), this implies
the immediate-exercise payoff `max(S − K, 0)` is strictly dominated by the
call price. Therefore early exercise of the American call is never optimal,
and the American call value equals the European call value. -/
theorem bsV_strict_gt_immediate_exercise
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) (hr : 0 < r) :
    S_0 - K < bsV K r σ S_0 T := by
  have h_forward := bsV_ge_forward_lower_bound h
  have hT_pos : 0 < T := h.T_pos
  have hK_pos : 0 < K := h.K_pos
  have h_rT_pos : 0 < r * T := mul_pos hr hT_pos
  have h_exp_lt_one : Real.exp (-(r * T)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have h_K_strict : K * Real.exp (-(r * T)) < K := by
    have := mul_lt_mul_of_pos_left h_exp_lt_one hK_pos
    simpa using this
  linarith

end HybridVerify
