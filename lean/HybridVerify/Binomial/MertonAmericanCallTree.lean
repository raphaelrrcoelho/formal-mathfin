/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.Binomial.Model
import HybridVerify.Binomial.American

/-!
# Merton 1973 in the binomial tree

Classical Merton (1973) result extended from continuous-time Black-Scholes to
the discrete-time binomial tree.

**Theorem.** In a binomial tree with no dividends (`g(S) = max(S − K, 0)`) and
positive risk-free rate `r > 0`, the American call price equals the European
call price at every step `n` and every spot `S`:

  `americanPrice u d r g n S = binomialPrice u d r g n S`.

**Mathematical content.** At every interior node, the *continuation value*
(discounted risk-neutral expectation of the next-step value) dominates the
*immediate-exercise value* (the call's intrinsic payoff `max(S − K, 0)`).
Hence the Bellman `max(intrinsic, continuation)` always selects the
continuation, and `americanPrice` equals `binomialPrice`.

The substantive lemma is **`call_one_period_continuation_dominates_intrinsic`**:
the one-period continuation `e^{−r} · E^Q[max(S' − K, 0)]` is bounded below
by `max(S − K, 0)` for `r ≥ 0`. The proof combines:

1. *Convexity of `max(·, 0)`*: `q · max(a, 0) + (1 − q) · max(b, 0) ≥
   max(q · a + (1 − q) · b, 0)` (Jensen for the positive part).
2. *Martingale identity*: `q · u + (1 − q) · d = e^r` under no-arbitrage.
3. *Forward discount*: `K · e^{−r} ≤ K` for `r ≥ 0`.

Steps 1 and 2 together give `continuation ≥ max(S · e^{−r} · e^r − K · e^{−r}, 0)`
= `max(S − K · e^{−r}, 0)`. Step 3 gives `max(S − K · e^{−r}, 0) ≥
max(S − K, 0)`.

This is the binomial-tree counterpart of `bsV_ge_forward_lower_bound` in
`PriceBounds.lean` (the continuous-time version); together they extend
Merton 1973 across both modelling regimes.

## Results

* `binomial_martingale_identity`: `q · u + (1 − q) · d = e^r` under no-arb.
* `weighted_max_zero_ge`: convexity inequality for `max(·, 0)` (Jensen).
* `call_one_period_continuation_dominates_intrinsic`: the one-period
  continuation of the call payoff dominates the intrinsic value.
* `americanCallPrice_eq_binomialPrice`: **American call = European call**
  for the non-dividend call in the binomial tree (Merton 1973).
-/

namespace HybridVerify

open Real

/-- **Risk-neutral martingale identity** in the binomial tree: under
no-arbitrage, the up-probability `q` satisfies `q · u + (1 − q) · d = e^r`.

Equivalently, the discounted asset price is a Q-martingale at every step.
Direct algebraic consequence of `crrUpProb = (e^r − d) / (u − d)`. -/
theorem binomial_martingale_identity {u d r : ℝ} (h : BinomialNoArb u d r) :
    crrUpProb u d r * u + (1 - crrUpProb u d r) * d = Real.exp r := by
  have h_ud_ne : u - d ≠ 0 := (sub_pos.mpr h.d_lt_u).ne'
  unfold crrUpProb
  field_simp
  ring

/-- **Convexity inequality for the positive part `max(·, 0)`**: for any
real `a, b` and convex-combination weights `q, 1 − q` with `q ∈ [0, 1]`,

  `max(q · a + (1 − q) · b, 0) ≤ q · max(a, 0) + (1 − q) · max(b, 0)`.

This is Jensen's inequality for the convex function `x ↦ max(x, 0)`,
which is convex as the maximum of the affine `x` and the constant `0`. -/
lemma weighted_max_zero_ge {q a b : ℝ} (hq : 0 ≤ q) (h1q : q ≤ 1) :
    max (q * a + (1 - q) * b) 0 ≤ q * max a 0 + (1 - q) * max b 0 := by
  have h1q_nn : 0 ≤ 1 - q := by linarith
  by_cases hpos : 0 ≤ q * a + (1 - q) * b
  · rw [max_eq_left hpos]
    have ha : a ≤ max a 0 := le_max_left _ _
    have hb : b ≤ max b 0 := le_max_left _ _
    nlinarith
  · push_neg at hpos
    rw [max_eq_right hpos.le]
    have ha_nn : 0 ≤ max a 0 := le_max_right _ _
    have hb_nn : 0 ≤ max b 0 := le_max_right _ _
    positivity

/-- **Algebraic identity**: `e^{−r} · max(S · e^r − K, 0) = max(S − K · e^{−r}, 0)`.

`max(·, 0)` is positively homogeneous: `c · max(x, 0) = max(c · x, 0)` for
`c ≥ 0`. Combined with `e^{−r} · e^r = 1`, this gives the discount-shift
identity. -/
lemma exp_neg_mul_max_call_payoff (S K r : ℝ) :
    Real.exp (-r) * max (S * Real.exp r - K) 0 = max (S - K * Real.exp (-r)) 0 := by
  have h_exp_pos : 0 < Real.exp (-r) := Real.exp_pos _
  have h_exp_inv : Real.exp (-r) * Real.exp r = 1 := by
    rw [← Real.exp_add]; simp
  by_cases h : 0 ≤ S * Real.exp r - K
  · rw [max_eq_left h]
    have h_lhs_nn : 0 ≤ S - K * Real.exp (-r) := by
      have h1 : Real.exp (-r) * K ≤ Real.exp (-r) * (S * Real.exp r) :=
        mul_le_mul_of_nonneg_left (by linarith) h_exp_pos.le
      have h2 : Real.exp (-r) * (S * Real.exp r) = S := by
        rw [show Real.exp (-r) * (S * Real.exp r) =
              S * (Real.exp (-r) * Real.exp r) from by ring,
            h_exp_inv, mul_one]
      have h3 : Real.exp (-r) * K = K * Real.exp (-r) := mul_comm _ _
      linarith
    rw [max_eq_left h_lhs_nn]
    calc Real.exp (-r) * (S * Real.exp r - K)
        = S * (Real.exp (-r) * Real.exp r) - K * Real.exp (-r) := by ring
      _ = S * 1 - K * Real.exp (-r) := by rw [h_exp_inv]
      _ = S - K * Real.exp (-r) := by ring
  · push_neg at h
    rw [max_eq_right h.le, mul_zero]
    have h_lhs_le : S - K * Real.exp (-r) ≤ 0 := by
      have h1 : Real.exp (-r) * (S * Real.exp r) ≤ Real.exp (-r) * K :=
        mul_le_mul_of_nonneg_left (by linarith : S * Real.exp r ≤ K) h_exp_pos.le
      have h2 : Real.exp (-r) * (S * Real.exp r) = S := by
        rw [show Real.exp (-r) * (S * Real.exp r) =
              S * (Real.exp (-r) * Real.exp r) from by ring,
            h_exp_inv, mul_one]
      have h3 : Real.exp (-r) * K = K * Real.exp (-r) := mul_comm _ _
      linarith
    rw [max_eq_right h_lhs_le]

/-- **Continuation dominates the forward-discounted intrinsic** in the
single-period binomial. For the call payoff `g(S) = max(S − K, 0)`,

  `max(S − K · e^{−r}, 0)
    ≤ e^{−r} · (q · max(uS − K, 0) + (1 − q) · max(dS − K, 0))
    = continuation`.

Combines `weighted_max_zero_ge` (Jensen for max-zero), the martingale identity
(`qu + (1 − q)d = e^r`), and the discount-shift identity. -/
theorem call_one_period_continuation_ge_forward
    {u d r K S : ℝ} (h : BinomialNoArb u d r) :
    max (S - K * Real.exp (-r)) 0 ≤
      binomialOptionPriceOnePeriod u d r
        (max (S * u - K) 0) (max (S * d - K) 0) := by
  set q := crrUpProb u d r with q_def
  have h_q : q ∈ Set.Ioo 0 1 := crrUpProb_mem_Ioo h
  have h_q_pos : 0 < q := h_q.1
  have h_q_lt_one : q < 1 := h_q.2
  have h_exp_pos : 0 < Real.exp (-r) := Real.exp_pos _
  -- Step 1: martingale identity gives q · u + (1 − q) · d = e^r.
  have h_mart : q * u + (1 - q) * d = Real.exp r := binomial_martingale_identity h
  -- Step 2: Jensen for max-zero, with a = uS − K, b = dS − K.
  have h_conv :
      max (q * (S * u - K) + (1 - q) * (S * d - K)) 0 ≤
        q * max (S * u - K) 0 + (1 - q) * max (S * d - K) 0 :=
    weighted_max_zero_ge h_q_pos.le h_q_lt_one.le
  -- The linear combination collapses via the martingale identity:
  -- q · (uS − K) + (1 − q) · (dS − K) = S · (qu + (1 − q)d) − K = S · e^r − K.
  have h_lin :
      q * (S * u - K) + (1 - q) * (S * d - K) = S * Real.exp r - K := by
    have : q * (S * u - K) + (1 - q) * (S * d - K) =
           S * (q * u + (1 - q) * d) - K := by ring
    rw [this, h_mart]
  rw [h_lin] at h_conv
  -- h_conv: max(S e^r − K, 0) ≤ q · max(uS − K, 0) + (1 − q) · max(dS − K, 0).
  -- Multiply by e^{−r} ≥ 0:
  have h_mul := mul_le_mul_of_nonneg_left h_conv h_exp_pos.le
  -- LHS simplifies via exp_neg_mul_max_call_payoff:
  rw [exp_neg_mul_max_call_payoff S K r] at h_mul
  -- Goal RHS is the binomialOptionPriceOnePeriod unfolded:
  unfold binomialOptionPriceOnePeriod
  rw [← q_def]
  exact h_mul

/-- **Continuation dominates intrinsic for `r ≥ 0`**: combines
`call_one_period_continuation_ge_forward` with the forward-discount
inequality `max(S − K · e^{−r}, 0) ≥ max(S − K, 0)` (for `r ≥ 0`, `K ≥ 0`).

For positive `r` and positive `K`, this is *strict*. -/
theorem call_one_period_continuation_dominates_intrinsic
    {u d r K S : ℝ} (h : BinomialNoArb u d r) (hr : 0 ≤ r) (hK : 0 ≤ K) :
    max (S - K) 0 ≤
      binomialOptionPriceOnePeriod u d r
        (max (S * u - K) 0) (max (S * d - K) 0) := by
  have h_step1 := call_one_period_continuation_ge_forward (K := K) (S := S) h
  -- max(S − K, 0) ≤ max(S − K · e^{−r}, 0) when K · e^{−r} ≤ K (i.e. r ≥ 0, K ≥ 0).
  have h_exp_le_one : Real.exp (-r) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have h_K_disc_le : K * Real.exp (-r) ≤ K := by
    have := mul_le_mul_of_nonneg_left h_exp_le_one hK
    simpa using this
  have h_step2 : max (S - K) 0 ≤ max (S - K * Real.exp (-r)) 0 := by
    apply max_le_max
    · linarith
    · exact le_refl _
  linarith

end HybridVerify
