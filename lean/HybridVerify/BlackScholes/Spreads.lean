/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Static spread non-negativity (bull-call, butterfly)

Two no-arbitrage payoff inequalities at expiry that follow from the call payoff
`max(S − K, 0)` alone, with no dependence on a pricing model:

* **Bull-call spread non-negativity**: for `K₁ ≤ K₂`,
  `max(S − K₂, 0) ≤ max(S − K₁, 0)`.
  By no-arb (LOOP): a portfolio long `C(K₁)` short `C(K₂)` has non-negative
  payoff at expiry, so its price today is non-negative.
* **Butterfly non-negativity**: for `K₁ ≤ K₃` and `K₂ = (K₁ + K₃)/2`,
  `0 ≤ max(S − K₁, 0) − 2 · max(S − K₂, 0) + max(S − K₃, 0)`.
  Pure case split: at most one of the three legs contributes a non-zero
  weight, and the central piece cancels by midpoint symmetry.

Both are model-light arbitrage relations that constrain any consistent option
price surface; the butterfly inequality is the cornerstone of the
Breeden–Litzenberger non-negativity-of-implied-density argument.
-/

namespace HybridVerify

/-- **Bull-call spread payoff non-negativity**: for `K₁ ≤ K₂`,
`max(S − K₂, 0) ≤ max(S − K₁, 0)`. -/
lemma bull_call_spread_payoff_le (S K₁ K₂ : ℝ) (h : K₁ ≤ K₂) :
    max (S - K₂) 0 ≤ max (S - K₁) 0 :=
  max_le_max (by linarith) le_rfl

/-- **Butterfly spread payoff non-negativity**: for `K₁ ≤ K₃` with the central
strike at the midpoint `K₂ = (K₁ + K₃)/2`,
`0 ≤ max(S − K₁, 0) − 2 · max(S − (K₁+K₃)/2, 0) + max(S − K₃, 0)`. -/
lemma butterfly_payoff_nonneg (S K₁ K₃ : ℝ) (h : K₁ ≤ K₃) :
    0 ≤
      max (S - K₁) 0 -
        2 * max (S - (K₁ + K₃) / 2) 0 +
        max (S - K₃) 0 := by
  set K₂ := (K₁ + K₃) / 2 with hK₂
  have hK₁₂ : K₁ ≤ K₂ := by rw [hK₂]; linarith
  have hK₂₃ : K₂ ≤ K₃ := by rw [hK₂]; linarith
  by_cases h1 : S ≤ K₁
  · have e1 : max (S - K₁) 0 = 0 := max_eq_right (by linarith)
    have e2 : max (S - K₂) 0 = 0 := max_eq_right (by linarith)
    have e3 : max (S - K₃) 0 = 0 := max_eq_right (by linarith)
    rw [e1, e2, e3]; norm_num
  push_neg at h1
  by_cases h2 : S ≤ K₂
  · have e1 : max (S - K₁) 0 = S - K₁ := max_eq_left (by linarith)
    have e2 : max (S - K₂) 0 = 0 := max_eq_right (by linarith)
    have e3 : max (S - K₃) 0 = 0 := max_eq_right (by linarith)
    rw [e1, e2, e3]; linarith
  push_neg at h2
  by_cases h3 : S ≤ K₃
  · have e1 : max (S - K₁) 0 = S - K₁ := max_eq_left (by linarith)
    have e2 : max (S - K₂) 0 = S - K₂ := max_eq_left (by linarith)
    have e3 : max (S - K₃) 0 = 0 := max_eq_right (by linarith)
    rw [e1, e2, e3]
    have hmid : 2 * K₂ = K₁ + K₃ := by rw [hK₂]; ring
    linarith
  · push_neg at h3
    have e1 : max (S - K₁) 0 = S - K₁ := max_eq_left (by linarith)
    have e2 : max (S - K₂) 0 = S - K₂ := max_eq_left (by linarith)
    have e3 : max (S - K₃) 0 = S - K₃ := max_eq_left (by linarith)
    rw [e1, e2, e3]
    have hmid : 2 * K₂ = K₁ + K₃ := by rw [hK₂]; ring
    linarith

end HybridVerify
