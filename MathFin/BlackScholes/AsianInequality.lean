/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Geometric vs arithmetic Asian options

The geometric Asian option's payoff is bounded above by the arithmetic Asian
option's payoff at every state, because the geometric mean of positive numbers
is at most their arithmetic mean (AM-GM).

For prices `S_{t_1}, …, S_{t_n} ≥ 0`:

  `(∏ S_{t_i})^{1/n} ≤ (1/n) ∑ S_{t_i}`.

Since `x ↦ max(x − K, 0)` is monotone non-decreasing:

  `max(geomMean − K, 0) ≤ max(arithMean − K, 0)`.

Integrating over the pricing measure preserves this pointwise inequality, so
the geometric Asian price is bounded above by the arithmetic Asian price.

Results:

* `am_gm_two`: `√(a · b) ≤ (a + b) / 2` for `a, b ≥ 0` — Mathlib's
  `Real.geom_mean_le_arith_mean2_weighted` at weights `1/2`, bridged from
  `rpow` to `sqrt`.
* `geom_mean_le_arith_mean_n`: weighted AM-GM specialized to equal weights
  `1/n` (Mathlib's `Real.geom_mean_le_arith_mean_weighted`).
* `asian_payoff_geom_le_arith_two`: two-time-point geometric Asian payoff is
  bounded above by the arithmetic Asian payoff.
-/

namespace MathFin

open Real

/-- **Two-element AM-GM**: `√(a · b) ≤ (a + b) / 2` for `a, b ≥ 0`. Mathlib's
weighted two-element AM-GM `Real.geom_mean_le_arith_mean2_weighted` at weights
`w₁ = w₂ = 1/2`, with `√x = x^(1/2)` bridging `sqrt` to `rpow`. -/
lemma am_gm_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have h := Real.geom_mean_le_arith_mean2_weighted
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) ha hb
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  calc Real.sqrt (a * b) = (a * b) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
    _ = a ^ ((1:ℝ)/2) * b ^ ((1:ℝ)/2) := Real.mul_rpow ha hb
    _ ≤ 1/2 * a + 1/2 * b := h
    _ = (a + b) / 2 := by ring

/-- **Two-time-point geometric vs arithmetic Asian payoff**: for positive
prices `S₁, S₂` and any strike `K`, the geometric-Asian-call payoff is
bounded above by the arithmetic-Asian-call payoff. -/
lemma asian_payoff_geom_le_arith_two (S₁ S₂ K : ℝ) (h₁ : 0 ≤ S₁) (h₂ : 0 ≤ S₂) :
    max (Real.sqrt (S₁ * S₂) - K) 0 ≤ max ((S₁ + S₂) / 2 - K) 0 := by
  have h_mean := am_gm_two S₁ S₂ h₁ h₂
  -- max is monotone in the first argument: x ≤ y ⟹ max(x - K, 0) ≤ max(y - K, 0)
  have h_sub : Real.sqrt (S₁ * S₂) - K ≤ (S₁ + S₂) / 2 - K := by linarith
  exact max_le_max h_sub le_rfl

/-- **Weighted AM-GM, n-element equal-weight form**:
`n · ∏ f_i^{1/n} ≤ ∑ f_i` for non-negative `f : Fin n → ℝ` and `n > 0`. -/
lemma geom_mean_le_arith_mean_n {n : ℕ} (f : Fin n → ℝ)
    (h_nn : ∀ i, 0 ≤ f i) (hn : 0 < n) :
    (n : ℝ) * (∏ i : Fin n, f i ^ ((n : ℝ)⁻¹)) ≤ ∑ i : Fin n, f i := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have hn_inv_nn : 0 ≤ ((n : ℝ))⁻¹ := inv_nonneg.mpr hn_pos.le
  set w : Fin n → ℝ := fun _ => ((n : ℝ))⁻¹ with hw
  have h_w_nn : ∀ i ∈ Finset.univ, 0 ≤ w i := fun _ _ => hn_inv_nn
  have h_f_nn : ∀ i ∈ Finset.univ, 0 ≤ f i := fun i _ => h_nn i
  have h_sum_w : ∑ i ∈ Finset.univ, w i = 1 := by
    show ∑ _ : Fin n, ((n : ℝ))⁻¹ = 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- Apply Mathlib weighted AM-GM with `w` and `z := f`.
  have h := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
              w f h_w_nn h_sum_w h_f_nn
  -- `h : ∏ i, f i ^ (1/n) ≤ ∑ i, (1/n) * f i`
  -- Multiply both sides by `n ≥ 0`.
  have h_mul := mul_le_mul_of_nonneg_left h hn_pos.le
  -- Now LHS: n * ∏, RHS: n * ∑ (1/n) * f = ∑ f.
  have h_rhs_simp : (n : ℝ) * ∑ i : Fin n, w i * f i = ∑ i : Fin n, f i := by
    show (n : ℝ) * ∑ i : Fin n, ((n : ℝ))⁻¹ * f i = ∑ i : Fin n, f i
    rw [← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hn_ne, one_mul]
  rw [h_rhs_simp] at h_mul
  exact h_mul

end MathFin
