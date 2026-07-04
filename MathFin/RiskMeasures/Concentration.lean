/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Concentration risk: Herfindahl–Hirschman Index (HHI)

For a portfolio with weights `w_i` (non-negative, summing to `1`), the
Herfindahl–Hirschman Index is

  `HHI(w) := Σ_i w_i²`.

Properties:
* **Bounds**: `1/n ≤ HHI ≤ 1`.
* **Lower bound by Cauchy-Schwarz**: from `(Σ wᵢ)² ≤ n · Σ wᵢ²` with `Σ wᵢ = 1`.
* **Upper bound**: `wᵢ² ≤ wᵢ` when `0 ≤ wᵢ ≤ 1`, so `Σ wᵢ² ≤ Σ wᵢ ≤ 1`.

The "effective number of assets" is `n_eff := 1/HHI ∈ [1, n]`, ranging from
full concentration (`n_eff = 1`) to full diversification (`n_eff = n`).

Results:

* `herfindahl`: `Σ w_i²`.
* `herfindahl_nonneg`: HHI ≥ 0.
* `herfindahl_le_one_of_sum_le_one_of_nonneg`: HHI ≤ 1 under unit budget.
* `herfindahl_card_inv_le_of_sum_one`: HHI ≥ 1/n via Cauchy-Schwarz.
-/

@[expose] public section

namespace MathFin

open Finset

variable {ι : Type*}

/-- Herfindahl–Hirschman Index: `HHI(w) := Σ w_i²`. -/
noncomputable def herfindahl (s : Finset ι) (w : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (w i)^2

/-- **Non-negativity**: `HHI ≥ 0`. -/
lemma herfindahl_nonneg (s : Finset ι) (w : ι → ℝ) :
    0 ≤ herfindahl s w := by
  unfold herfindahl
  apply Finset.sum_nonneg
  intros i _
  exact sq_nonneg _

/-- **Upper bound HHI ≤ 1** when weights are in `[0,1]` and `Σ w ≤ 1`. -/
lemma herfindahl_le_one_of_sum_le_one_of_nonneg
    (s : Finset ι) (w : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ w i) (hw_le : ∀ i ∈ s, w i ≤ 1)
    (h_sum : ∑ i ∈ s, w i ≤ 1) :
    herfindahl s w ≤ 1 := by
  unfold herfindahl
  -- `w²≤w` for `w∈[0,1]` is exactly `pow_le_of_le_one` (patterns.md flagged
  -- this goal as needing `nlinarith`; the direct Mathlib lemma supersedes it).
  have h_bound : ∀ i ∈ s, (w i)^2 ≤ w i := fun i hi =>
    pow_le_of_le_one (hnn i hi) (hw_le i hi) (by norm_num)
  calc ∑ i ∈ s, (w i)^2
      ≤ ∑ i ∈ s, w i := Finset.sum_le_sum h_bound
    _ ≤ 1 := h_sum

/-- **Cauchy-Schwarz lower bound HHI ≥ 1/n** under unit-budget constraint. -/
lemma herfindahl_card_inv_le_of_sum_one (s : Finset ι) (w : ι → ℝ)
    (hs : s.Nonempty) (h_sum : ∑ i ∈ s, w i = 1) :
    (s.card : ℝ)⁻¹ ≤ herfindahl s w := by
  unfold herfindahl
  -- Mathlib's Cauchy–Schwarz card form, exactly this statement.
  have h_cs : (∑ i ∈ s, w i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (w i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [h_sum, one_pow] at h_cs
  -- h_cs : 1 ≤ s.card * ∑ wᵢ²
  have h_card_pos : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  rw [inv_le_iff_one_le_mul₀ h_card_pos]
  linarith

end MathFin
