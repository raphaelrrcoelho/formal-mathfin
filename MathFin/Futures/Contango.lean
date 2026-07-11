/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

-- pointers: MathFin/BlackScholes/Dividends.lean, MathFin/BlackScholes/Forward.lean
-- main-module: MathFin/Futures/Contango.lean
-- benchmark: benchmarks/mathematical_finance.json
-- benchmark-id: mf-futures-contango
-- source-issue: 88

/-!
# Contango, backwardation, and basis convergence

The no-arbitrage forward with a carry / convenience yield `δ` is
`F(T) = S · exp((r − δ)·T)` (the dividend-yield forward of `BlackScholes/Dividends`,
where the convenience yield plays the role of a continuous dividend). This records
the qualitative cost-of-carry sign structure: the market is in **contango**
(`F > S`) exactly when `r > δ`, in **backwardation** (`F < S`) exactly when
`r < δ`, and the **basis** `S − F` vanishes at `T = 0`. Pure `Real.exp`
monotonicity in the effective drift `r − δ`.
-/

@[expose] public section

namespace MathFin

/-- Cost-of-carry sign structure for the forward `F(T) = S · exp((r − δ)·T)`:
contango `F > S ↔ r > δ`, backwardation `F < S ↔ r < δ`, and basis convergence
`F(0) = S`. -/
theorem contango_backwardation_basis
    {S r δ T : ℝ} (hS : 0 < S) (hT : 0 < T) :
    (S < S * Real.exp ((r - δ) * T) ↔ δ < r) ∧
    (S * Real.exp ((r - δ) * T) < S ↔ r < δ) ∧
    S * Real.exp ((r - δ) * 0) = S := by
  have h_third : S * Real.exp ((r - δ) * 0) = S := by simp
  have h_first : (S < S * Real.exp ((r - δ) * T) ↔ δ < r) := by
    constructor
    · intro h
      have h_one_lt_exp : 1 < Real.exp ((r - δ) * T) := by
        by_contra hle
        push_neg at hle
        have hle' : S * Real.exp ((r - δ) * T) ≤ S := by
          calc
            S * Real.exp ((r - δ) * T) ≤ S * 1 := mul_le_mul_of_nonneg_left hle (by linarith)
            _ = S := by ring
        linarith
      have h_mul_pos : 0 < (r - δ) * T := by
        have h_exp_lt : Real.exp 0 < Real.exp ((r - δ) * T) := by
          simpa [Real.exp_zero] using h_one_lt_exp
        exact Real.exp_lt_exp.mp h_exp_lt
      have h_r_gt_delta : 0 < r - δ := by
        nlinarith
      linarith
    · intro h
      have h_r_gt_delta : 0 < r - δ := by linarith
      have h_mul_pos : 0 < (r - δ) * T := by nlinarith
      have h_exp_lt : Real.exp 0 < Real.exp ((r - δ) * T) := Real.exp_lt_exp.mpr h_mul_pos
      have h_one_lt_exp : 1 < Real.exp ((r - δ) * T) := by simpa [Real.exp_zero] using h_exp_lt
      calc
        S = S * 1 := by ring
        _ < S * Real.exp ((r - δ) * T) := mul_lt_mul_of_pos_left h_one_lt_exp hS
  have h_second : (S * Real.exp ((r - δ) * T) < S ↔ r < δ) := by
    constructor
    · intro h
      have h_exp_lt_one : Real.exp ((r - δ) * T) < 1 := by
        by_contra hle
        push_neg at hle
        have hle' : S ≤ S * Real.exp ((r - δ) * T) := by
          calc
            S = S * 1 := by ring
            _ ≤ S * Real.exp ((r - δ) * T) := mul_le_mul_of_nonneg_left hle (by linarith)
        linarith
      have h_mul_neg : (r - δ) * T < 0 := by
        have h_exp_lt : Real.exp ((r - δ) * T) < Real.exp 0 := by
          simpa [Real.exp_zero] using h_exp_lt_one
        exact Real.exp_lt_exp.mp h_exp_lt
      have h_r_lt_delta : r - δ < 0 := by
        nlinarith
      linarith
    · intro h
      have h_r_lt_delta : r - δ < 0 := by linarith
      have h_mul_neg : (r - δ) * T < 0 := by nlinarith
      have h_exp_lt : Real.exp ((r - δ) * T) < Real.exp 0 := Real.exp_lt_exp.mpr h_mul_neg
      have h_exp_lt_one : Real.exp ((r - δ) * T) < 1 := by simpa [Real.exp_zero] using h_exp_lt
      calc
        S * Real.exp ((r - δ) * T) < S * 1 := mul_lt_mul_of_pos_left h_exp_lt_one hS
        _ = S := by ring
  exact ⟨h_first, h_second, h_third⟩

end MathFin
