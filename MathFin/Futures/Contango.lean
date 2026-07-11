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
  have h_cancel_lt : S < S * Real.exp ((r - δ) * T) ↔ 1 < Real.exp ((r - δ) * T) := by
    constructor
    · intro h
      have : S * 1 < S * Real.exp ((r - δ) * T) := by simpa [mul_one] using h
      exact lt_of_mul_lt_mul_left this hS.le
    · intro h
      have : S * 1 < S * Real.exp ((r - δ) * T) := mul_lt_mul_of_pos_left h hS
      simpa [mul_one] using this
  have h_cancel_gt : S * Real.exp ((r - δ) * T) < S ↔ Real.exp ((r - δ) * T) < 1 := by
    constructor
    · intro h
      have : S * Real.exp ((r - δ) * T) < S * 1 := by simpa [mul_one] using h
      exact lt_of_mul_lt_mul_left this hS.le
    · intro h
      have : S * Real.exp ((r - δ) * T) < S * 1 := mul_lt_mul_of_pos_left h hS
      simpa [mul_one] using this
  refine ⟨?_, ?_, ?_⟩
  · rw [h_cancel_lt, ← Real.exp_zero, Real.exp_lt_exp]
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  · rw [h_cancel_gt, ← Real.exp_zero, Real.exp_lt_exp]
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  · simp
