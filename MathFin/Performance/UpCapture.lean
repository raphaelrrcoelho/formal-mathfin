/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

-- pointers: MathFin/Performance/RatiosExtended.lean
-- main-module: MathFin/Performance/UpCapture.lean
-- benchmark: benchmarks/mathematical_finance.json
-- benchmark-id: mf-performance-upside_capture
-- source-issue: 162
-- new-defs: upCapture

/-!
Upside-capture ratio and its homogeneity in portfolio returns.
-/

set_option autoImplicit false

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Upside-capture ratio: sum of portfolio returns over up periods divided by sum of benchmark returns over up periods. -/
noncomputable def upCapture {S : Type*} (up : Finset S) (p : S → ℝ) (b : S → ℝ) : ℝ :=
  (∑ s ∈ up, p s) / (∑ s ∈ up, b s)

theorem upCapture_scale_invariant {S : Type*} (up : Finset S) (p b : S → ℝ) (c : ℝ)
    (h : (∑ s ∈ up, b s) ≠ 0) : upCapture up (fun s => c * p s) b = c * upCapture up p b := by
  unfold upCapture
  field_simp [h]
  simp [Finset.mul_sum]

end MathFin
