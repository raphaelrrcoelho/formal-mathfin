/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

-- pointers: MathFin/Performance/RatiosExtended.lean
-- main-module: MathFin/Performance/GainToPain.lean
-- benchmark: benchmarks/mathematical_finance.json
-- benchmark-id: mf-performance-gain_to_pain
-- source-issue: 161
-- new-defs: gainToPain

/-!
Gain-to-pain ratio is nonnegative when defined.
-/

set_option autoImplicit false

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open scoped BigOperators

/-- The gain-to-pain ratio is the sum of positive returns over the sum of absolute negative returns. -/
noncomputable def gainToPain {α : Type*} (S : Finset α) (r : α → ℝ) : ℝ :=
  (∑ s ∈ S, max (r s) 0) / (∑ s ∈ S, max (-(r s)) 0)

/-- If the sum of absolute negative returns is positive, then the gain-to-pain ratio is nonnegative. -/
theorem gainToPain_nonneg_of_pain_pos {α : Type*} (S : Finset α) (r : α → ℝ)
    (h : 0 < ∑ s ∈ S, max (-(r s)) 0) : 0 ≤ gainToPain S r := by
  have hnum : 0 ≤ ∑ s ∈ S, max (r s) 0 :=
    Finset.sum_nonneg fun s _ => le_max_right _ _
  have hden : 0 ≤ ∑ s ∈ S, max (-(r s)) 0 := h.le
  exact div_nonneg hnum hden

end MathFin
