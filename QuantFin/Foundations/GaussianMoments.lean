/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Gaussian moments

Small, shared moment facts for real Gaussians used across the Brownian-motion
foundations (`BrownianMartingale`, `BrownianQuadraticVariation`). Kept in one
place so each identity is proved exactly once.
-/

@[expose] public section

namespace QuantFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Second moment of a centered real Gaussian: `∫ x, x² ∂(gaussianReal 0 v) = v`.
For a mean-zero law the second moment is the variance (`variance_id_gaussianReal`). -/
lemma integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h_var : variance id (gaussianReal 0 v) = (v : ℝ) := variance_id_gaussianReal
  have h_mean : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  rw [variance_of_integral_eq_zero aemeasurable_id h_mean] at h_var
  exact h_var

end QuantFin
