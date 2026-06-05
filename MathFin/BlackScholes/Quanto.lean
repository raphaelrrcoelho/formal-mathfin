/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.Dividends

/-!
# Quanto correction — re-export

The quanto-correction content (the quanto-adjusted forward and the correction
factor `exp(−ρ σ_S σ_FX T)`) has been folded into `BlackScholes/Dividends.lean`,
alongside Garman-Kohlhagen — both are foreign/dividend drift-adjustment
variants of the same BS pricing formula.

The namespace `MathFin` exposes `quantoForward` and
`quanto_correction_factor` through the transitive import.
-/

@[expose] public section
