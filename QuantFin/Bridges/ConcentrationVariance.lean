/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.RiskMeasures.Concentration
import QuantFin.Portfolio.MarkowitzNAsset

/-!
# Bridge: concentration is diversifiable variance

For independent assets of common variance `σ²`, the N-asset Markowitz portfolio
variance equals `σ²` times the Herfindahl–Hirschman concentration index. This
ties `RiskMeasures/Concentration.lean` to `Portfolio/MarkowitzNAsset.lean`: the
diversifiable part of portfolio variance *is* the concentration metric. A
certified unification of two known textbook facts — not new finance.
-/

namespace QuantFin

/-- **Concentration ✕ variance bridge.** Diagonal covariance with common
variance `σ_sq` ⇒ `Var(w) = σ_sq · HHI(w)`. -/
theorem portfolioVarN_diag_eq_herfindahl {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w : ι → ℝ) (σ : ι → ι → ℝ) (σ_sq : ℝ)
    (h_diag : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → σ i j = 0)
    (h_var : ∀ i ∈ s, σ i i = σ_sq) :
    portfolioVarN s w σ = σ_sq * herfindahl s w := by
  rw [portfolioVarN_diag s w σ h_diag]
  unfold herfindahl
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [h_var i hi]; ring

end QuantFin
