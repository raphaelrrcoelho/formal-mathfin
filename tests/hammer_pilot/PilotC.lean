import Mathlib
import Hammer

/-! # Hammer pilot C — premise lookup + stretch goals -/

open Lean.LibrarySuggestions in
set_library_suggestions sineQuaNonSelector.intersperse currentFile

open MeasureTheory ProbabilityTheory

-- C1 [CoherentAxioms] the full sqrt lemma; we wrote: sqrt_le_sqrt + sqrt_sq + nlinarith
example (σ₁ σ₂ ρ : ℝ) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) (hρ : ρ ≤ 1) :
    Real.sqrt (σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2) ≤ σ₁ + σ₂ := by hammer

-- C2 [BrownianQuadraticVariation] limit; we wrote: funext rewrite + tendsto algebra
example (t : ℝ) : Filter.Tendsto (fun n : ℕ => (n : ℝ) * t / ((n : ℝ) + 1))
    Filter.atTop (nhds t) := by hammer

-- C3 [FeynmanKac] abs bound; we wrote: abs_le + constructor <;> nlinarith
example (y s t : ℝ) (ht : 0 < t) (hs_lo : t / 2 < s) (hs_hi : s ≤ 3 * t / 2) :
    |y ^ 2 - s| ≤ y ^ 2 + 3 * t / 2 := by hammer

-- C4 sanity: payoff nonnegativity
example (S K : ℝ) : 0 ≤ max (S - K) 0 := by hammer

-- C5 [StandardNormal-shape] Gaussian mean lookup
example : ∫ x, x ∂(gaussianReal 0 1) = 0 := by hammer
