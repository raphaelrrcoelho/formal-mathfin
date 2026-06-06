import Mathlib
import Hammer

/-! # Hammer pilot A — algebra / inequalities (real corpus goals)
Privacy: LOCAL premise selection only (sineQuaNon symbolic selector);
no goal context leaves the machine. -/

open Lean.LibrarySuggestions in
set_library_suggestions sineQuaNonSelector.intersperse currentFile

-- A1 [RiskParity] field identity; we wrote: rw-normalize; field_simp; ring
example (σ₁ σ₂ : ℝ) (hσ : σ₁ + σ₂ ≠ 0) :
    σ₂ / (σ₁ + σ₂) + σ₁ / (σ₂ + σ₁) = 1 := by hammer {disableGrind := true}

-- A2 [Concentration] w² ≤ w on [0,1]; we wrote: nlinarith [sq_nonneg w]
example (w : ℝ) (h0 : 0 ≤ w) (h1 : w ≤ 1) : w ^ 2 ≤ w := by hammer {disableGrind := true}

-- A3 [CoherentAxioms] joint-stdev core; we wrote: nlinarith [mul_nonneg ...]
example (σ₁ σ₂ ρ : ℝ) (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) (hρ : ρ ≤ 1) :
    σ₁ ^ 2 + 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2 ≤ (σ₁ + σ₂) ^ 2 := by hammer {disableGrind := true}

-- A4 [BrownianQuadraticVariation] division monotone; we wrote: div_le_div_iff_of_pos_right + nlinarith
example (t : ℝ) (ht : 0 ≤ t) (n k : ℕ) :
    (k : ℝ) * t / ((n : ℝ) + 1) ≤ ((k : ℝ) + 1) * t / ((n : ℝ) + 1) := by hammer {disableGrind := true}

-- A5 [ItoProcessQV] ℕ-cast nonlinear; we wrote: nlinarith (grind also fails this)
example (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by hammer {disableGrind := true}
