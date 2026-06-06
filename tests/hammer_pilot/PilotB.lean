import Mathlib
import Hammer

/-! # Hammer pilot B — measure-theory side-goals (the authoring tax) -/

open Lean.LibrarySuggestions in
set_library_suggestions sineQuaNonSelector.intersperse currentFile

open MeasureTheory

-- B1 [ItoProcessQV] integrability transport; we wrote: hE2_int.const_mul 3
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f : Ω → ℝ)
    (hf : Integrable f μ) : Integrable (fun ω => 3 * f ω) μ := by hammer

-- B2 [GaussianGirsanov-shape] measurability of exp-affine
example (σ : ℝ) : Measurable (fun x : ℝ => Real.exp (σ * x - σ ^ 2 / 2)) := by hammer

-- B3 [ItoProcessQV] MemLp → Integrable of the square; we wrote: this.integrable_sq
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f : Ω → ℝ)
    (hf : MemLp f 2 μ) : Integrable (fun ω => f ω ^ 2) μ := by hammer

-- B4 [Concentration] pointwise sum bound; we wrote: Finset.sum_le_sum
example {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by hammer

-- B5 [FeynmanKac] exp/div composite; we wrote: exp_le_exp.mpr + div_le_div_iff₀ + nlinarith
example (y s t : ℝ) (ht : 0 < t) (hs_lo : t / 2 < s) (hs_hi : s ≤ 3 * t / 2) :
    Real.exp (-(y ^ 2) / (2 * s)) ≤ Real.exp (-(y ^ 2) / (3 * t)) := by hammer
