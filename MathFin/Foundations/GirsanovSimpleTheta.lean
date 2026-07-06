/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.SimpleDoleansExponential
public import MathFin.Foundations.EquivMeasure

/-!
# Simple (piecewise-constant adapted) Girsanov — the density measure

Route-α, brick α3 (`docs/plans/2026-07-06-girsanov-track-alpha.md`). For a market price of risk
`θ` that is **simple** (piecewise-constant adapted) over a partition `s : ℕ → ℝ≥0`, the Girsanov
density is the simple Doléans exponential `Z_T = simpleDoleansExp s d N T` (`d = −c` the drift
multipliers). Since `Z` is a `P`-martingale (`simpleDoleansExp_isMartingale`, α2), positive, and
starts at `1`, its `P`-mean is `1`, so `Q = P.withDensity Z_T` is a probability measure — the
foundation on which the drift-corrected process `B^θ` is shown to be a `Q`-Brownian motion.

This file lands the measure-side foundation:
* `MathFin.simpleDoleansExp_zero`, `simpleDoleansExp_pos` — the density is `1` at `t = 0` and
  strictly positive;
* `MathFin.simpleDoleansExp_integral_eq_one` — unit `P`-mean, from the martingale property;
* `MathFin.simpleGirsanovMeasure_isProbabilityMeasure` — `Q = P.withDensity Z_T` is a probability
  measure.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ}

/-- Every cell factor is `1` at time `0` (both clamped endpoints collapse to `0`). -/
lemma cellExp_zero (a b : ℝ≥0) (c : Ω → ℝ) (ω : Ω) : cellExp (X := X) a b c 0 ω = 1 := by
  rw [cellExp, min_eq_right (zero_le' : (0:ℝ≥0) ≤ b), min_eq_right (zero_le' : (0:ℝ≥0) ≤ a)]; simp

/-- The simple Doléans exponential is `1` at time `0`. -/
lemma simpleDoleansExp_zero (s : ℕ → ℝ≥0) (d : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    simpleDoleansExp (X := X) s d N 0 ω = 1 := by
  induction N with
  | zero => rfl
  | succ n ih =>
    show simpleDoleansExp (X := X) s d n 0 ω * cellExp (X := X) (s n) (s (n + 1)) (d n) 0 ω = 1
    rw [ih, cellExp_zero, mul_one]

/-- The simple Doléans exponential is strictly positive (a product of exponentials). -/
lemma simpleDoleansExp_pos (s : ℕ → ℝ≥0) (d : ℕ → Ω → ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    0 < simpleDoleansExp (X := X) s d N t ω := by
  induction N with
  | zero => exact one_pos
  | succ n ih =>
    show 0 < simpleDoleansExp (X := X) s d n t ω * cellExp (X := X) (s n) (s (n + 1)) (d n) t ω
    exact mul_pos ih (Real.exp_pos _)

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  [SigmaFiniteFiltration P 𝓕] [hX : IsFilteredPreBrownian X 𝓕 P]

include hX in
/-- **Unit `P`-mean of the density.** `∫ Z_T dP = 1`: the martingale property equates the mean at
`T` with the mean at `0`, where `Z_0 = 1`. -/
theorem simpleDoleansExp_integral_eq_one (s : ℕ → ℝ≥0) (hs : Monotone s) (d : ℕ → Ω → ℝ)
    (hd : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (d i)) {K : ℝ}
    (hd_bdd : ∀ i ω, |d i ω| ≤ K) (N : ℕ) (T : ℝ≥0) :
    ∫ ω, simpleDoleansExp (X := X) s d N T ω ∂P = 1 := by
  have hmart := simpleDoleansExp_isMartingale (X := X) (P := P) s hs d hd hd_bdd N
  have hmean := hmart.setIntegral_eq (i := 0) (j := T) (zero_le' : (0:ℝ≥0) ≤ T) (s := Set.univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at hmean
  calc ∫ ω, simpleDoleansExp (X := X) s d N T ω ∂P
      = ∫ ω, simpleDoleansExp (X := X) s d N 0 ω ∂P := hmean.symm
    _ = ∫ _, (1 : ℝ) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ simpleDoleansExp_zero s d N ω)
    _ = 1 := by simp

include hX in
/-- **The simple Girsanov measure is a probability measure.** `Q = P.withDensity Z_T` with the
positive, unit-mean simple Doléans density `Z_T`. -/
theorem simpleGirsanovMeasure_isProbabilityMeasure (s : ℕ → ℝ≥0) (hs : Monotone s) (d : ℕ → Ω → ℝ)
    (hd : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (d i)) {K : ℝ}
    (hd_bdd : ∀ i ω, |d i ω| ≤ K) (N : ℕ) (T : ℝ≥0) :
    IsProbabilityMeasure
      (P.withDensity fun ω ↦ ENNReal.ofReal (simpleDoleansExp (X := X) s d N T ω)) := by
  have hmart := simpleDoleansExp_isMartingale (X := X) (P := P) s hs d hd hd_bdd N
  have hZmeas : Measurable (fun ω ↦ simpleDoleansExp (X := X) s d N T ω) :=
    ((hmart.1 T).mono (𝓕.le T)).measurable
  exact (isEquivProbMeasure_withDensity P hZmeas (fun ω ↦ simpleDoleansExp_pos s d N T ω)
    (hmart.integrable T) (simpleDoleansExp_integral_eq_one s hs d hd hd_bdd N T)).1

end MathFin
