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
  rw [cellExp, min_eq_right (zero_le : (0:ℝ≥0) ≤ b), min_eq_right (zero_le : (0:ℝ≥0) ≤ a)]; simp

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

/-- **The simple (piecewise-constant adapted) drift** `∑_{i<N} c_i · (s_{i+1}∧t − s_i∧t)`, clamped
to `[0,t]`: the drift added to `X` to form the simple-θ Girsanov process `B^θ_t = X_t + drift_t`.
Each cell contributes `c_i` times the length of its clamped time-interval. -/
noncomputable def simpleDrift (s : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N,
    c i ω * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t))

/-- **Log-form of the simple Doléans exponential.** `simpleDoleansExp s d N t = exp(∑_{i<N}
[d_i·(X_{s_{i+1}∧t} − X_{s_i∧t}) − ½ d_i²·(s_{i+1}∧t − s_i∧t)])`: the product of cell exponentials
is a single exponential of a sum, so the Girsanov spine becomes one exponent identity. -/
lemma simpleDoleansExp_eq_exp_sum (s : ℕ → ℝ≥0) (d : ℕ → Ω → ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    simpleDoleansExp (X := X) s d N t ω
      = Real.exp (∑ i ∈ Finset.range N,
          (d i ω * (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
            - (d i ω) ^ 2
                * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) / 2)) := by
  induction N with
  | zero => simp [simpleDoleansExp]
  | succ n ih =>
    show simpleDoleansExp (X := X) s d n t ω * cellExp (X := X) (s n) (s (n + 1)) (d n) t ω = _
    rw [ih, cellExp, ← Real.exp_add, Finset.sum_range_succ]

/-- **The simple Girsanov spine.** `Z_t · exp(a·B^θ_t − ½a²t) = exp(a·X_0) · E^{a−c}_t`, where the
density `Z = E^{−c}` and the tilted density `E^{a−c}` are simple Doléans exponentials, and
`B^θ_t = X_t + simpleDrift_t`. This is the "`Z·D` is another exponential density" trick for simple
θ: the per-cell exponents `(−c_i)ΔX_i − ½c_i²Δτ_i` and `a·ΔX_i + a·c_i·Δτ_i − ½a²Δτ_i` combine to
`(a−c_i)ΔX_i − ½(a−c_i)²Δτ_i`, the `a−c` cell. Needs the partition to cover `[0,t]`
(`s_0 = 0`, `t ≤ T ≤ s_N`), so the increments telescope to `X_t − X_0` and `t`. Combined with
`X_0 = 0` a.e. it gives `Z·D =ᵐ E^{a−c}`. -/
lemma simple_spine (s : ℕ → ℝ≥0) (hs0 : s 0 = 0) (c : ℕ → Ω → ℝ) (a : ℝ) (N : ℕ)
    {t T : ℝ≥0} (htT : t ≤ T) (hNT : T ≤ s N) (ω : Ω) :
    simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N t ω
        * Real.exp (a * (X t ω + simpleDrift s c N t ω) - a ^ 2 * (t : ℝ) / 2)
      = Real.exp (a * X 0 ω)
        * simpleDoleansExp (X := X) s (fun i ω ↦ a - c i ω) N t ω := by
  rw [simpleDoleansExp_eq_exp_sum, simpleDoleansExp_eq_exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have htN : min (s N) t = t := min_eq_right (htT.trans hNT)
  have h0t : min (s 0) t = 0 := by rw [hs0]; exact min_eq_left (zero_le : (0 : ℝ≥0) ≤ t)
  have hβX : ∑ i ∈ Finset.range N, (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
      = X t ω - X 0 ω := by
    rw [Finset.sum_range_sub (fun i ↦ X (min (s i) t) ω) N, htN, h0t]
  have hβτ : ∑ i ∈ Finset.range N,
      (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) = (t : ℝ) := by
    rw [Finset.sum_range_sub (fun i ↦ NNReal.toReal (min (s i) t)) N, htN, h0t]; simp
  have key :
      (∑ i ∈ Finset.range N,
          ((a - c i ω) * (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
            - (a - c i ω) ^ 2
                * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) / 2))
        - (∑ i ∈ Finset.range N,
          ((-(c i ω)) * (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
            - (-(c i ω)) ^ 2
                * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) / 2))
      = a * (X t ω - X 0 ω) + a * simpleDrift s c N t ω - a ^ 2 * (t : ℝ) / 2 := by
    rw [← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun i _ ↦ show
        ((a - c i ω) * (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
            - (a - c i ω) ^ 2
                * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) / 2)
          - ((-(c i ω)) * (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
            - (-(c i ω)) ^ 2
                * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) / 2)
        = a * (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
            + a * (c i ω * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)))
            - a ^ 2 / 2 * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t))
        from by ring),
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hβX, hβτ]
    simp only [simpleDrift]; ring
  linear_combination -key

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
  have hmean := hmart.setIntegral_eq (i := 0) (j := T) (zero_le : (0:ℝ≥0) ≤ T) (s := Set.univ) MeasurableSet.univ
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

/-- **Adaptedness of the simple drift.** `simpleDrift s c N u` is `𝓕_u`-measurable when the
multipliers are adapted (`c i` is `𝓕_{s i}`-measurable): each cell contributes
`c_i · (s_{i+1}∧u − s_i∧u)`, and either `s_i ≤ u` (so `c_i` is `𝓕_u`-measurable) or `u ≤ s_i`
(so the clamped interval length is `0`). -/
lemma stronglyMeasurable_simpleDrift {s : ℕ → ℝ≥0} (hs : Monotone s) {c : ℕ → Ω → ℝ}
    (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) (N : ℕ) (u : ℝ≥0) :
    StronglyMeasurable[(𝓕 u : MeasurableSpace Ω)] (fun ω ↦ simpleDrift s c N u ω) := by
  have hfun : (fun ω ↦ simpleDrift s c N u ω)
      = ∑ i ∈ Finset.range N,
          (fun ω ↦ c i ω * (NNReal.toReal (min (s (i + 1)) u) - NNReal.toReal (min (s i) u))) := by
    funext ω; simp only [simpleDrift, Finset.sum_apply]
  rw [hfun]
  apply Finset.stronglyMeasurable_sum
  intro i _
  rcases le_total (s i) u with hiu | hui
  · exact ((hc i).mono (𝓕.mono hiu)).mul_const _
  · have hτ : NNReal.toReal (min (s (i + 1)) u) - NNReal.toReal (min (s i) u) = 0 := by
      rw [min_eq_right (hui.trans (hs (Nat.le_succ i))), min_eq_right hui]; ring
    simp only [hτ, mul_zero]
    exact stronglyMeasurable_const

omit [IsProbabilityMeasure P] [SigmaFiniteFiltration P 𝓕] in
include hX in
/-- **The simple Girsanov spine, a.e. form.** For a partition covering `[0,t]` (`s_0 = 0`,
`t ≤ T ≤ s_N`), the product of the density `Z = E^{−c}` and the drift-corrected exponential
`exp(a·B^θ_t − ½a²t)` is a.e. equal to the tilted simple Doléans exponential `E^{a−c}_t` — because
`X_0 = 0` a.e. `P` kills the `exp(a·X_0)` factor of `simple_spine`. This is the "`Z·D` is another
exponential density" identity that will feed the Bayes change-of-measure engine, exactly as
`Wald(−θ)·Wald(a)` collapses to `Wald(a−θ)` in the constant-θ file. -/
theorem simple_spine_ae (s : ℕ → ℝ≥0) (hs0 : s 0 = 0) (c : ℕ → Ω → ℝ) (a : ℝ) (N : ℕ)
    {t T : ℝ≥0} (htT : t ≤ T) (hNT : T ≤ s N) :
    (fun ω ↦ simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N t ω
        * Real.exp (a * (X t ω + simpleDrift s c N t ω) - a ^ 2 * (t : ℝ) / 2))
      =ᵐ[P] fun ω ↦ simpleDoleansExp (X := X) s (fun i ω ↦ a - c i ω) N t ω := by
  have hX0 : ∀ᵐ ω ∂P, X 0 ω = 0 := by
    have hmeasX0 : Measurable (X 0) := ((hX.stronglyAdapted 0).mono (𝓕.le 0)).measurable
    have hmap := Measure.map_apply (μ := P) hmeasX0 (measurableSet_singleton (0 : ℝ)).compl
    rw [(hX.hasLaw_eval 0).map_eq, gaussianReal_zero_var,
        Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl] at hmap
    have hpre : X 0 ⁻¹' {(0 : ℝ)}ᶜ = {ω | X 0 ω ≠ 0} := by ext ω; simp [Set.mem_preimage]
    rw [hpre] at hmap
    exact ae_iff.mpr (by simpa using hmap.symm)
  filter_upwards [hX0] with ω hω
  rw [simple_spine s hs0 c a N htT hNT ω, hω, mul_zero, Real.exp_zero, one_mul]

end MathFin
