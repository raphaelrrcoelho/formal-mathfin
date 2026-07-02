/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.DriftProcessPredictable

/-! # SDE existence/uniqueness via Picard on `E` (build)

The strong solution of `dX = b(X)dt + σ(X)dB`, `X₀ = η` is the fixed point of the
Picard iterate `Φ(X)_t = η + ∫₀ᵗ b(X_s) ds + ∫₀ᵗ σ(X_s) dB_s`, built as a self-map of
the predictable `L²` space `E := Lp ℝ 2 (trimMeasure_T T)`. Both analytic terms already land
back in `E` — the drift as a genuine CLM `driftProcessAssembled : E →L[ℝ] E`, the Itô term as the
element-valued linear map `itoProcessAssembled : E → E` (built from a continuous modification, so
*not* a CLM — its linearity is re-established a.e.). This file wires them into the Picard map, proves
the contraction estimate `‖Φ(X) − Φ(Y)‖ ≤ (T·L_b + √T·L_σ)·‖X − Y‖`, and — when that constant is
`< 1` — obtains the **unique fixed point** (`picardSolution`) via Banach's theorem: existence and
uniqueness of the strong solution in `E`.

The `T` vs `√T` asymmetry is structural: both terms integrate a `[0,t]` quantity over `t ∈ [0,T]`,
but Cauchy–Schwarz already spends a factor of time inside each drift slice (leaving the full `T`),
whereas the Itô isometry bounds each `[0,t]` energy flatly by the total energy (so only `√T`
survives the outer time-integral). The `driftProcessAssembled_norm_le` (`≤ T‖·‖`) and
`itoProcessAssembled_norm_le` (`≤ √T‖·‖`) bounds live with their operators in
`DriftProcessPredictable` / `ItoProcessPredictable`.

* `lipComp` — the coefficient composition `f ∘ X ∈ E` (centered via `lipschitz_sub_const`);
  `lipComp_sub_norm_le` — its `L`-Lipschitz bound.
* `picardMap` — the Picard iterate `Φ : E → E`.
* `picardMap_contraction` — the contraction estimate; `picardMap_contractingWith` — as `ContractingWith`.
* `picardSolution` — the strong solution (the fixed point); `picardMap_exists_unique_fixedPoint` — `∃!`.

The remaining bridge to the benchmark `sc-thm-8.2.5` (its `ℝ`-time, pointwise-per-`t`,
`intervalIntegral`-drift, opaque-`Iσ` shape) and the all-`T` extension (a Bielecki weighted
norm) are the next steps.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace SDEExistence
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral
  ItoIntegralProcessContinuousModification

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- Centering a Lipschitz coefficient at `0`: `x ↦ f x − f 0` is `L`-Lipschitz and
sends `0 ↦ 0`, so it composes with an `L²` process via `LipschitzWith.compLp`. -/
theorem lipschitz_sub_const {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (fun x => f x - f 0) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hf.dist_le_mul x y

/-- **The coefficient composition** `f ∘ X ∈ E` for a Lipschitz `f : ℝ → ℝ` and a
predictable process `X ∈ E`: `f(0)·1 + (f − f 0)∘X`. The centered part lands in `E` by
`compLp` (predictability is inherited from `E`'s trim measure); the constant `f 0` is
added back as a genuine element of `E` (finite measure). -/
noncomputable def lipComp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (f : ℝ → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f)
    (X : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  Lp.const 2 _ (f 0) + (lipschitz_sub_const hf).compLp (by simp) X

/-- **The composition is `L`-Lipschitz in `X`** — the constant `f 0` cancels in the
difference, and `LipschitzWith.norm_compLp_sub_le` bounds the centered part. This is the
per-coefficient Lipschitz factor of the Picard contraction. -/
theorem lipComp_sub_norm_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (X Y : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ‖lipComp T hBmeas f L hf X - lipComp T hBmeas f L hf Y‖ ≤ (L : ℝ) * ‖X - Y‖ := by
  rw [lipComp, lipComp, add_sub_add_left_eq_sub]
  exact (lipschitz_sub_const hf).norm_compLp_sub_le (by simp) X Y

/-- **The Picard iterate** `Φ(X) = η + driftProcessAssembled(b∘X) + itoProcessAssembled(σ∘X)`,
a self-map of `E`. Its fixed point is the strong solution of the SDE. -/
noncomputable def picardMap (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (X : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  η_E + driftProcessAssembled T hBmeas (lipComp T hBmeas b Lb hb X)
      + itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ X)

/-- **The Picard contraction estimate** `‖Φ(X) − Φ(Y)‖ ≤ (T·L_b + √T·L_σ)·‖X − Y‖`. The
initial condition cancels in the difference; the drift term contributes `T·L_b` (operator
bound `T` × Lipschitz `L_b`), the Itô term `√T·L_σ` (operator bound `√T` × Lipschitz `L_σ`).
For `T` small this constant is `< 1`, giving a contraction. -/
theorem picardMap_contraction (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E X Y : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ‖picardMap hB T hBmeas hBcont hb hσ η_E X - picardMap hB T hBmeas hBcont hb hσ η_E Y‖
      ≤ ((T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ) * ‖X - Y‖ := by
  have hdrift : driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb X)
      - driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb Y)
      = driftProcessAssembled (μ := μ) T hBmeas
          (lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y) :=
    (map_sub (driftProcessAssembled (μ := μ) T hBmeas) _ _).symm
  have hito : itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ X)
      - itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ Y)
      = itoProcessAssembled hB T hBmeas hBcont
          (lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y) :=
    (itoProcessAssembled_sub hB T hBmeas hBcont _ _).symm
  have hdecomp :
      picardMap hB T hBmeas hBcont hb hσ η_E X - picardMap hB T hBmeas hBcont hb hσ η_E Y
        = driftProcessAssembled (μ := μ) T hBmeas
            (lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y)
          + itoProcessAssembled hB T hBmeas hBcont
            (lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y) := by
    rw [picardMap, picardMap, ← hdrift, ← hito]; abel
  rw [hdecomp]
  calc ‖driftProcessAssembled (μ := μ) T hBmeas
            (lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y)
          + itoProcessAssembled hB T hBmeas hBcont
            (lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y)‖
      ≤ ‖driftProcessAssembled (μ := μ) T hBmeas
            (lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y)‖
        + ‖itoProcessAssembled hB T hBmeas hBcont
            (lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y)‖ := norm_add_le _ _
    _ ≤ (T : ℝ) * ‖lipComp T hBmeas b Lb hb X - lipComp T hBmeas b Lb hb Y‖
        + Real.sqrt (T : ℝ) * ‖lipComp T hBmeas σ Lσ hσ X - lipComp T hBmeas σ Lσ hσ Y‖ :=
        add_le_add (driftProcessAssembled_norm_le T hBmeas _)
          (itoProcessAssembled_norm_le hB T hBmeas hBcont _)
    _ ≤ (T : ℝ) * ((Lb : ℝ) * ‖X - Y‖) + Real.sqrt (T : ℝ) * ((Lσ : ℝ) * ‖X - Y‖) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (lipComp_sub_norm_le T hBmeas hb X Y) T.coe_nonneg)
          (mul_le_mul_of_nonneg_left (lipComp_sub_norm_le T hBmeas hσ X Y) (Real.sqrt_nonneg _))
    _ = ((T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ) * ‖X - Y‖ := by ring

/-- **The Picard map is a contraction** on `E` once `T·L_b + √T·L_σ < 1` (a smallness
condition on the horizon `T` given the Lipschitz constants). Packages
`picardMap_contraction` as Mathlib's `ContractingWith`. -/
theorem picardMap_contractingWith (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hc : (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ < 1) :
    ContractingWith (Real.toNNReal ((T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ))
      (picardMap hB T hBmeas hBcont hb hσ η_E) := by
  have hc0 : (0 : ℝ) ≤ (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ := by positivity
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun X Y => ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc0, NNReal.coe_one]; exact hc
  · rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hc0]
    exact picardMap_contraction hB T hBmeas hBcont hb hσ η_E X Y

/-- **The strong solution** of the SDE (contraction regime): the unique fixed point of the
Picard map in `E`, from Banach's fixed-point theorem (`ContractingWith.fixedPoint`; `E` is a
complete, nonempty metric space). -/
noncomputable def picardSolution (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hc : (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ < 1) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  (picardMap_contractingWith hB T hBmeas hBcont hb hσ η_E hc).fixedPoint _

/-- **Existence + uniqueness** of the strong solution: `picardSolution` is a fixed point of
the Picard map, and it is the *only* one — the SDE `dX = b(X)dt + σ(X)dB` has a unique
strong solution in `E` under the contraction condition. -/
theorem picardMap_exists_unique_fixedPoint (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hc : (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ < 1) :
    ∃! X, picardMap hB T hBmeas hBcont hb hσ η_E X = X := by
  refine ⟨picardSolution hB T hBmeas hBcont hb hσ η_E hc, ?_, fun Y hY => ?_⟩
  · exact (picardMap_contractingWith hB T hBmeas hBcont hb hσ η_E hc).fixedPoint_isFixedPt
  · exact (picardMap_contractingWith hB T hBmeas hBcont hb hσ η_E hc).fixedPoint_unique hY

end SDEExistence
end MathFin
