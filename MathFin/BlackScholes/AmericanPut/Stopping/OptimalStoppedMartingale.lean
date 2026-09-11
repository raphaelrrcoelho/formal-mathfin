/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import MathFin.BlackScholes.AmericanPut.Stopping.OrderedSampling
public import MathFin.BlackScholes.AmericanPut.Stopping.BoundedLocalMartingale

/-! # A bounded continuous supermartingale stopped at a value-preserving rule

Ordered optional sampling gives equality at every earlier rule. Pasting two
observation times on a past event then gives equality of the corresponding set
integrals, which is exactly the martingale criterion.

## Result

Public entry points include `BoundedRule.binary`, `BoundedRule.capTime`, `BoundedRule.capBinary`, `expected_value_eq_before_optimal_rule`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The two-valued rule stopping at `i` on the event `A ∈ 𝓕 i` and at `j` off it. -/
noncomputable def BoundedRule.binary {i j : ℝ≥0} (hij : i ≤ j) (A : Set Ω)
    (hA : MeasurableSet[𝓕 i] A) : BoundedRule 𝓕 j := by
  classical
  refine ⟨fun ω => if ω ∈ A then i else j,?_,?_⟩
  · intro t
    by_cases hjt : j ≤ t
    · have hit := hij.trans hjt
      convert! (@MeasurableSet.univ Ω (𝓕 t)) using 1
      ext ω
      by_cases hω : ω ∈ A <;> simp [hω]
      · convert! hit using 1
        simp only [ENNReal.ofNNReal,WithTop.coe_le_coe]
      · convert! hjt using 1
        simp only [ENNReal.ofNNReal,WithTop.coe_le_coe]
    · by_cases hit : i ≤ t
      · convert! (𝓕.mono hit A hA) using 1
        ext ω
        by_cases hω : ω ∈ A <;> simp [hω]
        · convert! hit using 1
          simp only [ENNReal.ofNNReal,WithTop.coe_le_coe]
        · convert! (lt_of_not_ge hjt) using 1
          simp only [ENNReal.ofNNReal,not_le,WithTop.coe_lt_coe]
      · convert! (@MeasurableSet.empty Ω (𝓕 t)) using 1
        ext ω
        by_cases hω : ω ∈ A <;> simp [hω]
        · convert! (lt_of_not_ge hit) using 1
          simp only [ENNReal.ofNNReal,not_le,WithTop.coe_lt_coe]
        · convert! (lt_of_not_ge hjt) using 1
          simp only [ENNReal.ofNNReal,not_le,WithTop.coe_lt_coe]
  · intro ω
    split_ifs
    · exact hij
    · exact le_rfl

/-- The rule `τ` stopped no later than the deterministic time `t`. -/
def BoundedRule.capTime {T : ℝ≥0} (τ : BoundedRule 𝓕 T) (t : ℝ≥0) : BoundedRule 𝓕 T where
  time := fun ω => min t (τ.time ω)
  stopping := by
    intro s
    convert! ((isStoppingTime_const 𝓕 t) s).union (τ.stopping s) using 1
    ext ω
    simp only [mem_setOf_eq,WithTop.coe_le_coe,min_le_iff,mem_union]
  le_horizon := fun ω => (min_le_right _ _).trans (τ.le_horizon ω)

/-- The rule `τ` stopped no later than `BoundedRule.binary hij A hA`. -/
noncomputable def BoundedRule.capBinary {T i j : ℝ≥0} (τ : BoundedRule 𝓕 T)
    (hij : i ≤ j) (A : Set Ω) (hA : MeasurableSet[𝓕 i] A) : BoundedRule 𝓕 T where
  time := fun ω => min ((BoundedRule.binary hij A hA).time ω) (τ.time ω)
  stopping := by
    intro t
    convert! ((BoundedRule.binary hij A hA).stopping t).union (τ.stopping t) using 1
    ext ω
    simp only [mem_setOf_eq,WithTop.coe_le_coe,min_le_iff,mem_union]
  le_horizon := fun ω => (min_le_right _ _).trans (τ.le_horizon ω)

variable {P : Measure Ω} [IsFiniteMeasure P] {U : ℝ≥0 → Ω → ℝ} {C : ℝ} {T : ℝ≥0}

theorem expected_value_eq_before_optimal_rule
    (hU : Supermartingale U 𝓕 P) (hc : ∀ ω, Continuous (fun t => U t ω))
    (hb : ∀ t ω, ‖U t ω‖ ≤ C) (τ : BoundedRule 𝓕 T)
    (hopt : (∫ ω, U (τ.time ω) ω ∂P) = ∫ ω, U 0 ω ∂P)
    (η : BoundedRule 𝓕 T) (hη : ∀ ω, η.time ω ≤ τ.time ω) :
    (∫ ω, U (η.time ω) ω ∂P) = ∫ ω, U 0 ω ∂P := by
  apply le_antisymm (expected_stoppedValue_le_initial hU hc hb η)
  rw [← hopt]
  exact expected_stoppedValue_le_of_le hU hc hb η τ hη

theorem stopped_martingale_of_expected_value_eq
    (hU : Supermartingale U 𝓕 P) (hc : ∀ ω, Continuous (fun t => U t ω))
    (hb : ∀ t ω, ‖U t ω‖ ≤ C) (τ : BoundedRule 𝓕 T)
    (hopt : (∫ ω, U (τ.time ω) ω ∂P) = ∫ ω, U 0 ω ∂P) :
    Martingale (fun t ω => U (min t (τ.time ω)) ω) 𝓕 P := by
  classical
  let X : ℝ≥0 → Ω → ℝ := fun t ω => U (min t (τ.time ω)) ω
  have ha : StronglyAdapted 𝓕 X := by
    convert! hU.stronglyAdapted.stoppedProcess hc τ.stopping using 1
  have hi (t : ℝ≥0) : Integrable (X t) P :=
    (integrable_const C).mono' ((ha t).mono (𝓕.le t)).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hb _ ω))
  have hmean (t : ℝ≥0) : (∫ ω, X t ω ∂P) = ∫ ω, U 0 ω ∂P :=
    expected_value_eq_before_optimal_rule hU hc hb τ hopt (τ.capTime t) (fun _ => min_le_right _ _)
  apply martingale_of_setIntegral_eq_real ha hi
  intro i j hij A hA
  have hAm : MeasurableSet A := 𝓕.le i A hA
  let η := τ.capBinary hij A hA
  have hη : (∫ ω, U (η.time ω) ω ∂P) = ∫ ω, U 0 ω ∂P :=
    expected_value_eq_before_optimal_rule hU hc hb τ hopt η (fun _ => min_le_right _ _)
  have he : (fun ω => U (η.time ω) ω) = A.piecewise (X i) (X j) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [η,BoundedRule.capBinary,BoundedRule.binary,X,hω]
  rw [he,integral_piecewise hAm (hi i).integrableOn (hi j).integrableOn] at hη
  have hj := (integral_add_compl hAm (hi j)).trans (hmean j)
  linarith

end MathFin.BlackScholes.AmericanPut.Stopping
