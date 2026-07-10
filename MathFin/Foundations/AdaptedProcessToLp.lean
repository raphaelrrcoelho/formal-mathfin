/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralCLM
public import BrownianMotion.StochasticIntegral.Predictable

/-!
# Realizing a bounded adapted continuous process as an Itô-integrand class (the σ-realization)

The Itô integral `∫₀ᵀ σ dB` (`ItoIntegralCLM.itoIntegralCLM_T`) takes its integrand from the
**predictable** `L²` space `E := Lp ℝ 2 (trimMeasure_T T)` — an `Lp` class over the trim product
measure on the predictable σ-algebra, never a raw process `σ : ℝ≥0 → Ω → ℝ`. To integrate a genuine
bounded adapted process (e.g. a continuous market price of risk `θ` for the general adapted Girsanov
theorem), one must first **realize** it inside `E`. This is the σ-realization: the last piece of
"the concrete adapted stochastic integral" (SP0, half (i)) that the drift/Itô SDE files build only
for their specific processes.

For an **every-`ω`-continuous** bounded adapted `σ` this is a short assembly on the existing tower —
no a.e./everywhere friction, exactly as `DriftProcessPredictable.driftSimpleProcess` handles its
elementary drift:

* `MathFin.isStronglyPredictable_of_bdd_adapted_cont` — continuous + adapted ⟹ predictable, via
  Degenne's `StronglyAdapted.isStronglyPredictable_of_leftContinuous` (continuity gives the
  left-continuity it wants);
* `MathFin.memLp_uncurry_of_bdd_adapted_cont` — predictable + bounded on the *finite* measure
  `trimMeasure_T T` ⟹ `MemLp … 2`;
* `MathFin.processToLp` — the realization `σ ↦ (its class in E)`, with `processToLp_coeFn` the a.e.
  identification back to `Function.uncurry σ`.

This unblocks the continuous-adapted Girsanov (brick α4): `∫θdB` and its Doléans density are now
formable for a bounded adapted continuous `θ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin

open ItoIntegralL2 ItoIntegralCLM

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- **A bounded adapted continuous process is predictable.** For an `𝓕`-adapted `σ` that is
continuous in time for every `ω`, the space-time function `(t, ω) ↦ σ t ω` is measurable for the
predictable σ-algebra — continuity gives the left-continuity Degenne's
`StronglyAdapted.isStronglyPredictable_of_leftContinuous` requires, and no randomness in the
time-regularity means no exceptional null set to dodge. -/
theorem isStronglyPredictable_of_bdd_adapted_cont (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) :
    IsStronglyPredictable (natFiltration hBmeas) σ := by
  apply MeasureTheory.StronglyAdapted.isStronglyPredictable_of_leftContinuous hadap
  exact fun ω a ↦ (hcont ω).continuousWithinAt

/-- **A bounded adapted continuous process is `L²` over `trimMeasure_T T`.** It is predictable
(`isStronglyPredictable_of_bdd_adapted_cont`) and bounded, and `trimMeasure_T T` is a finite
measure, so `MemLp.of_bound` applies. -/
theorem memLp_uncurry_of_bdd_adapted_cont (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    MemLp (Function.uncurry σ) 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  MemLp.of_bound
    (isStronglyPredictable_of_bdd_adapted_cont hBmeas hadap hcont).aestronglyMeasurable
    C (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hbdd z.1 z.2)

/-- **The σ-realization.** A bounded adapted continuous process realized as an element of the
Itô-integrand space `E = Lp ℝ 2 (trimMeasure_T T)` — the domain of
`ItoIntegralCLM.itoIntegralCLM_T`. This is the missing bridge from a raw bounded adapted continuous
process `σ : ℝ≥0 → Ω → ℝ` to `∫₀ᵀ σ dB`; with it, the general continuous-adapted Girsanov density is
formable. -/
noncomputable def processToLp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  (memLp_uncurry_of_bdd_adapted_cont T hBmeas hadap hcont hbdd).toLp (Function.uncurry σ)

/-- **The realization agrees with `σ` a.e.** `processToLp T σ =ᵐ[trimMeasure_T T] Function.uncurry σ`
— the identification that lets Itô-integral computations read the class back as the process. -/
theorem processToLp_coeFn (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (σ t))
    (hcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ σ t ω)) {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    processToLp (μ := μ) T hBmeas hadap hcont hbdd
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas] Function.uncurry σ :=
  (memLp_uncurry_of_bdd_adapted_cont T hBmeas hadap hcont hbdd).coeFn_toLp

/-! ### The σ-realization for a bounded **predictable** integrand (Girsanov Rung 1)

Dropping the continuity hypothesis: the Itô integral's domain is the *predictable* `L²` space, so a
bounded process that is already strongly predictable needs no continuity to be realized — the
`aestronglyMeasurable` it carries is exactly what `MemLp.of_bound` consumes. The continuous
realization above is the special case `IsStronglyPredictable` = `isStronglyPredictable_of_bdd_adapted_cont`. -/

/-- **A bounded predictable process is `L²` over `trimMeasure_T T`.** Predictable + bounded on the
finite measure `trimMeasure_T T` ⟹ `MemLp.of_bound`; the continuity of
`memLp_uncurry_of_bdd_adapted_cont` is dropped. -/
theorem memLp_uncurry_of_bdd_predictable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) σ)
    {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    MemLp (Function.uncurry σ) 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  MemLp.of_bound hpred.aestronglyMeasurable C
    (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact hbdd z.1 z.2)

/-- **The σ-realization for a bounded predictable process.** Realizes a bounded strongly-predictable
`σ : ℝ≥0 → Ω → ℝ` as an element of the Itô-integrand space `E = Lp ℝ 2 (trimMeasure_T T)` — the
domain of `ItoIntegralCLM.itoIntegralCLM_T` — with no continuity assumption. -/
noncomputable def processToLpPredictable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) σ)
    {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  (memLp_uncurry_of_bdd_predictable T hBmeas hpred hbdd).toLp (Function.uncurry σ)

/-- **The predictable realization agrees with `σ` a.e.** -/
theorem processToLpPredictable_coeFn (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {σ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) σ)
    {C : ℝ} (hbdd : ∀ t ω, |σ t ω| ≤ C) :
    processToLpPredictable (μ := μ) T hBmeas hpred hbdd
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas] Function.uncurry σ :=
  (memLp_uncurry_of_bdd_predictable T hBmeas hpred hbdd).coeFn_toLp

end MathFin
