/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoProcessPredictable

/-! # Predictability and `L²` assembly of the drift process (SDE-existence keystone II)

The Picard iterate for the SDE `dX = b(X)dt + σ(X)dB` is
`Φ(X)_t = η + ∫₀ᵗ b(X_s) ds + ∫₀ᵗ σ(X_s) dB_s`. The Itô term was assembled into
the predictable `L²` space `E := Lp ℝ 2 (trimMeasure_T T)` in
`ItoProcessPredictable`. This file does the same for the **drift** term
`t ↦ ∫₀ᵗ g(s, ω) ds`: it too must land back in `E` (predictable `L²`), because the
*next* iterate is fed through the Itô integral, whose integrand domain is `E`.

The drift is pure Lebesgue integration, so — unlike the Itô side — **none of this
needs the Brownian motion `B` itself** (`IsPreBrownianReal`), only its *filtration*
`natFiltration hBmeas`. Predictability follows the same route as the Itô term:
each elementary drift `driftSimpleProcess V` (the Lebesgue integral of the step
process `V`) is genuinely continuous and adapted for **every** `ω` — a finite sum
of `𝓕`-measurable coefficients times deterministic continuous time-increments — so
Degenne's `StronglyAdapted.isStronglyPredictable_of_leftContinuous` applies, and
predictability of the general assembled drift lifts through the `limUnder` that
defines its continuous version (`StronglyMeasurable.limUnder`).

* `driftSimpleProcess` — the elementary drift `∑_p V(p)(ω)·((p.2 ∧ t) − (p.1 ∧ t))`.
* `driftSimpleProcess_continuous` / `_stronglyAdapted` / `_isStronglyPredictable`.
* `driftContinuousMod` — the general assembled drift (pointwise `limUnder`).
* `driftContinuousMod_isStronglyPredictable` — it is predictable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcessContinuousModification
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- **The elementary drift (Lebesgue) integral** of a simple process `V`:
`driftSimpleProcess V t ω = ∑_p V(p)(ω)·((p.2 ∧ t) − (p.1 ∧ t))`. This is exactly
`∫₀ᵗ Ṽ(s, ω) ds` for the step process `Ṽ = ∑_p V(p)·𝟙_{(p.1, p.2]}` — the time
increment `(p.2 ∧ t) − (p.1 ∧ t)` is the Lebesgue length of `(p.1, p.2] ∩ (0, t]`. -/
noncomputable def driftSimpleProcess (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  V.value.sum fun p v => v ω * (((min p.2 t : ℝ≥0) : ℝ) - ((min p.1 t : ℝ≥0) : ℝ))

/-- **Path continuity of the elementary drift.** For every `ω`, `t ↦ driftSimpleProcess V t ω`
is continuous: a finite sum of `V(p)(ω)` (constant in `t`) times the continuous
time-increment `(p.2 ∧ t) − (p.1 ∧ t)` (continuous clamp `t ↦ min c t`, then the
coercion `ℝ≥0 → ℝ`). -/
theorem driftSimpleProcess_continuous (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (ω : Ω) :
    Continuous (fun t : ℝ≥0 => driftSimpleProcess hBmeas V t ω) := by
  rw [show (fun t : ℝ≥0 => driftSimpleProcess hBmeas V t ω)
        = fun t : ℝ≥0 => ∑ p ∈ V.value.support, V.value p ω * (((min p.2 t : ℝ≥0) : ℝ) - ((min p.1 t : ℝ≥0) : ℝ))
      from funext fun t => by rw [driftSimpleProcess]; rfl]
  fun_prop

/-- **The elementary drift is adapted.** For each `t`, `driftSimpleProcess V t` is
`𝓕_t`-measurable: it is `∑_p V(p)·c_p(t)` with `c_p(t) := (p.2 ∧ t) − (p.1 ∧ t)` a
real constant; for `p.1 ≤ t` the coefficient `V(p)` is `𝓕_{p.1} ⊆ 𝓕_t`-measurable, and
for `p.1 > t` the increment `c_p(t)` collapses to `0` (both endpoints clamp to `t`). -/
theorem driftSimpleProcess_stronglyAdapted (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) :
    StronglyAdapted (natFiltration hBmeas) (driftSimpleProcess hBmeas V) := by
  intro t
  have hsm : ∀ p ∈ V.value.support, StronglyMeasurable[natFiltration hBmeas t]
      (fun ω => V.value p ω * (((min p.2 t : ℝ≥0) : ℝ) - ((min p.1 t : ℝ≥0) : ℝ))) := by
    intro p hp
    by_cases ht : p.1 ≤ t
    · exact (((V.measurable_value p).mono ((natFiltration hBmeas).mono ht) le_rfl).stronglyMeasurable).mul
        stronglyMeasurable_const
    · push Not at ht
      have h1 : min p.1 t = t := min_eq_right ht.le
      have h2 : min p.2 t = t := min_eq_right (ht.le.trans (V.le_of_mem_support_value p hp))
      simp only [h1, h2, sub_self, mul_zero]
      exact stronglyMeasurable_const
  rw [show driftSimpleProcess hBmeas V t
        = fun ω => ∑ p ∈ V.value.support, V.value p ω * (((min p.2 t : ℝ≥0) : ℝ) - ((min p.1 t : ℝ≥0) : ℝ))
      from funext fun ω => by rw [driftSimpleProcess]; rfl]
  exact Finset.stronglyMeasurable_fun_sum _ hsm

/-- **The elementary drift is predictable** as a space-time function — genuinely
(every `ω`) continuous, hence left-continuous, and genuinely adapted, so Degenne's
`StronglyAdapted.isStronglyPredictable_of_leftContinuous` applies (the base case,
sidestepping the a.e./everywhere friction). -/
theorem driftSimpleProcess_isStronglyPredictable (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) :
    IsStronglyPredictable (natFiltration hBmeas) (driftSimpleProcess hBmeas V) := by
  apply MeasureTheory.StronglyAdapted.isStronglyPredictable_of_leftContinuous
  · exact driftSimpleProcess_stronglyAdapted hBmeas V
  · exact fun ω a => (driftSimpleProcess_continuous hBmeas V ω).continuousWithinAt

/-- The pathwise drift-limit process: for each `t, ω` the limit (junk off the
convergence set) of the elementary drifts of a fixed approximating sequence `Vₙ`
(`approxSeq`'s choice for `φ`). -/
noncomputable def driftContinuousMod (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop fun n => driftSimpleProcess hBmeas ((approxSeq T hBmeas φ).choose n).val t ω

/-- **The assembled drift is predictable** (general integrand). By construction
`driftContinuousMod` is the pointwise `limUnder` of the elementary drifts of a fixed
approximating sequence; each is predictable (`driftSimpleProcess_isStronglyPredictable`),
and `StronglyMeasurable.limUnder` lifts predictability to the limit. -/
theorem driftContinuousMod_isStronglyPredictable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    IsStronglyPredictable (natFiltration hBmeas) (driftContinuousMod T hBmeas φ) := by
  rw [IsStronglyPredictable]
  have hrw : (Function.uncurry (driftContinuousMod T hBmeas φ))
      = fun z : ℝ≥0 × Ω => limUnder atTop (fun n =>
          Function.uncurry (driftSimpleProcess hBmeas
            ((approxSeq T hBmeas φ).choose n).val) z) := by
    funext z; rfl
  rw [hrw]
  letI : MeasurableSpace (ℝ≥0 × Ω) := (natFiltration hBmeas).predictable
  exact StronglyMeasurable.limUnder (fun n =>
    driftSimpleProcess_isStronglyPredictable hBmeas
      ((approxSeq T hBmeas φ).choose n).val)

/-! ## Part 2 — the drift assembled into `E` (`L²`, energy bound, linearity) -/

/-- **Bridge to the honest Lebesgue integral.** The elementary drift is literally the
Lebesgue integral `∫₀ᵗ ⇑V(s,ω) ds` (against `timeMeasure`) of the step process `⇑V`: on
`(0,t]` the `⊥`-fibre vanishes and `⇑V(s,ω) = ∑_p 𝟙_{(p.1,p.2]}(s)·V(p)(ω)`, so each interval
contributes `V(p)(ω)·timeMeasure((0,t] ∩ (p.1,p.2])`, whose real value is the time-increment
`(p.2 ∧ t) − (p.1 ∧ t)`. This is the identity the `L²` bound reads through Cauchy–Schwarz. -/
theorem driftSimpleProcess_eq_setIntegral (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) (ω : Ω) :
    driftSimpleProcess hBmeas V t ω = ∫ s in Set.Ioc (0 : ℝ≥0) t, ⇑V s ω ∂timeMeasure := by
  haveI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have htoReal : ∀ p : ℝ≥0 × ℝ≥0, p.1 ≤ p.2 →
      (timeMeasure (Set.Ioc (0 : ℝ≥0) t ∩ Set.Ioc p.1 p.2)).toReal
        = ((min p.2 t : ℝ≥0) : ℝ) - ((min p.1 t : ℝ≥0) : ℝ) := by
    intro p hp12
    rw [Set.inter_comm, timeMeasure_Ioc_inter, NNReal.coe_zero, max_eq_left p.1.coe_nonneg,
        NNReal.coe_min, NNReal.coe_min]
    by_cases ht : p.1 ≤ t
    · rw [ENNReal.toReal_ofReal (by
            have : (p.1 : ℝ) ≤ min (p.2 : ℝ) t :=
              le_min (by exact_mod_cast hp12) (by exact_mod_cast ht)
            linarith), min_eq_left (by exact_mod_cast ht : (p.1 : ℝ) ≤ t)]
    · rw [not_le] at ht
      have htp1 : (t : ℝ) ≤ p.1 := le_of_lt (by exact_mod_cast ht)
      have htp2 : (t : ℝ) ≤ p.2 := htp1.trans (by exact_mod_cast hp12)
      rw [min_eq_right htp2, min_eq_right htp1, sub_self,
          ENNReal.ofReal_eq_zero.mpr (by linarith), ENNReal.toReal_zero]
  have hV_eq : Set.EqOn (fun s => ⇑V s ω)
      (fun s => ∑ p ∈ V.value.support, (Set.Ioc p.1 p.2).indicator (fun _ => V.value p ω) s)
      (Set.Ioc (0 : ℝ≥0) t) := by
    intro s hs
    have hs0 : s ∉ ({⊥} : Set ℝ≥0) := by
      simp only [Set.mem_singleton_iff]
      rintro rfl
      exact absurd hs.1 not_lt_bot
    simp only [SimpleProcess.apply_eq, Set.indicator_of_notMem hs0, zero_add, Finsupp.sum]
  have hint : ∀ p ∈ V.value.support,
      Integrable (fun s => (Set.Ioc p.1 p.2).indicator (fun _ => V.value p ω) s)
        (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)) :=
    fun p _ => (integrable_const (V.value p ω)).indicator measurableSet_Ioc
  rw [driftSimpleProcess, Finsupp.sum, setIntegral_congr_fun measurableSet_Ioc hV_eq,
      integral_finsetSum _ hint]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul,
      measureReal_def, htoReal p (V.le_of_mem_support_value p hp), mul_comm]

/-- **The elementary drift is `L²`** — indeed bounded. Each term satisfies
`|V(p)(ω)·((p.2 ∧ t) − (p.1 ∧ t))| ≤ valueBound·p.2` (the coefficient is bounded and the
time-increment lies in `[0, p.2]`), so the finite sum is bounded by the constant
`∑_p valueBound·p.2`; being predictable on the finite measure `trimMeasure_T T`, it is `MemLp`. -/
theorem memLp_uncurry_driftSimpleProcess (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) :
    MemLp (Function.uncurry (driftSimpleProcess hBmeas V)) 2 (trimMeasure_T (μ := μ) T hBmeas) := by
  refine MemLp.of_bound (driftSimpleProcess_isStronglyPredictable hBmeas V).aestronglyMeasurable
    (∑ p ∈ V.value.support, V.valueBound * (p.2 : ℝ)) (ae_of_all _ fun z => ?_)
  rw [Function.uncurry_apply_pair, driftSimpleProcess, Finsupp.sum, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  rw [abs_mul]
  have hval : |V.value p z.2| ≤ V.valueBound := by
    rw [← Real.norm_eq_abs]; exact V.value_le_valueBound p z.2
  have hc : |((min p.2 z.1 : ℝ≥0) : ℝ) - ((min p.1 z.1 : ℝ≥0) : ℝ)| ≤ (p.2 : ℝ) := by
    rw [abs_of_nonneg (by
      have : ((min p.1 z.1 : ℝ≥0) : ℝ) ≤ ((min p.2 z.1 : ℝ≥0) : ℝ) := by
        exact_mod_cast min_le_min_right z.1 (V.le_of_mem_support_value p hp)
      linarith)]
    have h1 : ((min p.2 z.1 : ℝ≥0) : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast min_le_left p.2 z.1
    have h2 : (0 : ℝ) ≤ ((min p.1 z.1 : ℝ≥0) : ℝ) := (min p.1 z.1).coe_nonneg
    linarith
  exact mul_le_mul hval hc (abs_nonneg _) (le_trans (abs_nonneg _) hval)

end ItoIntegralProcessContinuousModification
end MathFin
