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

/-- **Cauchy–Schwarz for a finite measure**: `(∫ f)² ≤ ν(univ)·∫ f²`. The drift's `L²` bound
reads through this (with `ν = timeMeasure` restricted to `(0,t]`): `∫₀ᵗ` costs a factor `t`. -/
private lemma sq_integral_le_measureReal_mul {α : Type*} {m : MeasurableSpace α} {ν : Measure α}
    [IsFiniteMeasure ν] {f : α → ℝ} (hf : MemLp f 2 ν) :
    (∫ a, f a ∂ν) ^ 2 ≤ (ν Set.univ).toReal * ∫ a, (f a) ^ 2 ∂ν := by
  have hp : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hf2 : Integrable (fun a => (f a) ^ 2) ν :=
    (hf.integrable_mul hf).congr (ae_of_all _ fun a => by simp only [Pi.mul_apply, pow_two])
  have hint_nonneg : 0 ≤ ∫ a, (f a) ^ 2 ∂ν := integral_nonneg fun a => sq_nonneg _
  have hmeas_nonneg : 0 ≤ (ν Set.univ).toReal := ENNReal.toReal_nonneg
  -- Hölder with `g = 1`: `∫|f| ≤ (∫f²)^½·(ν univ)^½` (Hölder exponents are `rpow`).
  have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ν) hp
    (f := |f|) (g := fun _ => (1 : ℝ))
    (ae_of_all ν fun a => abs_nonneg (f a)) (ae_of_all ν fun _ => zero_le_one)
    (by simpa [ENNReal.ofReal_ofNat] using hf.abs)
    (by simpa [ENNReal.ofReal_ofNat] using memLp_const (1 : ℝ))
  have hpow : ∫ a, |f| a ^ (2 : ℝ) ∂ν = ∫ a, (f a) ^ 2 ∂ν := by
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    show |f a| ^ (2 : ℝ) = (f a) ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [hpow, Real.one_rpow, integral_const, smul_eq_mul, mul_one, measureReal_def] at hhold
  -- `|∫ f| ≤ ∫ |f|` then square through the Hölder bound.
  have habs : |∫ a, f a ∂ν| ≤ (∫ a, (f a) ^ 2 ∂ν) ^ (1 / 2 : ℝ) * (ν Set.univ).toReal ^ (1 / 2 : ℝ) := by
    refine (abs_integral_le_integral_abs).trans ?_
    simpa only [Pi.abs_apply, mul_one] using hhold
  calc (∫ a, f a ∂ν) ^ 2 = |∫ a, f a ∂ν| ^ 2 := (sq_abs _).symm
    _ ≤ ((∫ a, (f a) ^ 2 ∂ν) ^ (1 / 2 : ℝ) * (ν Set.univ).toReal ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = (ν Set.univ).toReal * ∫ a, (f a) ^ 2 ∂ν := by
        rw [mul_pow, ← Real.rpow_natCast ((∫ a, (f a) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) 2,
          ← Real.rpow_natCast ((ν Set.univ).toReal ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hint_nonneg,
          ← Real.rpow_mul hmeas_nonneg]
        norm_num
        ring

/-- **The elementary-drift slice is `L²` in the time variable** (bounded step process on the
finite measure `timeMeasure.restrict (Ioc 0 T)`). -/
private lemma memLp_slice (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (ω : Ω) :
    MemLp (fun s => ⇑V s ω) 2 (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) := by
  haveI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  refine MemLp.of_bound
    (((V.isStronglyPredictable.mono (natFiltration hBmeas).predictable_le_prod).comp_measurable
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (V.valueBotBound + ∑ p ∈ V.value.support, V.valueBound) (ae_of_all _ fun s => ?_)
  rw [SimpleProcess.apply_eq, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [Set.indicator]
    split_ifs with h
    · exact V.valueBot_le_valueBotBound ω
    · rw [abs_zero]; exact V.valueBotBound_nonneg
  · rw [Finsupp.sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [Set.indicator]
    split_ifs with h
    · rw [← Real.norm_eq_abs]; exact V.value_le_valueBound p ω
    · rw [abs_zero]; exact V.valueBound_nonneg

/-- **Pointwise `L²` bound of the elementary drift** (bridge + Cauchy–Schwarz + interval
extension): for `t ≤ T`, `(driftSimpleProcess V t ω)² ≤ T·∫₀ᵀ (⇑V s ω)² ds`. -/
private lemma driftSimpleProcess_sq_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) {t : ℝ≥0} (htT : t ≤ T) (ω : Ω) :
    (driftSimpleProcess hBmeas V t ω) ^ 2
      ≤ (T : ℝ) * ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑V s ω) ^ 2 ∂timeMeasure := by
  haveI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  rw [driftSimpleProcess_eq_setIntegral]
  have hCS := sq_integral_le_measureReal_mul (ν := timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) t))
    (f := fun s => ⇑V s ω) ((memLp_slice T hBmeas V ω).mono_measure (Measure.restrict_mono
      (Set.Ioc_subset_Ioc_right htT) le_rfl))
  rw [Measure.restrict_apply_univ, timeMeasure_Ioc,
    ENNReal.toReal_ofReal (by rw [NNReal.coe_zero, sub_zero]; exact t.coe_nonneg),
    NNReal.coe_zero, sub_zero] at hCS
  refine hCS.trans (mul_le_mul (by exact_mod_cast htT) ?_ (integral_nonneg fun s => sq_nonneg _)
    T.coe_nonneg)
  exact setIntegral_mono_set ((memLp_slice T hBmeas V ω).integrable_sq)
    (ae_of_all _ fun s => sq_nonneg _) (Set.Ioc_subset_Ioc_right htT).eventuallyLE

/-- The elementary drift assembled as an element of `E = Lp ℝ 2 (trimMeasure_T T)`. -/
noncomputable def driftProcessLp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  (memLp_uncurry_driftSimpleProcess T hBmeas V).toLp (Function.uncurry (driftSimpleProcess hBmeas V))

/-- **The drift energy bound** — the relative `L²` bound that makes the drift a bounded operator
on `E`: `‖driftProcessLp V‖ ≤ T·‖simpleAssembly_T V‖`. Tonelli turns the `E`-norm into
`∫₀ᵀ∫_Ω (drift)² `; the pointwise Cauchy–Schwarz bound `(drift)² ≤ T·∫₀ᵀ(⇑V)²` and Fubini
collapse the inner double integral to `T·‖simpleAssembly_T V‖²`; the outer `∫₀ᵀ` adds the last `T`. -/
theorem driftProcessLp_norm_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (V : TBoundedSP T hBmeas) :
    ‖driftProcessLp (μ := μ) T hBmeas V.val‖ ≤ (T : ℝ) * ‖simpleAssembly_T (μ := μ) T hBmeas V‖ := by
  set 𝓕 := natFiltration (mΩ := mΩ) hBmeas
  have hpredD := driftSimpleProcess_isStronglyPredictable hBmeas V.val
  have hmemD := memLp_uncurry_driftSimpleProcess (μ := μ) T hBmeas V.val
  have hmemV := memLp_uncurry_trim_T (μ := μ) T hBmeas V.val
  -- both `E`-norms², via `lp_two_norm_sq` + `coeFn_toLp` + `integral_trim`, as product integrals.
  have hnorm : ∀ (g : ℝ≥0 → Ω → ℝ) (hg : MemLp (Function.uncurry g) 2 (trimMeasure_T (μ := μ) T hBmeas)),
      StronglyMeasurable[𝓕.predictable] (Function.uncurry g) →
      ‖hg.toLp (Function.uncurry g)‖ ^ 2
        = ∫ z, (Function.uncurry g z) ^ 2 ∂((timeMeasure_T T).prod μ) := by
    intro g hg hgp
    rw [lp_two_norm_sq, integral_congr_ae (g := fun z => (Function.uncurry g z) ^ 2)
      (by filter_upwards [hg.coeFn_toLp] with z hz; rw [hz]),
      show trimMeasure_T (μ := μ) T hBmeas
          = ((timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod from rfl,
      ← integral_trim 𝓕.predictable_le_prod
        (f := fun z => (Function.uncurry g z) ^ 2) (hgp.pow 2)]
  have hsAsm : simpleAssembly_T (μ := μ) T hBmeas V = hmemV.toLp (Function.uncurry ⇑V.val) := rfl
  have hsq : ‖driftProcessLp (μ := μ) T hBmeas V.val‖ ^ 2
      ≤ ((T : ℝ) * ‖simpleAssembly_T (μ := μ) T hBmeas V‖) ^ 2 := by
    rw [driftProcessLp, hnorm _ hmemD hpredD, mul_pow, hsAsm,
      hnorm _ hmemV V.val.isStronglyPredictable]
    -- ∫ (drift)² ∂prod ≤ (T:ℝ)² · ∫ (⇑V)² ∂prod
    have hmemD_prod : MemLp (Function.uncurry (driftSimpleProcess hBmeas V.val)) 2
        ((timeMeasure_T T).prod μ) :=
      ⟨(hpredD.mono 𝓕.predictable_le_prod).aestronglyMeasurable, by
        rw [← eLpNorm_trim 𝓕.predictable_le_prod hpredD]; exact hmemD.2⟩
    have hmemV_prod : MemLp (Function.uncurry ⇑V.val) 2 ((timeMeasure_T T).prod μ) :=
      ⟨(V.val.isStronglyPredictable.mono 𝓕.predictable_le_prod).aestronglyMeasurable, by
        rw [← eLpNorm_trim 𝓕.predictable_le_prod V.val.isStronglyPredictable]; exact hmemV.2⟩
    have hintD := hmemD_prod.integrable_sq
    have hintV := hmemV_prod.integrable_sq
    rw [integral_prod _ hintD]
    -- Fubini: `∫_ω ∫_{Ioc 0 T}(⇑V)² dμ = ∫_prod (⇑V)²`.
    have hW : ∫ ω, (∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑V.val s ω) ^ 2 ∂timeMeasure) ∂μ
        = ∫ z, (Function.uncurry ⇑V.val z) ^ 2 ∂((timeMeasure_T T).prod μ) := by
      rw [integral_prod _ hintV]
      exact integral_integral_swap hintV.swap
    calc ∫ t, ∫ ω, (driftSimpleProcess hBmeas V.val t ω) ^ 2 ∂μ ∂(timeMeasure_T T)
        ≤ ∫ _t : ℝ≥0, (T : ℝ) * ∫ z, (Function.uncurry ⇑V.val z) ^ 2 ∂((timeMeasure_T T).prod μ)
            ∂(timeMeasure_T T) := by
          refine integral_mono_ae hintD.integral_prod_left (integrable_const _) ?_
          have hslice : ∀ᵐ t ∂(timeMeasure_T T),
              Integrable (fun ω => (driftSimpleProcess hBmeas V.val t ω) ^ 2) μ :=
            hintD.prod_right_ae
          filter_upwards [ae_restrict_mem (μ := timeMeasure) measurableSet_Ioc, hslice]
            with t ht hint_t
          calc ∫ ω, (driftSimpleProcess hBmeas V.val t ω) ^ 2 ∂μ
              ≤ ∫ ω, (T : ℝ) * ∫ s in Set.Ioc (0 : ℝ≥0) T, (⇑V.val s ω) ^ 2 ∂timeMeasure ∂μ :=
                integral_mono_ae hint_t
                  ((hintV.integral_prod_right).const_mul _)
                  (ae_of_all _ fun ω => driftSimpleProcess_sq_le T hBmeas V.val ht.2 ω)
            _ = (T : ℝ) * ∫ z, (Function.uncurry ⇑V.val z) ^ 2 ∂((timeMeasure_T T).prod μ) := by
                rw [integral_const_mul, hW]
      _ = (T : ℝ) ^ 2 * ∫ z, (Function.uncurry ⇑V.val z) ^ 2 ∂((timeMeasure_T T).prod μ) := by
          rw [integral_const, timeMeasure_T, measureReal_def, Measure.restrict_apply_univ,
            timeMeasure_Ioc,
            ENNReal.toReal_ofReal (by rw [NNReal.coe_zero, sub_zero]; exact T.coe_nonneg),
            NNReal.coe_zero, sub_zero, smul_eq_mul]
          ring
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (mul_nonneg T.coe_nonneg (norm_nonneg _))] at h

end ItoIntegralProcessContinuousModification
end MathFin
