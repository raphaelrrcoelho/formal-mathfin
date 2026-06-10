/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralProcess

/-! # The Itô integral process is an adapted L² martingale (B1a)

The simple-integrand Itô integral `t ↦ (V●B)_t` (`ItoIntegralProcess`), as a
process, is adapted, a martingale, satisfies the time-indexed isometry, and is
L²-continuous. The crux is lifting the *unconditional* martingale-difference
`ItoIsometryAdapted.integral_adapted_mul_increment` to its `condExp` form.
Pathwise continuity and general (non-simple) integrands are later milestones. -/

@[expose] public section

namespace MathFin
namespace ItoIntegralProcess

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- The process `(V●B)_t` is `𝓕_t`-measurable: each surviving summand is an
`𝓕_{p.1}`-measurable coefficient (`p.1 ≤ t`) times increments `B_{p.i∧t}` with
`p.i ∧ t ≤ t`. -/
theorem itoSimpleProcess_adaptedAt (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) (t : ℝ≥0) :
    Measurable[ItoIntegralL2.natFiltration hBmeas t] (itoSimpleProcess hBmeas V t) := by
  -- `B u` is `𝓕_t`-measurable for `u ≤ t`: `comap (B u) ≤ ⨆ j ≤ t, comap (B j) = 𝓕_t`.
  have hBmeas_le : ∀ {u : ℝ≥0}, u ≤ t →
      Measurable[ItoIntegralL2.natFiltration hBmeas t] (B u) := by
    intro u hu
    have hle : MeasurableSpace.comap (B u) (inferInstance : MeasurableSpace ℝ)
        ≤ ItoIntegralL2.natFiltration hBmeas t :=
      le_iSup₂_of_le u hu le_rfl
    exact (measurable_iff_comap_le.mpr le_rfl).mono hle le_rfl
  rw [show itoSimpleProcess hBmeas V t
        = fun ω => ∑ p ∈ V.value.support,
            V.value p ω * (B (min p.2 t) ω - B (min p.1 t) ω)
      from funext fun ω => by rw [itoSimpleProcess_apply]; rfl]
  refine Finset.measurable_sum _ (fun p hp => ?_)
  by_cases ht : p.1 ≤ t
  · -- active interval: coefficient `𝓕_{p.1} ⊆ 𝓕_t`, both truncated endpoints `≤ t`
    have hV : Measurable[ItoIntegralL2.natFiltration hBmeas t] (V.value p) :=
      (V.measurable_value p).mono ((ItoIntegralL2.natFiltration hBmeas).mono ht) le_rfl
    exact hV.mul ((hBmeas_le (min_le_right p.2 t)).sub (hBmeas_le (min_le_right p.1 t)))
  · -- interval past `t`: both endpoints truncate to `t`, the term is `0`
    push Not at ht
    have h1 : min p.1 t = t := min_eq_right ht.le
    have h2 : min p.2 t = t := min_eq_right (ht.le.trans (V.le_of_mem_support_value p hp))
    simp only [h1, h2, sub_self, mul_zero]
    exact measurable_const

end ItoIntegralProcess
end MathFin
