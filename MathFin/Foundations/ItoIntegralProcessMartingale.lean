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

variable [hB : IsPreBrownian B μ]

/-- **Conditional martingale-difference.** For `φ` adapted at `t₀ ≤ t₁` and
bounded, `μ[φ·(B_{t₁}−B_{t₀}) | 𝓕_{t₀}] = 0` — the `condExp` lift of the
unconditional `ItoIsometryAdapted.integral_adapted_mul_increment`, via the
set-integral characterisation of conditional expectation (the candidate `0`
agrees with `φ·ΔB` on every `𝓕_{t₀}`-set, since `(s.indicator φ)·ΔB` is the
unconditional martingale-difference). -/
theorem condExp_adapted_mul_increment (hBmeas : ∀ t, Measurable (B t))
    {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) {φ : Ω → ℝ}
    (hφ : ItoIsometryAdapted.AdaptedAt B t₀ φ) {C : ℝ} (hC : ∀ ω, |φ ω| ≤ C) :
    μ[fun ω => φ ω * (B t₁ ω - B t₀ ω) | ItoIntegralL2.natFiltration hBmeas t₀]
      =ᵐ[μ] 0 := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hm : ItoIntegralL2.natFiltration hBmeas t₀ ≤ mΩ :=
    (ItoIntegralL2.natFiltration hBmeas).le t₀
  have hφm : Measurable φ := hφ.measurable hBmeas
  have hφ_L2 : MemLp φ 2 μ :=
    MemLp.of_bound hφm.aestronglyMeasurable C
      (ae_of_all _ fun ω => (Real.norm_eq_abs _).trans_le (hC ω))
  have hg_int : Integrable (fun ω => φ ω * (B t₁ ω - B t₀ ω)) μ :=
    (ItoIsometryAdapted.memLp_adapted_mul_increment hBmeas ht hφ hφ_L2).integrable
      (by norm_num)
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hg_int
    (fun s _ _ => (integrable_zero Ω ℝ μ).integrableOn) (fun s hs _ => ?_) ?_
  · -- `∫_s 0 = ∫_s φ·ΔB`, and `∫_s φ·ΔB = ∫ (s.indicator φ)·ΔB = 0`.
    have hind_adapt : ItoIsometryAdapted.AdaptedAt B t₀ (s.indicator φ) := by
      have h1 : ItoIsometryAdapted.AdaptedAt B t₀ (s.indicator (1 : Ω → ℝ)) :=
        ItoIntegralL2.adaptedAt_of_measurable_natural hBmeas
          ((measurable_const :
            Measurable[ItoIntegralL2.natFiltration hBmeas t₀] (1 : Ω → ℝ)).indicator hs)
      have heq : (fun ω => s.indicator (1 : Ω → ℝ) ω * φ ω) = s.indicator φ := by
        funext ω; by_cases h : ω ∈ s <;> simp [h]
      exact heq ▸ h1.mul hφ
    have heq2 : Set.indicator s (fun ω => φ ω * (B t₁ ω - B t₀ ω))
        = fun ω => s.indicator φ ω * (B t₁ ω - B t₀ ω) := by
      funext ω; by_cases h : ω ∈ s <;> simp [h]
    simp only [Pi.zero_apply, integral_zero]
    rw [← integral_indicator (hm s hs), heq2]
    exact (ItoIsometryAdapted.integral_adapted_mul_increment hBmeas ht hind_adapt).symm
  · exact stronglyMeasurable_const.aestronglyMeasurable

end ItoIntegralProcess
end MathFin
