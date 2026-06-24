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
L²-continuous. The conditional martingale-difference `condExp_adapted_mul_increment`
— the conditional sibling of the unconditional
`ItoIsometryAdapted.integral_adapted_mul_increment` — packages
`μ[φ·ΔB | 𝓕_{t₀}] = 0` as a reusable lemma; the martingale property itself is
established directly, applying that same set-integral characterisation per
`𝓕_s`-set. Pathwise continuity and general (non-simple) integrands are later
milestones. -/

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

variable (hB : IsPreBrownianReal B μ)

include hB

/-- **Conditional martingale-difference** — the conditional sibling of the
unconditional `ItoIsometryAdapted.integral_adapted_mul_increment`, packaged for
reuse. For `φ` adapted at `t₀ ≤ t₁` and bounded,
`μ[φ·(B_{t₁}−B_{t₀}) | 𝓕_{t₀}] = 0`, via the set-integral characterisation of
conditional expectation: the candidate `0` agrees with `φ·ΔB` on every
`𝓕_{t₀}`-set, since `(s.indicator φ)·ΔB` is the unconditional
martingale-difference. (`itoSimpleProcess_isMartingale` applies this same
characterisation directly per-set rather than calling this lemma; it stands here
as the reusable single-increment statement.) -/
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
    (ItoIsometryAdapted.memLp_adapted_mul_increment hB hBmeas ht hφ hφ_L2).integrable
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
    exact (ItoIsometryAdapted.integral_adapted_mul_increment hB hBmeas ht hind_adapt).symm
  · exact stronglyMeasurable_const.aestronglyMeasurable

omit hB in
/-- **Clamped-increment identity.** For `u ≤ v` and `i ≤ j`, the increment between
times `i` and `j` of the single-interval contribution `t ↦ B_{v∧t} − B_{u∧t}` is
the Brownian increment over `[u∨i, (u∨i)∨(v∧j)]` — so it is a martingale
difference past `𝓕_i`. (`B` is an arbitrary path here; pure `min`/`max` algebra.) -/
private lemma clamped_increment_eq {u v i j : ℝ≥0} (huv : u ≤ v) (hij : i ≤ j)
    (ω : Ω) :
    (B (min v j) ω - B (min u j) ω) - (B (min v i) ω - B (min u i) ω)
      = B (max (max u i) (min v j)) ω - B (max u i) ω := by
  rcases le_total i u with h1 | h1 <;> rcases le_total j u with h2 | h2 <;>
    rcases le_total i v with h3 | h3 <;> rcases le_total j v with h4 | h4 <;>
      simp_all <;> grind

/-- **The Itô integral process is an `L²` martingale.** `t ↦ (V●B)_t` is adapted
(`itoSimpleProcess_adaptedAt`), `L¹` (`memLp_itoSimpleProcess`, `L²⟹L¹` on a
probability space), and for `i ≤ j`, `μ[(V●B)_j | 𝓕_i] = (V●B)_i`: the increment
`(V●B)_i − (V●B)_j` is, per interval, `V(p)·(B(mₚ) − B(Mₚ))` with
`mₚ = p.1∨i ≤ Mₚ = (p.1∨i)∨(p.2∧j)` (`clamped_increment_eq`), whose `𝓕_i`-set
integral vanishes by the unconditional martingale-difference
`integral_adapted_mul_increment` applied to `s.indicator (V(p))` (adapted at `mₚ`). -/
theorem itoSimpleProcess_isMartingale (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) :
    Martingale (fun t ω => itoSimpleProcess hBmeas V t ω)
      (ItoIntegralL2.natFiltration hBmeas) μ := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t => (itoSimpleProcess_adaptedAt hBmeas V t).stronglyMeasurable, ?_⟩
  intro i j hij
  have hint : ∀ t : ℝ≥0, Integrable (fun ω => itoSimpleProcess hBmeas V t ω) μ :=
    fun t => (memLp_itoSimpleProcess hB hBmeas V t).integrable (by norm_num)
  have hadapt : ∀ p ∈ V.value.support,
      ItoIsometryAdapted.AdaptedAt B (max p.1 i) (V.value p) := fun p _ =>
    (ItoIntegralL2.adaptedAt_of_measurable_natural hBmeas
      (V.measurable_value p)).mono (le_max_left _ _)
  have hVL2 : ∀ p, MemLp (V.value p) 2 μ := fun p => memLp_value hB hBmeas V p
  have hle_mM : ∀ p : ℝ≥0 × ℝ≥0,
      max p.1 i ≤ max (max p.1 i) (min p.2 j) := fun _ => le_max_left _ _
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq ((ItoIntegralL2.natFiltration hBmeas).le i)
    (hint j) (fun s _ _ => (hint i).integrableOn) (fun s hs _ => ?_)
    (itoSimpleProcess_adaptedAt hBmeas V i).stronglyMeasurable.aestronglyMeasurable
  have hmle : ItoIntegralL2.natFiltration hBmeas i ≤ mΩ :=
    (ItoIntegralL2.natFiltration hBmeas).le i
  -- the `i`-minus-`j` increment is `-∑ₚ V(p)·(B(Mₚ) − B(mₚ))`
  have hpt : (fun ω => itoSimpleProcess hBmeas V i ω - itoSimpleProcess hBmeas V j ω)
      = fun ω => -∑ p ∈ V.value.support,
          V.value p ω * (B (max (max p.1 i) (min p.2 j)) ω - B (max p.1 i) ω) := by
    funext ω
    rw [itoSimpleProcess_apply, itoSimpleProcess_apply, Finsupp.sum, Finsupp.sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hcl := clamped_increment_eq (B := B) (V.le_of_mem_support_value p hp) hij ω
    rw [← mul_sub, ← mul_neg]
    congr 1
    linarith [hcl]
  have hterm_int : ∀ p ∈ V.value.support,
      Integrable (fun ω => V.value p ω
        * (B (max (max p.1 i) (min p.2 j)) ω - B (max p.1 i) ω)) (μ.restrict s) :=
    fun p hp => ((ItoIsometryAdapted.memLp_adapted_mul_increment hB hBmeas (hle_mM p)
      (hadapt p hp) (hVL2 p)).integrable (by norm_num)).integrableOn
  rw [← sub_eq_zero, ← integral_sub (hint i).integrableOn (hint j).integrableOn, hpt,
      integral_neg, neg_eq_zero, integral_finsetSum _ hterm_int]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hAadapt : ItoIsometryAdapted.AdaptedAt B (max p.1 i) (s.indicator (V.value p)) := by
    have h1 : ItoIsometryAdapted.AdaptedAt B (max p.1 i) (s.indicator (1 : Ω → ℝ)) :=
      (ItoIntegralL2.adaptedAt_of_measurable_natural hBmeas
        ((measurable_const :
          Measurable[ItoIntegralL2.natFiltration hBmeas i] (1 : Ω → ℝ)).indicator hs)).mono
        (le_max_right _ _)
    have heq : (fun ω => s.indicator (1 : Ω → ℝ) ω * V.value p ω) = s.indicator (V.value p) := by
      funext ω; by_cases h : ω ∈ s <;> simp [h]
    exact heq ▸ h1.mul (hadapt p hp)
  rw [← integral_indicator (hmle s hs),
      show (s.indicator fun ω => V.value p ω
            * (B (max (max p.1 i) (min p.2 j)) ω - B (max p.1 i) ω))
          = fun ω => s.indicator (V.value p) ω
            * (B (max (max p.1 i) (min p.2 j)) ω - B (max p.1 i) ω) from by
        funext ω; by_cases h : ω ∈ s <;> simp [h]]
  exact ItoIsometryAdapted.integral_adapted_mul_increment hB hBmeas (hle_mM p) hAadapt

/-- **Time-indexed Itô isometry.** `E[(V●B)_t²]` equals the predictable-rectangle
double sum with every interval endpoint truncated at `t`:
`∑_{p,q} E[V(p)·V(q)]·vol((p.1∧t, p.2∧t] ∩ (q.1∧t, q.2∧t])`. The proof mirrors the
terminal `ItoIntegralL2.itoSimple_sq_integral`: the square of the truncated
increment sum expands into a double sum; active rectangles collapse by
`rect_increment_pairing`, while a rectangle whose left endpoint is past `t` has a
collapsed (zero-length) increment matching the zero overlap on the right.
Mathematically, `itoSimple_sq_integral` is recovered when `t` is past every right
endpoint. (RHS endpoints are cast after `min` — `↑(p.2∧t)` — to match
`rect_increment_pairing`'s output.) -/
theorem itoSimpleProcess_isometry_time (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) (t : ℝ≥0) :
    ∫ ω, (itoSimpleProcess hBmeas V t ω) ^ 2 ∂μ
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min ((min p.2 t : ℝ≥0) : ℝ) ((min q.2 t : ℝ≥0) : ℝ))
                - (max ((min p.1 t : ℝ≥0) : ℝ) ((min q.1 t : ℝ≥0) : ℝ))) := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  classical
  set a : (ℝ≥0 × ℝ≥0) → Ω → ℝ :=
    fun p ω => V.value p ω * (B (min p.2 t) ω - B (min p.1 t) ω) with ha_def
  have ha_L2 : ∀ p ∈ V.value.support, MemLp (a p) 2 μ :=
    fun p hp => memLp_truncated_term hB hBmeas V t hp
  have hint : ∀ p ∈ V.value.support, ∀ q ∈ V.value.support,
      Integrable (fun ω => a p ω * a q ω) μ :=
    fun p hp q hq => (ha_L2 p hp).integrable_mul (ha_L2 q hq)
  calc ∫ ω, (itoSimpleProcess hBmeas V t ω) ^ 2 ∂μ
      = ∫ ω, ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, a p ω * a q ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show itoSimpleProcess hBmeas V t ω ^ 2
          = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, a p ω * a q ω
        rw [show itoSimpleProcess hBmeas V t ω = ∑ p ∈ V.value.support, a p ω from by
              rw [itoSimpleProcess_apply]; rfl, sq, Finset.sum_mul_sum]
    _ = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, ∫ ω, a p ω * a q ω ∂μ := by
        rw [integral_finsetSum _ (fun p hp => integrable_finsetSum _ fun q hq => hint p hp q hq)]
        exact Finset.sum_congr rfl fun p hp =>
          integral_finsetSum _ (fun q hq => hint p hp q hq)
    _ = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min ((min p.2 t : ℝ≥0) : ℝ) ((min q.2 t : ℝ≥0) : ℝ))
                - (max ((min p.1 t : ℝ≥0) : ℝ) ((min q.1 t : ℝ≥0) : ℝ))) := by
        refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
        by_cases htp : p.1 ≤ t
        · by_cases htq : q.1 ≤ t
          · -- both rectangles active: collapse via the rectangle pairing
            simp only [ha_def, min_eq_left htp, min_eq_left htq]
            exact ItoIsometryAdapted.rect_increment_pairing hB hBmeas
              (ItoIntegralL2.adaptedAt_of_measurable_natural hBmeas (V.measurable_value p))
              (ItoIntegralL2.adaptedAt_of_measurable_natural hBmeas (V.measurable_value q))
              (fun ω => by rw [← Real.norm_eq_abs]; exact V.value_le_valueBound p ω)
              (fun ω => by rw [← Real.norm_eq_abs]; exact V.value_le_valueBound q ω)
              (le_min (V.le_of_mem_support_value p hp) htp)
              (le_min (V.le_of_mem_support_value q hq) htq)
          · -- `q` past `t`: its increment collapses, overlap is zero
            have hq1 : min q.1 t = t := min_eq_right (not_le.mp htq).le
            have hq2 : min q.2 t = t :=
              min_eq_right ((not_le.mp htq).le.trans (V.le_of_mem_support_value q hq))
            have hz : ∀ ω, a p ω * a q ω = 0 := fun ω => by simp [ha_def, hq1, hq2]
            rw [integral_congr_ae (Filter.Eventually.of_forall hz), integral_zero, hq1, hq2,
              max_eq_left (sub_nonpos.mpr ((min_le_right _ _).trans (le_max_right _ _))), mul_zero]
        · -- `p` past `t`: symmetric
          have hp1 : min p.1 t = t := min_eq_right (not_le.mp htp).le
          have hp2 : min p.2 t = t :=
            min_eq_right ((not_le.mp htp).le.trans (V.le_of_mem_support_value p hp))
          have hz : ∀ ω, a p ω * a q ω = 0 := fun ω => by simp [ha_def, hp1, hp2]
          rw [integral_congr_ae (Filter.Eventually.of_forall hz), integral_zero, hp1, hp2,
            max_eq_left (sub_nonpos.mpr ((min_le_left _ _).trans (le_max_left _ _))), mul_zero]

/-- **`L²`-continuity.** `t ↦ (V●B)_t` is continuous into `Lp ℝ 2 μ`. For `s ≤ t`
the increment `(V●B)_t − (V●B)_s = ∑_p V(p)·(B_{a_p∨(p.2∧t)} − B_{a_p})`
(`a_p = p.1∨s`) is a finite sum of adapted Brownian increments over sub-intervals of
`(s, t]` (`clamped_increment_eq`). Cauchy–Schwarz over the finite support plus the
single-increment isometry `integral_adapted_sq_mul_increment_sq` give the `√`-Hölder
modulus `‖(V●B)_t − (V●B)_s‖² ≤ (|support|·∑_p E[V(p)²])·|t − s|`, whence continuity. -/
theorem itoSimpleProcessLp_l2_continuous (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) :
    Continuous (fun t : ℝ≥0 => (itoSimpleProcessLp hB hBmeas V t : Lp ℝ 2 μ)) := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  set C : ℝ := (V.value.support.card : ℝ)
    * ∑ p ∈ V.value.support, ∫ ω, (V.value p ω) ^ 2 ∂μ with hC
  have hVsq_nonneg : ∀ p, 0 ≤ ∫ ω, (V.value p ω) ^ 2 ∂μ :=
    fun p => integral_nonneg fun ω => sq_nonneg _
  have hC0 : 0 ≤ C :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun p _ => hVsq_nonneg p)
  -- `L²`-modulus on an ordered pair: `∫ ((V●B)_t − (V●B)_s)² ≤ C·(t − s)` for `s ≤ t`.
  have hmod : ∀ {s t : ℝ≥0}, s ≤ t →
      ∫ ω, (itoSimpleProcess hBmeas V t ω - itoSimpleProcess hBmeas V s ω) ^ 2 ∂μ
        ≤ C * ((t : ℝ) - s) := by
    intro s t hst
    have hadapt : ∀ p, ItoIsometryAdapted.AdaptedAt B (max p.1 s) (V.value p) := fun p =>
      (ItoIntegralL2.adaptedAt_of_measurable_natural hBmeas (V.measurable_value p)).mono
        (le_max_left _ _)
    have hVL2 : ∀ p, MemLp (V.value p) 2 μ := fun p => memLp_value hB hBmeas V p
    have hXL2 : ∀ p, MemLp (fun ω => V.value p ω
        * (B (max (max p.1 s) (min p.2 t)) ω - B (max p.1 s) ω)) 2 μ := fun p =>
      ItoIsometryAdapted.memLp_adapted_mul_increment hB hBmeas (le_max_left _ _) (hadapt p) (hVL2 p)
    have hintXsq : ∀ p, Integrable (fun ω => (V.value p ω
        * (B (max (max p.1 s) (min p.2 t)) ω - B (max p.1 s) ω)) ^ 2) μ :=
      fun p => (hXL2 p).integrable_sq
    have hgdiff : ∀ ω, itoSimpleProcess hBmeas V t ω - itoSimpleProcess hBmeas V s ω
        = ∑ p ∈ V.value.support, V.value p ω
            * (B (max (max p.1 s) (min p.2 t)) ω - B (max p.1 s) ω) := by
      intro ω
      rw [itoSimpleProcess_apply, itoSimpleProcess_apply, Finsupp.sum, Finsupp.sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hcl := clamped_increment_eq (B := B) (V.le_of_mem_support_value p hp) hst ω
      rw [← mul_sub, hcl]
    have hsq_int : Integrable (fun ω => (∑ p ∈ V.value.support, V.value p ω
        * (B (max (max p.1 s) (min p.2 t)) ω - B (max p.1 s) ω)) ^ 2) μ :=
      (memLp_finsetSum _ fun p _ => hXL2 p).integrable_sq
    have hcard_int : Integrable (fun ω => (V.value.support.card : ℝ)
        * ∑ p ∈ V.value.support, (V.value p ω
          * (B (max (max p.1 s) (min p.2 t)) ω - B (max p.1 s) ω)) ^ 2) μ :=
      (integrable_finsetSum _ fun p _ => hintXsq p).const_mul _
    calc ∫ ω, (itoSimpleProcess hBmeas V t ω - itoSimpleProcess hBmeas V s ω) ^ 2 ∂μ
        = ∫ ω, (∑ p ∈ V.value.support, V.value p ω
            * (B (max (max p.1 s) (min p.2 t)) ω - B (max p.1 s) ω)) ^ 2 ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          simp only [hgdiff]
      _ ≤ ∫ ω, (V.value.support.card : ℝ) * ∑ p ∈ V.value.support, (V.value p ω
            * (B (max (max p.1 s) (min p.2 t)) ω - B (max p.1 s) ω)) ^ 2 ∂μ := by
          refine integral_mono hsq_int hcard_int fun ω => ?_
          have h := Finset.sum_mul_sq_le_sq_mul_sq V.value.support (fun _ => (1 : ℝ))
            (fun p => V.value p ω * (B (max (max p.1 s) (min p.2 t)) ω - B (max p.1 s) ω))
          simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using h
      _ = (V.value.support.card : ℝ) * ∑ p ∈ V.value.support, ∫ ω, (V.value p ω
            * (B (max (max p.1 s) (min p.2 t)) ω - B (max p.1 s) ω)) ^ 2 ∂μ := by
          rw [integral_const_mul, integral_finsetSum _ fun p _ => hintXsq p]
      _ ≤ C * ((t : ℝ) - s) := by
          rw [hC, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun p hp => ?_
          have hXsq_eq : ∫ ω, (V.value p ω
              * (B (max (max p.1 s) (min p.2 t)) ω - B (max p.1 s) ω)) ^ 2 ∂μ
              = (∫ ω, (V.value p ω) ^ 2 ∂μ)
                * (((max (max p.1 s) (min p.2 t) : ℝ≥0) : ℝ) - ((max p.1 s : ℝ≥0) : ℝ)) := by
            rw [← ItoIsometryAdapted.integral_adapted_sq_mul_increment_sq hB hBmeas
              (le_max_left _ _) (hadapt p)]
            exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
          rw [hXsq_eq]
          refine mul_le_mul_of_nonneg_left ?_ (hVsq_nonneg p)
          have e1 : ((min p.2 t : ℝ≥0) : ℝ) ≤ (t : ℝ) := by exact_mod_cast min_le_right p.2 t
          have e2 : (s : ℝ) ≤ ((max p.1 s : ℝ≥0) : ℝ) := by exact_mod_cast le_max_right p.1 s
          have e3 : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
          rw [NNReal.coe_max]
          rcases le_total ((min p.2 t : ℝ≥0) : ℝ) ((max p.1 s : ℝ≥0) : ℝ) with h | h
          · rw [max_eq_left h]; linarith
          · rw [max_eq_right h]; linarith
  -- symmetric modulus in `dist`, then the `√`-Hölder bound and continuity.
  have hmod_sym : ∀ t s : ℝ≥0,
      ∫ ω, (itoSimpleProcess hBmeas V t ω - itoSimpleProcess hBmeas V s ω) ^ 2 ∂μ
        ≤ C * dist t s := by
    intro t s
    rw [NNReal.dist_eq]
    rcases le_total s t with h | h
    · rw [abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))]
      exact hmod h
    · rw [abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (NNReal.coe_le_coe.mpr h)), neg_sub,
        show (fun ω => (itoSimpleProcess hBmeas V t ω - itoSimpleProcess hBmeas V s ω) ^ 2)
          = (fun ω => (itoSimpleProcess hBmeas V s ω - itoSimpleProcess hBmeas V t ω) ^ 2)
          from funext fun ω => by ring]
      exact hmod h
  set F : ℝ≥0 → Lp ℝ 2 μ := fun t => itoSimpleProcessLp hB hBmeas V t with hF
  rw [continuous_iff_continuousAt]
  intro s
  have hbound : ∀ t : ℝ≥0, ‖F t - F s‖ ≤ Real.sqrt C * Real.sqrt (dist t s) := by
    intro t
    have hnorm_sq : ‖F t - F s‖ ^ 2
        = ∫ ω, (itoSimpleProcess hBmeas V t ω - itoSimpleProcess hBmeas V s ω) ^ 2 ∂μ := by
      have hsub : F t - F s
          = ((memLp_itoSimpleProcess hB hBmeas V t).sub
              (memLp_itoSimpleProcess hB hBmeas V s)).toLp _ := by
        simp only [hF]
        show (memLp_itoSimpleProcess hB hBmeas V t).toLp _ -
            (memLp_itoSimpleProcess hB hBmeas V s).toLp _ = _
        rw [← MemLp.toLp_sub]
      rw [hsub, ← real_inner_self_eq_norm_sq, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp ((memLp_itoSimpleProcess (μ := μ) hB hBmeas V t).sub
        (memLp_itoSimpleProcess (μ := μ) hB hBmeas V s))] with ω hω
      rw [hω]; simp only [Pi.sub_apply]
      show (itoSimpleProcess hBmeas V t ω - itoSimpleProcess hBmeas V s ω)
          * (itoSimpleProcess hBmeas V t ω - itoSimpleProcess hBmeas V s ω)
          = (itoSimpleProcess hBmeas V t ω - itoSimpleProcess hBmeas V s ω) ^ 2
      ring
    rw [← Real.sqrt_mul hC0, ← Real.sqrt_sq (norm_nonneg (F t - F s))]
    refine Real.sqrt_le_sqrt ?_
    rw [hnorm_sq]; exact hmod_sym t s
  have htendsto : Filter.Tendsto
      (fun t : ℝ≥0 => Real.sqrt C * Real.sqrt (dist t s)) (nhds s) (nhds 0) := by
    have hcont : Continuous (fun t : ℝ≥0 => Real.sqrt C * Real.sqrt (dist t s)) :=
      continuous_const.mul ((continuous_id.dist continuous_const).sqrt)
    simpa [dist_self] using hcont.tendsto s
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr
    (squeeze_zero (fun t => norm_nonneg _) hbound htendsto)

end ItoIntegralProcess
end MathFin
