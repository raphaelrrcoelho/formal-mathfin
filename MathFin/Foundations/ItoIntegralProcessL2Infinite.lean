/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralL2Dense
public import MathFin.Foundations.ItoIntegralProcessGeneral

/-!
# The unbounded-horizon Itô integral as an L² process

B2 (`ItoIntegralL2Dense`) built the **terminal** `[0,∞)` Itô integral
`itoIntegralL2 : Lp 2 trim_full →L[ℝ] Lp 2 μ` over the **horizon-independent**
predictable integrand `f` (the σ-finite completion). This file lifts it to a
**process** `itoProcessL2Inf t f := E[∫₀^∞ f dB | 𝓕_t]` — the
conditional-expectation projection of the terminal integral onto the natural
filtration `𝓕_t`, exactly mirroring the finite-horizon `itoProcessCLM`
(`ItoIntegralProcessGeneral`) but with the horizon-independent terminal integral.

Because the integrand no longer depends on the horizon, the L² **martingale
property** (`itoProcessL2Inf_isMartingale`) and **adaptedness**
(`itoProcessL2Inf_aeStronglyMeasurable`) hold on all of `ℝ≥0` directly from the
conditional-expectation tower — no integrand gluing is needed.

## The `[0,∞)` continuous-local-martingale arc

This is **step 1** (the L² process). Remaining:
* **step 2** — horizon consistency: `itoProcessL2Inf t f =ᵐ itoProcessCLM T t (f|[0,T])`
  for `t ≤ T` (the Itô increment-independence lemma `E[∫₀^∞ | 𝓕_T] = ∫₀ᵀ`);
* **step 3** — the glued continuous modification on `[0,∞)` (the finite gate per
  horizon `T = n`, glued by `indistinguishable_of_modification_on`);
* **step 4** — the `IsLocalMartingale` on the null-augmented filtration (reusing
  `condExp_sup_nulls` / `augFiltration` from the `[0,T]` follow-on).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcessL2Infinite

open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral

/-! ## The `Lp` inclusion for `ν ≤ μ` (generic) -/

section MonoMeasureLp
variable {α : Type*} {_mα : MeasurableSpace α} {μ ν : Measure α}

/-- **The `Lp` inclusion for `ν ≤ μ`.** For `f ∈ Lp 2 μ` the *same* function lies in
`Lp 2 ν` with no larger norm (a smaller measure can only shrink the `L²` norm), so
`f ↦ f` is a norm-`≤ 1` continuous linear map `Lp 2 μ →L[ℝ] Lp 2 ν`. Mathlib has
`MemLp.mono_measure` but no packaged CLM; generic measure theory, a natural upstream
candidate. Specialises to measure restriction (`ν = μ.restrict s`, via
`Measure.restrict_le_self`). -/
noncomputable def monoMeasureLp (h : ν ≤ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ((Lp.memLp f).mono_measure h).toLp
      map_add' := fun f g ↦ by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).mono_measure h),
          Lp.coeFn_add (((Lp.memLp f).mono_measure h).toLp) (((Lp.memLp g).mono_measure h).toLp),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_measure h),
          MemLp.coeFn_toLp ((Lp.memLp g).mono_measure h),
          (Lp.coeFn_add f g).filter_mono (ae_mono h)] with x h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.add_apply]
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_measure h),
          Lp.coeFn_smul c (((Lp.memLp f).mono_measure h).toLp),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_measure h),
          (Lp.coeFn_smul c f).filter_mono (ae_mono h)] with x h1 h2 h3 h4
        simp only [h1, h2, h3, h4, Pi.smul_apply, RingHom.id_apply] }
    1 (fun f ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.memLp f).2.ne ?_
      rw [eLpNorm_congr_ae (MemLp.coeFn_toLp ((Lp.memLp f).mono_measure h))]
      exact eLpNorm_mono_measure _ h)

@[simp] lemma monoMeasureLp_coeFn (h : ν ≤ μ) (f : Lp ℝ 2 μ) :
    ⇑(monoMeasureLp h f) =ᵐ[ν] ⇑f := by
  simp only [monoMeasureLp, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

end MonoMeasureLp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

/-- **Restriction of a `[0,∞)` predictable integrand to the band `[0,T]`** as a CLM
`Lp 2 trim_full →L[ℝ] Lp 2 (trimMeasure_T T)`: the `Lp` inclusion for
`trimMeasure_T T ≤ trim_full` (the band restriction, `trimMeasure_T_eq_restrict` +
`Measure.restrict_le_self`). The integrand seen on `[0,T]`. -/
noncomputable def restrictToBand (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 ((timeMeasure.prod μ).trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)
      →L[ℝ] Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  monoMeasureLp ((trimMeasure_T_eq_restrict T hBmeas).le.trans Measure.restrict_le_self)

@[simp] lemma restrictToBand_coeFn (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    ⇑(restrictToBand (μ := μ) T hBmeas f) =ᵐ[trimMeasure_T (μ := μ) T hBmeas] ⇑f :=
  monoMeasureLp_coeFn _ f

/-- **The `[0,T]`-restriction of a simple process's `[0,∞)` assembly is its `[0,T]`
simple-process element** `simpleProcessL2_T`. Both are `toLp (uncurry V)` — one against
the full trim, one against the `[0,T]` trim — and `restrictToBand` only re-reads the
*same* function against the smaller measure, so they coincide a.e. on `[0,T]` (where
`trimMeasure_T` is supported). **No truncation of `V` is needed**: the `[0,T]` element is
literally `V`'s integrand re-measured, not a clamped process. -/
lemma restrictToBand_simpleAssembly (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    restrictToBand (μ := μ) T hBmeas (simpleAssembly hBmeas V)
      = simpleProcessL2_T (μ := μ) T hBmeas V := by
  have hmono : trimMeasure_T (μ := μ) T hBmeas
      ≤ (timeMeasure.prod μ).trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod :=
    (trimMeasure_T_eq_restrict T hBmeas).le.trans Measure.restrict_le_self
  refine Lp.ext ?_
  calc ⇑(restrictToBand (μ := μ) T hBmeas (simpleAssembly hBmeas V))
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas] ⇑(simpleAssembly hBmeas V) :=
        restrictToBand_coeFn T hBmeas _
    _ =ᵐ[trimMeasure_T (μ := μ) T hBmeas] Function.uncurry ⇑V :=
        (MemLp.coeFn_toLp (memLp_uncurry_trim hBmeas V)).filter_mono (ae_mono hmono)
    _ =ᵐ[trimMeasure_T (μ := μ) T hBmeas] ⇑(simpleProcessL2_T (μ := μ) T hBmeas V) :=
        (MemLp.coeFn_toLp (memLp_uncurry_trim_T T hBmeas V)).symm

/-! ### The `[0,T]` clamp of a simple process

The increment-independence crux `itoIntegralCLM_T T (simpleProcessL2_T T V) =ᵐ
itoSimpleProcess V T` cannot be read off the existing `T`-bounded machinery directly,
because a general `V` may carry intervals reaching past `T`. We clamp `V` to the band:
**drop the intervals starting past `T`, clamp every surviving right endpoint to `T`**.
The clamp `clampSP T V` is `T`-bounded, its discrete Itô integral on `[0,t]` agrees with
`V`'s for `t ≤ T`, and its `[0,T]` `L²` integrand agrees with `V`'s — so `V` and its clamp
are indistinguishable to all of the `[0,T]` machinery, which is exactly what closes the
crux. -/

/-- Fiber-sum value of the clamped `mapDomain`: `mapDomain` collapses intervals sharing a
left endpoint, so the value at `p` is the (finite) sum of the original `V`-values over the
clamp-preimage of `p`. The contributors all share `p`'s left endpoint, which keeps the
value `𝓕_{p.1}`-measurable. -/
private lemma clamp_value_apply (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (p : ℝ≥0 × ℝ≥0) (ω : Ω) :
    ((V.value.filter (fun q ↦ q.1 ≤ T)).mapDomain (fun q ↦ (q.1, q.2 ⊓ T))) p ω
      = ∑ a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support,
          (if (a.1, a.2 ⊓ T) = p then V.value a ω else 0) := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [Finsupp.support_filter, Finset.mem_filter] at ha
  rw [Finsupp.single_apply]
  by_cases h : (a.1, a.2 ⊓ T) = p
  · simp only [if_pos h, Finsupp.filter_apply_pos (fun q ↦ q.1 ≤ T) V.value ha.2]
  · simp only [if_neg h, Pi.zero_apply]

/-- **The `[0,T]` clamp of a simple process.** -/
noncomputable def clampSP (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas) where
  valueBot := V.valueBot
  value := (V.value.filter (fun q ↦ q.1 ≤ T)).mapDomain (fun q ↦ (q.1, q.2 ⊓ T))
  le_of_mem_support_value := fun p hp ↦ by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
    rw [Finsupp.support_filter, Finset.mem_filter] at ha
    exact le_inf (V.le_of_mem_support_value a ha.1) ha.2
  measurable_valueBot := V.measurable_valueBot
  measurable_value' := fun p hp ↦ by
    rw [show ((V.value.filter (fun q ↦ q.1 ≤ T)).mapDomain (fun q ↦ (q.1, q.2 ⊓ T))) p
          = fun ω ↦ ∑ a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support,
              (if (a.1, a.2 ⊓ T) = p then V.value a ω else 0)
        from funext fun ω ↦ clamp_value_apply T hBmeas V p ω]
    refine Finset.measurable_sum _ fun a ha ↦ ?_
    by_cases h : (a.1, a.2 ⊓ T) = p
    · simp only [if_pos h]
      rw [Finsupp.support_filter, Finset.mem_filter] at ha
      have hp1 : a.1 = p.1 := (Prod.ext_iff.mp h).1
      exact hp1 ▸ V.measurable_value a
    · simp only [if_neg h]; exact measurable_const
  bounded_valueBot := V.bounded_valueBot
  bounded_value := by
    refine ⟨(V.value.filter (fun q ↦ q.1 ≤ T)).support.card • |V.valueBound|, fun p hp ω ↦ ?_⟩
    rw [clamp_value_apply]
    calc ‖∑ a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support,
              (if (a.1, a.2 ⊓ T) = p then V.value a ω else 0)‖
        ≤ ∑ a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support,
            ‖(if (a.1, a.2 ⊓ T) = p then V.value a ω else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support, |V.valueBound| := by
          refine Finset.sum_le_sum fun a ha ↦ ?_
          by_cases h : (a.1, a.2 ⊓ T) = p
          · simp only [if_pos h]
            exact (V.value_le_valueBound a ω).trans (le_abs_self _)
          · simp only [if_neg h, norm_zero]; exact abs_nonneg _
      _ = (V.value.filter (fun q ↦ q.1 ≤ T)).support.card • |V.valueBound| := by
          rw [Finset.sum_const]

/-- **Master `Finsupp.sum` identity for the clamp.** Any additive-in-the-value statistic
`φ` summed over the clamp equals the same statistic summed over `V`, provided `φ` is
invariant under the right-endpoint clamp on the kept intervals (`hclamp`) and vanishes on
the dropped ones (`hdrop`). Both `clampSP_itoSimpleProcess` and `clampSP_simpleProcessL2_T`
are instances. -/
private lemma clampSP_value_sum {N : Type*} [AddCommMonoid N] (T : ℝ≥0)
    (hBmeas : ∀ u, Measurable (B u)) (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas))
    (φ : ℝ≥0 × ℝ≥0 → (Ω → ℝ) → N)
    (hφ0 : ∀ p, φ p 0 = 0) (hφadd : ∀ p u v, φ p (u + v) = φ p u + φ p v)
    (hclamp : ∀ a ∈ V.value.support, a.1 ≤ T → φ (a.1, a.2 ⊓ T) (V.value a) = φ a (V.value a))
    (hdrop : ∀ a ∈ V.value.support, T < a.1 → φ a (V.value a) = 0) :
    (clampSP T hBmeas V).value.sum φ = V.value.sum φ := by
  show ((V.value.filter (fun q ↦ q.1 ≤ T)).mapDomain (fun q ↦ (q.1, q.2 ⊓ T))).sum φ
      = V.value.sum φ
  rw [Finsupp.sum_mapDomain_index hφ0 hφadd, Finsupp.sum, Finsupp.support_filter,
      Finset.sum_filter]
  conv_rhs => rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  by_cases hP : a.1 ≤ T
  · rw [if_pos hP, Finsupp.filter_apply_pos (fun q ↦ q.1 ≤ T) V.value hP]
    exact hclamp a ha hP
  · rw [if_neg hP]
    exact (hdrop a ha (not_le.mp hP)).symm

/-- **Clamp preserves the `[0,t]` discrete Itô integral for `t ≤ T`.** -/
lemma clampSP_itoSimpleProcess (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (ht : t ≤ T) :
    itoSimpleProcess hBmeas (clampSP T hBmeas V) t = itoSimpleProcess hBmeas V t := by
  funext ω
  rw [itoSimpleProcess_apply, itoSimpleProcess_apply]
  refine clampSP_value_sum T hBmeas V (fun p v ↦ v ω * (B (min p.2 t) ω - B (min p.1 t) ω))
    (fun p ↦ by simp) (fun p u v ↦ by simp only [Pi.add_apply]; ring)
    (fun a ha hP ↦ ?_) (fun a ha hP ↦ ?_)
  · rw [show min (a.2 ⊓ T) t = min a.2 t from by rw [min_assoc, min_eq_right ht]]
  · have h1 : min a.1 t = t := min_eq_right (le_of_lt (lt_of_le_of_lt ht hP))
    have h2 : min a.2 t = t :=
      min_eq_right (le_of_lt (lt_of_le_of_lt ht (lt_of_lt_of_le hP (V.le_of_mem_support_value a ha))))
    rw [h1, h2, sub_self, mul_zero]

/-- **Clamp agrees with `V` pointwise on the band `(0,T]`.** -/
lemma clampSP_apply (T s : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hsT : s ≤ T) (ω : Ω) :
    (clampSP T hBmeas V) s ω = V s ω := by
  rw [SimpleProcess.apply_eq, SimpleProcess.apply_eq]
  congr 1
  exact clampSP_value_sum T hBmeas V (fun p v ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) s)
    (fun p ↦ by simp)
    (fun p u v ↦ by
      simp only [Set.indicator_apply, Pi.add_apply]
      split_ifs <;> simp)
    (fun a ha hP ↦ by
      simp only [Set.indicator_apply]
      refine if_congr (Iff.intro (fun h ↦ ⟨h.1, h.2.trans inf_le_left⟩)
        (fun h ↦ ⟨h.1, le_inf h.2 hsT⟩)) rfl rfl)
    (fun a ha hP ↦ by
      rw [Set.indicator_of_notMem]
      rintro ⟨h1, _⟩
      exact absurd (lt_of_le_of_lt hsT hP) (not_lt.mpr h1.le))

/-- **Clamp preserves the `[0,T]` `L²` integrand.** -/
lemma clampSP_simpleProcessL2_T (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    simpleProcessL2_T (μ := μ) T hBmeas (clampSP T hBmeas V)
      = simpleProcessL2_T (μ := μ) T hBmeas V := by
  refine Lp.ext ((MemLp.coeFn_toLp (memLp_uncurry_trim_T T hBmeas (clampSP T hBmeas V))).trans
    ((?_ : Function.uncurry ⇑(clampSP T hBmeas V)
        =ᵐ[trimMeasure_T (μ := μ) T hBmeas] Function.uncurry ⇑V).trans
      (MemLp.coeFn_toLp (memLp_uncurry_trim_T T hBmeas V)).symm))
  rw [trimMeasure_T_eq_restrict]
  refine Filter.eventuallyEq_of_mem
    (self_mem_ae_restrict (MeasureTheory.measurableSet_predictable_Ioc_prod
      (𝓕 := natFiltration hBmeas) 0 T MeasurableSet.univ)) (fun z hz ↦ ?_)
  obtain ⟨⟨_, hzT⟩, _⟩ := hz
  exact clampSP_apply T z.1 hBmeas V hzT z.2

/-- **The increment-independence crux (process form).** For `t ≤ T` the finite-horizon
process `itoProcessCLM T t` of `V`'s `[0,T]` `L²` integrand reproduces `V`'s `[0,t]` discrete
Itô integral. Via the clamp: `simpleProcessL2_T T V = simpleAssembly_T T (clampSP T V)`
(`clampSP_simpleProcessL2_T`), `itoProcessCLM_simpleAssembly_T` then gives `(V'●B)_t` of the
`T`-bounded clamp, which equals `(V●B)_t` (`clampSP_itoSimpleProcess`). -/
lemma itoProcessCLM_simpleProcessL2_T (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (ht : t ≤ T) :
    (itoProcessCLM hB T t hBmeas (simpleProcessL2_T (μ := μ) T hBmeas V) : Ω → ℝ)
      =ᵐ[μ] itoSimpleProcess hBmeas V t := by
  have hclampT : clampSP T hBmeas V ∈ TBoundedSP T hBmeas := fun p hp ↦ by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
    exact inf_le_right
  have hP1 : simpleProcessL2_T (μ := μ) T hBmeas V
      = simpleAssembly_T (μ := μ) T hBmeas ⟨clampSP T hBmeas V, hclampT⟩ :=
    (clampSP_simpleProcessL2_T T hBmeas V).symm
  rw [hP1, itoProcessCLM_simpleAssembly_T]
  exact clampSP_itoSimpleProcess T t hBmeas V ht ▸
    (memLp_itoSimpleProcess hB hBmeas (clampSP T hBmeas V) t).coeFn_toLp

/-- **The unbounded-horizon Itô process** `(f●B)_t = E[∫₀^∞ f dB | 𝓕_t]`: the
conditional-expectation projection of the terminal `[0,∞)` integral `itoIntegralL2 f`
onto `𝓕_t`. The horizon-independent analogue of `itoProcessCLM`. -/
noncomputable def itoProcessL2Inf (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) →L[ℝ] Lp ℝ 2 μ :=
  ((lpMeas ℝ ℝ (natFiltration hBmeas t) 2 μ).subtypeL.comp
    (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t))).comp (itoIntegralL2 hB hBmeas)

/-- Unfold of the process to the `condExpL2` projection of the terminal integral
(coerced from the `𝓕_t`-measurable subspace into `Lp 2 μ`). -/
lemma itoProcessL2Inf_apply (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    itoProcessL2Inf hB t hBmeas f
      = (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t) (itoIntegralL2 hB hBmeas f) : Lp ℝ 2 μ) :=
  rfl

/-- **The unbounded-horizon Itô process is an L² martingale.** For `i ≤ j`,
`E[(f●B)_j | 𝓕_i] =ᵐ (f●B)_i` — directly from the conditional-expectation tower,
since each value is `E[∫₀^∞ f dB | 𝓕_k]`. -/
theorem itoProcessL2Inf_isMartingale (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) {i j : ℝ≥0} (hij : i ≤ j) :
    μ[(itoProcessL2Inf hB j hBmeas f : Ω → ℝ) | natFiltration hBmeas i]
      =ᵐ[μ] (itoProcessL2Inf hB i hBmeas f : Ω → ℝ) := by
  have hbridge : ∀ k : ℝ≥0,
      (itoProcessL2Inf hB k hBmeas f : Ω → ℝ)
        =ᵐ[μ] μ[(itoIntegralL2 hB hBmeas f : Ω → ℝ) | natFiltration hBmeas k] := by
    intro k
    rw [itoProcessL2Inf_apply]
    have h := (Lp.memLp (itoIntegralL2 hB hBmeas f)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) ((natFiltration hBmeas).le k)
    rwa [Lp.toLp_coeFn] at h
  calc μ[(itoProcessL2Inf hB j hBmeas f : Ω → ℝ) | natFiltration hBmeas i]
      =ᵐ[μ] μ[μ[(itoIntegralL2 hB hBmeas f : Ω → ℝ) | natFiltration hBmeas j]
              | natFiltration hBmeas i] := condExp_congr_ae (hbridge j)
    _ =ᵐ[μ] μ[(itoIntegralL2 hB hBmeas f : Ω → ℝ) | natFiltration hBmeas i] :=
        condExp_condExp_of_le ((natFiltration hBmeas).mono hij) ((natFiltration hBmeas).le j)
    _ =ᵐ[μ] (itoProcessL2Inf hB i hBmeas f : Ω → ℝ) := (hbridge i).symm

/-- **a.e.-adaptedness.** `(f●B)_t` is a.e. `𝓕_t`-measurable: it is the `condExpL2`
projection onto the `𝓕_t`-measurable subspace. -/
theorem itoProcessL2Inf_aeStronglyMeasurable (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    AEStronglyMeasurable[natFiltration hBmeas t]
      (itoProcessL2Inf hB t hBmeas f : Ω → ℝ) μ := by
  rw [itoProcessL2Inf_apply]
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t) (itoIntegralL2 hB hBmeas f)).2

/-- **The Itô-isometry contraction.** `‖(f●B)_t‖ ≤ ‖f‖`: conditional expectation is
an L² contraction and the terminal integral is an isometry (`itoIntegralL2_norm`). -/
theorem itoProcessL2Inf_norm_le (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    ‖itoProcessL2Inf hB t hBmeas f‖ ≤ ‖f‖ := by
  rw [itoProcessL2Inf_apply]
  exact (norm_condExpL2_le ((natFiltration hBmeas).le t) (itoIntegralL2 hB hBmeas f)).trans
    (itoIntegralL2_norm hB hBmeas f).le

/-! ## Step 2 — horizon consistency with the finite-horizon process

The crux relating `itoProcessL2Inf` (`[0,∞)`) to `itoProcessCLM` (`[0,T]`) is the
**Itô increment-independence**: `E[∫₀^∞ f dB | 𝓕_T] = ∫₀ᵀ f dB`. On the dense
simple processes this is concrete — the conditional expectation of the `[0,∞)`
integral onto `𝓕_t` is exactly the `[0,t]` truncation `(V●B)_t`, which is B1a's
martingale property applied past the simple process's (finite) support. -/

/-- **Bridge:** the `[0,∞)` integral of a simple process is its explicit simple
integral `itoSimpleLp V` (`extendOfNorm` on the dense embedding). -/
lemma itoIntegralL2_simpleAssembly (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    itoIntegralL2 hB hBmeas (simpleAssembly hBmeas V) = itoSimpleLp hB hBmeas V := by
  rw [itoIntegralL2, LinearMap.extendOfNorm_eq (simpleAssembly_denseRange (μ := μ) hBmeas)
    ⟨1, fun W ↦ by rw [one_mul]; exact (assembly_isometry hB hBmeas W).le⟩]
  rfl

/-- **Simple-process increment-independence (the step-2 core).** For a simple
process `V`, the conditional expectation of its `[0,∞)` integral onto `𝓕_t` is the
`[0,t]` truncation `(V●B)_t`: pick a horizon past `V`'s finite support, where the
`[0,∞)` integral coincides with the truncated process, and apply B1a's martingale
property (`condExp_itoSimple_eq`). The density lift to all `f ∈ Lp 2 trim_full`
(via a restriction CLM `Lp 2 trim_full → Lp 2 (trimMeasure_T T)` + `DenseRange`) is
the remaining work of step 2. -/
lemma condExp_itoIntegralL2_simple (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    μ[(itoIntegralL2 hB hBmeas (simpleAssembly hBmeas V) : Ω → ℝ) | natFiltration hBmeas t]
      =ᵐ[μ] fun ω ↦ itoSimpleProcess hBmeas V t ω := by
  have hbridge : (itoIntegralL2 hB hBmeas (simpleAssembly hBmeas V) : Ω → ℝ)
      =ᵐ[μ] itoSimple hBmeas V := by
    rw [itoIntegralL2_simpleAssembly]
    exact (memLp_itoSimple hB hBmeas V).coeFn_toLp
  exact (condExp_congr_ae hbridge).trans
    (condExp_itoSimple_eq hB (V.value.support.sup (fun p ↦ p.2)) t hBmeas V
      (fun p hp ↦ Finset.le_sup hp))

/-! ## Step 2 — horizon consistency

The `[0,∞)` process restricted to `[0,T]` is the finite-horizon process of the band-restricted
integrand. Both `f ↦ itoProcessL2Inf t f` and `f ↦ itoProcessCLM T t (restrictToBand T f)` are
continuous-linear in `f` and, on the dense simple processes, both reproduce `V`'s `[0,t]`
discrete Itô integral (`condExp_itoIntegralL2_simple` on the left;
`restrictToBand_simpleAssembly` + `itoProcessCLM_simpleProcessL2_T` on the right), so they
agree everywhere. -/

/-- **Horizon consistency.** For `t ≤ T`, the unbounded-horizon process equals the
finite-horizon process of the `[0,T]`-restricted integrand:
`(f●B)_t = (f|[0,T] ● B)_t`. -/
theorem itoProcessL2Inf_eq_itoProcessCLM (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) (ht : t ≤ T)
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    itoProcessL2Inf hB t hBmeas f
      = itoProcessCLM hB T t hBmeas (restrictToBand (μ := μ) T hBmeas f) := by
  refine congrFun (DenseRange.equalizer (simpleAssembly_denseRange (μ := μ) hBmeas)
    (itoProcessL2Inf hB t hBmeas).continuous
    ((itoProcessCLM hB T t hBmeas).comp (restrictToBand (μ := μ) T hBmeas)).continuous
    (funext fun V ↦ ?_)) f
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  refine Lp.ext ?_
  have hLHS : (itoProcessL2Inf hB t hBmeas (simpleAssembly hBmeas V) : Ω → ℝ)
      =ᵐ[μ] itoSimpleProcess hBmeas V t := by
    rw [itoProcessL2Inf_apply]
    have h := (Lp.memLp (itoIntegralL2 hB hBmeas (simpleAssembly hBmeas V))).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) ((natFiltration hBmeas).le t)
    rw [Lp.toLp_coeFn] at h
    exact h.trans (condExp_itoIntegralL2_simple hB t hBmeas V)
  have hRHS : (itoProcessCLM hB T t hBmeas
        (restrictToBand (μ := μ) T hBmeas (simpleAssembly hBmeas V)) : Ω → ℝ)
      =ᵐ[μ] itoSimpleProcess hBmeas V t := by
    rw [restrictToBand_simpleAssembly T hBmeas V]
    exact itoProcessCLM_simpleProcessL2_T hB T t hBmeas V ht
  exact hLHS.trans hRHS.symm

end ItoIntegralProcessL2Infinite
end MathFin
