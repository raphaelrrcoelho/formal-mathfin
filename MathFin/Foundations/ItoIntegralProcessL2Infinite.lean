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

open ItoIntegralL2 ItoIntegralProcess ItoIntegralProcessGeneral

/-! ## Restriction of an L² function to a sub-measure (generic) -/

section RestrictLp
variable {α : Type*} [MeasurableSpace α] (ν : Measure α) (s : Set α)

/-- **Restriction to a sub-measure as a CLM.** For `f ∈ Lp 2 ν` the *same* function
lies in `Lp 2 (ν.restrict s)` with no larger norm (restricting the measure can only
shrink the `L²` norm), so `f ↦ f` is a norm-`≤ 1` continuous linear map
`Lp 2 ν →L[ℝ] Lp 2 (ν.restrict s)`. Mathlib has `MemLp.restrict` but no packaged
CLM; generic measure theory, a natural upstream candidate. -/
noncomputable def restrictLp : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 (ν.restrict s) :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).restrict s).toLp
      map_add' := fun f g => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).restrict s),
          Lp.coeFn_add (((Lp.memLp f).restrict s).toLp) (((Lp.memLp g).restrict s).toLp),
          MemLp.coeFn_toLp ((Lp.memLp f).restrict s),
          MemLp.coeFn_toLp ((Lp.memLp g).restrict s),
          ae_restrict_of_ae (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.add_apply]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).restrict s),
          Lp.coeFn_smul c (((Lp.memLp f).restrict s).toLp),
          MemLp.coeFn_toLp ((Lp.memLp f).restrict s),
          ae_restrict_of_ae (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
        simp only [h1, h2, h3, h4, Pi.smul_apply, RingHom.id_apply] }
    1 (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.memLp f).2.ne ?_
      rw [eLpNorm_congr_ae (MemLp.coeFn_toLp ((Lp.memLp f).restrict s))]
      exact eLpNorm_mono_measure _ Measure.restrict_le_self)

@[simp] lemma restrictLp_coeFn (f : Lp ℝ 2 ν) :
    ⇑(restrictLp ν s f) =ᵐ[ν.restrict s] ⇑f := by
  simp only [restrictLp, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

end RestrictLp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

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
    ⟨1, fun W => by rw [one_mul]; exact (assembly_isometry hB hBmeas W).le⟩]
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
      =ᵐ[μ] fun ω => itoSimpleProcess hBmeas V t ω := by
  have hbridge : (itoIntegralL2 hB hBmeas (simpleAssembly hBmeas V) : Ω → ℝ)
      =ᵐ[μ] itoSimple hBmeas V := by
    rw [itoIntegralL2_simpleAssembly]
    exact (memLp_itoSimple hB hBmeas V).coeFn_toLp
  exact (condExp_congr_ae hbridge).trans
    (condExp_itoSimple_eq hB (V.value.support.sup (fun p => p.2)) t hBmeas V
      (fun p hp => Finset.le_sup hp))

end ItoIntegralProcessL2Infinite
end MathFin
