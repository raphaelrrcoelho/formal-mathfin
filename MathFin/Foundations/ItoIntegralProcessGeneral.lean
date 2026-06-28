/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralProcessMartingale
public import MathFin.Foundations.ItoIntegralCLM

/-! # The general-integrand Itô integral as an L² martingale on `[0,T]` (B1b)

B1a built the simple-integrand Itô integral `t ↦ (V●B)_t` as a continuous L²
martingale. This file extends it to a **general** predictable integrand
`φ ∈ Lp ℝ 2 (trimMeasure_T T)` (= Degenne's `L2Predictable` on `[0,T]`) by
density: the process `t ↦ (φ●B)_t := ∫₀ᵗ φ dB` is a continuous L² martingale, with
the Itô contraction `‖(φ●B)_t‖ ≤ ‖φ‖` and the terminal Itô isometry
`‖(φ●B)_T‖ = ‖φ‖`. The explicit time-indexed isometry
`E[(φ●B)_t²] = ∫₀ᵗ E[φ_s²] ds` is proved in the companion module
`ItoIntegralProcessIsometry` (`itoProcessCLM_norm_sq`), by density-transferring the
band-restricted simple-process isometry against a band-truncation CLM.

The construction mirrors `ItoIntegralCLM.itoIntegralCLM_T`: extend the linear map
`V ↦ itoSimpleProcessLp V t` (B1a's t-process) along the *same* dense embedding
`simpleAssembly_T` via `LinearMap.extendOfNorm`. The only new analytic input is the
contraction bound `‖itoSimpleProcessLp V t‖ ≤ ‖simpleProcessL2_T V‖`, which holds
because `(V●B)_t = E[(V●B)_T | 𝓕_t]` (B1a's martingale + terminal agreement) and
conditional expectation is an L² contraction. The bridge to B1a is then
*definitional* (`extendOfNorm_eq`).

The infinite-horizon `[0,∞)` integral (σ-finite predictable exhaustion) is the
separate later milestone B2. -/

@[expose] public section

namespace MathFin
namespace ItoIntegralProcessGeneral

open MeasureTheory ProbabilityTheory
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- **The contraction bound** — the one new analytic input. For a `T`-bounded
simple process, the L² norm of the t-process `(V●B)_t` is at most that of its
embedding `simpleProcessL2_T V`: indeed `(V●B)_t = μ[(V●B)_T | 𝓕_t]` (B1a's
martingale at `t ≤ T`, with `(V●B)_T = itoSimple V` since `T` is past every right
endpoint), and conditional expectation is an L² contraction. This is the bound
`LinearMap.extendOfNorm` consumes to produce the general Itô integral CLM. -/
theorem itoSimpleProcessLp_norm_le (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (hVT : ∀ p ∈ V.value.support, p.2 ≤ T) :
    ‖itoSimpleProcessLp hB hBmeas V t‖ ≤ ‖simpleProcessL2_T (μ := μ) T hBmeas V‖ := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  -- `‖simpleProcessL2_T T V‖ = ‖itoSimpleLp V‖`: the T-Itô isometry on simple processes.
  have hnorm_eq : ‖simpleProcessL2_T (μ := μ) T hBmeas V‖ = ‖itoSimpleLp hB hBmeas V‖ :=
    (assembly_isometry_T hB T hBmeas ⟨V, hVT⟩).symm
  rw [hnorm_eq]
  -- `(V●B)_t = μ[itoSimple V | 𝓕_t]`: B1a's martingale at `t ≤ T' = t ⊔ T`, with
  -- `(V●B)_{T'} = itoSimple V` since `T'` is past every right endpoint.
  have hT'eq : itoSimpleProcess hBmeas V (max t T) = itoSimple hBmeas V :=
    itoSimpleProcess_eq_itoSimple hBmeas V fun p hp => (hVT p hp).trans (le_max_right t T)
  have hcond : (μ[fun ω => itoSimpleProcess hBmeas V (max t T) ω | natFiltration hBmeas t])
      =ᵐ[μ] fun ω => itoSimpleProcess hBmeas V t ω :=
    (itoSimpleProcess_isMartingale hB hBmeas V).2 t (max t T) (le_max_left t T)
  simp only [hT'eq] at hcond
  -- conditional expectation is an L² contraction.
  simp only [itoSimpleProcessLp, itoSimpleLp, Lp.norm_toLp]
  refine ENNReal.toReal_mono (memLp_itoSimple hB hBmeas V).2.ne ?_
  calc eLpNorm (itoSimpleProcess hBmeas V t) 2 μ
      = eLpNorm (μ[itoSimple hBmeas V | natFiltration hBmeas t]) 2 μ :=
        (eLpNorm_congr_ae hcond).symm
    _ ≤ eLpNorm (itoSimple hBmeas V) 2 μ := eLpNorm_condExp_le

/-- **B1a's t-process as a linear map** on the `T`-bounded simple processes,
`V ↦ (V●B)_t`. The target of the `extendOfNorm` extension. -/
noncomputable def itoProcessLM (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    TBoundedSP T hBmeas →ₗ[ℝ] Lp ℝ 2 μ where
  toFun V := itoSimpleProcessLp hB hBmeas V.val t
  map_add' V W := by
    show itoSimpleProcessLp hB hBmeas ((V + W).val) t = _
    rw [Submodule.coe_add, itoSimpleProcessLp, itoSimpleProcessLp, itoSimpleProcessLp,
        ← MemLp.toLp_add (memLp_itoSimpleProcess hB hBmeas V.val t)
          (memLp_itoSimpleProcess hB hBmeas W.val t)]
    congr 1
    exact itoSimpleProcess_add hBmeas V.val W.val t
  map_smul' c V := by
    show itoSimpleProcessLp hB hBmeas ((c • V).val) t = _
    rw [Submodule.coe_smul, itoSimpleProcessLp, itoSimpleProcessLp, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_itoSimpleProcess hB hBmeas V.val t)]
    congr 1
    exact itoSimpleProcess_smul hBmeas c V.val t

/-- **The general Itô integral as a CLM on `[0,T]`.** Extends B1a's t-process
`itoProcessLM` along the dense embedding `simpleAssembly_T` (the same one that
builds `itoIntegralCLM_T`), via `LinearMap.extendOfNorm` with the contraction
bound `itoSimpleProcessLp_norm_le`. For `φ ∈ L²(predictable, [0,T])`, this is
`∫₀ᵗ φ dB ∈ L²(μ)`. -/
noncomputable def itoProcessCLM (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) →L[ℝ] Lp ℝ 2 μ :=
  (itoProcessLM hB T t hBmeas).extendOfNorm (simpleAssembly_T (μ := μ) T hBmeas)

/-- **The bridge to B1a (definitional).** On the embedding of a `T`-bounded simple
process, the general CLM reproduces B1a's t-process `(V●B)_t`. Immediate from
`extendOfNorm_eq` + the contraction bound + `simpleAssembly_T_denseRange`. -/
theorem itoProcessCLM_simpleAssembly_T (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP T hBmeas) :
    itoProcessCLM hB T t hBmeas (simpleAssembly_T (μ := μ) T hBmeas V)
      = itoSimpleProcessLp hB hBmeas V.val t := by
  rw [itoProcessCLM, LinearMap.extendOfNorm_eq (simpleAssembly_T_denseRange (μ := μ) T hBmeas)
    ⟨1, fun W => by rw [one_mul]; exact itoSimpleProcessLp_norm_le hB T t hBmeas W.val W.property⟩]
  rfl

/-- The existing terminal CLM on a simple embedding reproduces `itoSimpleLp` (the
`ItoIntegralCLM` analogue of `itoProcessCLM_simpleAssembly_T`). -/
theorem itoIntegralCLM_T_simpleAssembly_T (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : TBoundedSP T hBmeas) :
    itoIntegralCLM_T hB T hBmeas (simpleAssembly_T (μ := μ) T hBmeas V)
      = itoSimpleLp hB hBmeas V.val := by
  rw [itoIntegralCLM_T, LinearMap.extendOfNorm_eq (simpleAssembly_T_denseRange (μ := μ) T hBmeas)
    ⟨1, fun W => by rw [one_mul]; exact (assembly_isometry_T hB T hBmeas W).le⟩]
  rfl

omit [IsProbabilityMeasure μ] in
/-- B1a's martingale to the terminal: `μ[itoSimple V | 𝓕_t] = (V●B)_t` for
`T`-bounded `V` (`(V●B)_{T'} = itoSimple V` at `T' = t ⊔ T`). -/
theorem condExp_itoSimple_eq (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (hVT : ∀ p ∈ V.value.support, p.2 ≤ T) :
    μ[itoSimple hBmeas V | natFiltration hBmeas t]
      =ᵐ[μ] fun ω => itoSimpleProcess hBmeas V t ω := by
  have hT'eq : itoSimpleProcess hBmeas V (max t T) = itoSimple hBmeas V :=
    itoSimpleProcess_eq_itoSimple hBmeas V fun p hp => (hVT p hp).trans (le_max_right t T)
  simpa only [hT'eq] using (itoSimpleProcess_isMartingale hB hBmeas V).2 t (max t T) (le_max_left t T)

/-- **The key identity.** The general Itô integral at time `t` is the
conditional-expectation projection of its terminal value `∫₀ᵀ φ dB` onto `𝓕_t`:
`(φ●B)_t = condExpL2 𝓕_t (itoIntegralCLM_T T φ)`. On the dense simple processes
this is B1a's martingale `(V●B)_t = μ[itoSimple V | 𝓕_t]`; both sides are
continuous-linear in `φ`, so it holds for all `φ`. Adaptedness and the martingale
property are corollaries. -/
theorem itoProcessCLM_eq_condExpL2 (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    itoProcessCLM hB T t hBmeas φ
      = (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t)
          (itoIntegralCLM_T hB T hBmeas φ) : Lp ℝ 2 μ) := by
  have hcont_R : Continuous fun ψ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) =>
      (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t)
        (itoIntegralCLM_T hB T hBmeas ψ) : Lp ℝ 2 μ) :=
    (continuous_subtype_val.comp (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t)).continuous).comp
      (itoIntegralCLM_T hB T hBmeas).continuous
  refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (μ := μ) T hBmeas)
    (itoProcessCLM hB T t hBmeas).continuous hcont_R (funext fun V => ?_)) φ
  simp only [Function.comp_apply]
  rw [itoProcessCLM_simpleAssembly_T, itoIntegralCLM_T_simpleAssembly_T]
  refine Lp.ext ?_
  simp only [itoSimpleProcessLp, itoSimpleLp]
  filter_upwards [(memLp_itoSimpleProcess hB hBmeas V.val t).coeFn_toLp,
    (memLp_itoSimple hB hBmeas V.val).condExpL2_ae_eq_condExp (𝕜 := ℝ) ((natFiltration hBmeas).le t),
    condExp_itoSimple_eq hB T t hBmeas V.val V.property] with ω hω1 hω2 hω3
  rw [hω1, ← hω3, hω2]

/-- **a.e.-adaptedness.** `(φ●B)_t` is a.e. `𝓕_t`-measurable: by the key identity it
is (a `condExpL2` projection onto) the `𝓕_t`-measurable subspace. -/
theorem itoProcessCLM_aeStronglyMeasurable (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    AEStronglyMeasurable[natFiltration hBmeas t]
      (itoProcessCLM hB T t hBmeas φ : Ω → ℝ) μ := by
  rw [itoProcessCLM_eq_condExpL2]
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t) (itoIntegralCLM_T hB T hBmeas φ)).2

/-- **The general Itô integral is an L² martingale (B1b).** For `i ≤ j`,
`μ[(φ●B)_j | 𝓕_i] =ᵐ (φ●B)_i`. By the key identity each `(φ●B)_k` is the `𝓕_k`-
conditional expectation of the terminal integral `∫₀ᵀ φ dB`, so the martingale
property is the conditional-expectation tower `μ[μ[X | 𝓕_j] | 𝓕_i] = μ[X | 𝓕_i]`. -/
theorem itoIntegralProcessGen_isMartingale (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {i j : ℝ≥0} (hij : i ≤ j) :
    μ[(itoProcessCLM hB T j hBmeas φ : Ω → ℝ) | natFiltration hBmeas i]
      =ᵐ[μ] (itoProcessCLM hB T i hBmeas φ : Ω → ℝ) := by
  -- each value is the conditional expectation of the terminal integral `X`.
  have hbridge : ∀ k : ℝ≥0,
      ((condExpL2 ℝ ℝ ((natFiltration hBmeas).le k)
          (itoIntegralCLM_T hB T hBmeas φ) : Lp ℝ 2 μ) : Ω → ℝ)
        =ᵐ[μ] μ[(itoIntegralCLM_T hB T hBmeas φ : Ω → ℝ) | natFiltration hBmeas k] := by
    intro k
    have h := (Lp.memLp (itoIntegralCLM_T hB T hBmeas φ)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) ((natFiltration hBmeas).le k)
    rwa [Lp.toLp_coeFn] at h
  rw [itoProcessCLM_eq_condExpL2, itoProcessCLM_eq_condExpL2]
  calc μ[((condExpL2 ℝ ℝ ((natFiltration hBmeas).le j)
            (itoIntegralCLM_T hB T hBmeas φ) : Lp ℝ 2 μ) : Ω → ℝ) | natFiltration hBmeas i]
      =ᵐ[μ] μ[μ[(itoIntegralCLM_T hB T hBmeas φ : Ω → ℝ) | natFiltration hBmeas j]
              | natFiltration hBmeas i] := condExp_congr_ae (hbridge j)
    _ =ᵐ[μ] μ[(itoIntegralCLM_T hB T hBmeas φ : Ω → ℝ) | natFiltration hBmeas i] :=
        condExp_condExp_of_le ((natFiltration hBmeas).mono hij) ((natFiltration hBmeas).le j)
    _ =ᵐ[μ] ((condExpL2 ℝ ℝ ((natFiltration hBmeas).le i)
              (itoIntegralCLM_T hB T hBmeas φ) : Lp ℝ 2 μ) : Ω → ℝ) := (hbridge i).symm

/-- **The Itô-isometry contraction.** `‖(φ●B)_t‖ ≤ ‖φ‖`: by the key identity
`(φ●B)_t` is the `𝓕_t`-conditional expectation of `∫₀ᵀ φ dB`, and conditional
expectation is an L² contraction; the terminal integral is an isometry
(`itoIntegralCLM_T_norm`). -/
theorem itoProcessCLM_norm_le (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ‖itoProcessCLM hB T t hBmeas φ‖ ≤ ‖φ‖ := by
  have hae : (itoProcessCLM hB T t hBmeas φ : Ω → ℝ)
      =ᵐ[μ] μ[(itoIntegralCLM_T hB T hBmeas φ : Ω → ℝ) | natFiltration hBmeas t] := by
    rw [itoProcessCLM_eq_condExpL2]
    have h := (Lp.memLp (itoIntegralCLM_T hB T hBmeas φ)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) ((natFiltration hBmeas).le t)
    rwa [Lp.toLp_coeFn] at h
  rw [Lp.norm_def, ← itoIntegralCLM_T_norm hB T hBmeas φ, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.memLp (itoIntegralCLM_T hB T hBmeas φ)).2.ne ?_
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_condExp_le

/-- **At the terminal time the process is the terminal integral.** `(φ●B)_T = itoIntegralCLM_T φ`
as `Lp` elements: both are continuous-linear in `φ` and reproduce `itoSimple V` on the dense
simple processes (`(V●B)_T = itoSimple V`). -/
theorem itoProcessCLM_terminal_eq (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    itoProcessCLM hB T T hBmeas φ = itoIntegralCLM_T hB T hBmeas φ :=
  congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (μ := μ) T hBmeas)
    (itoProcessCLM hB T T hBmeas).continuous (itoIntegralCLM_T hB T hBmeas).continuous
    (funext fun V => by
      simp only [Function.comp_apply, itoProcessCLM_simpleAssembly_T,
        itoIntegralCLM_T_simpleAssembly_T, itoSimpleProcessLp, itoSimpleLp,
        itoSimpleProcess_eq_itoSimple hBmeas V.val (fun p hp => V.property p hp)])) φ

/-- **Terminal Itô isometry.** At the horizon the process is the terminal integral
(`itoProcessCLM_terminal_eq`), so `‖(φ●B)_T‖ = ‖φ‖` exactly. -/
theorem itoProcessCLM_norm_terminal (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ‖itoProcessCLM hB T T hBmeas φ‖ = ‖φ‖ := by
  rw [itoProcessCLM_terminal_eq hB T hBmeas φ, itoIntegralCLM_T_norm hB T hBmeas φ]

/-- **L²-continuity.** `t ↦ (φ●B)_t` is continuous into `Lp ℝ 2 μ`. The simple-
process integrals `t ↦ (Vₙ●B)_t` (continuous by B1a's
`itoSimpleProcessLp_l2_continuous`) approximate it *uniformly in `t`* — the
contraction `‖(φ●B)_t − (Vₙ●B)_t‖ ≤ ‖φ − Vₙ‖` is `t`-free — so the limit is
continuous (`TendstoUniformly.continuous`). -/
theorem itoIntegralProcessGen_l2_continuous (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Continuous (fun t => itoProcessCLM hB T t hBmeas φ) := by
  -- approximate `φ` by a sequence of simple-process embeddings (dense range).
  obtain ⟨g, hg_range, hg_lim⟩ := mem_closure_iff_seq_limit.mp
    ((simpleAssembly_T_denseRange (μ := μ) T hBmeas).closure_range.ge (Set.mem_univ φ))
  choose V hV using hg_range
  -- each approximant's process is continuous in `t` (bridge to B1a's continuity).
  have hcont_n : ∀ n, Continuous (fun t => itoProcessCLM hB T t hBmeas (g n)) := fun n => by
    simp only [← hV n, itoProcessCLM_simpleAssembly_T]
    exact itoSimpleProcessLp_l2_continuous hB hBmeas (V n).val
  -- uniform convergence: `dist ≤ ‖φ − gₙ‖ → 0`, independent of `t`.
  have huniform : TendstoUniformly (fun n t => itoProcessCLM hB T t hBmeas (g n))
      (fun t => itoProcessCLM hB T t hBmeas φ) Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hnorm_lim : Filter.Tendsto (fun n => ‖φ - g n‖) Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := φ)).sub hg_lim
      simpa using this.norm
    filter_upwards [hnorm_lim.eventually (eventually_lt_nhds hε)] with n hn t
    rw [dist_eq_norm, ← map_sub]
    exact lt_of_le_of_lt (itoProcessCLM_norm_le hB T t hBmeas (φ - g n)) hn
  exact huniform.continuous (Filter.Eventually.of_forall hcont_n).frequently

end ItoIntegralProcessGeneral
end MathFin
