/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.PointwiseBracket

/-! # The bracket is adapted, and it compensates `M²`

`PointwiseBracket` delivers `⟨M⟩_b − ⟨M⟩_a = ∫_a^b φ_u(ω)² du` (`bracketRep`) and the conditional
identity `μ[(M_b − M_a)² | 𝓕_a] =ᵐ μ[⟨M⟩_b − ⟨M⟩_a | 𝓕_a]`, and explicitly does *not* claim the
bracket adapted. This file supplies exactly that, and cashes it:

  `μ[M_b² − ⟨M⟩_b | 𝓕_a] =ᵐ M_a² − ⟨M⟩_a`   (`condExp_sq_sub_bracket`),

i.e. `M² − ⟨M⟩` is a martingale — the property that makes `⟨M⟩` *the* compensator of `M²` rather
than a formula with a suggestive name.

## Why adaptedness is not free

`⇑φ` is strongly measurable for the *predictable* σ-algebra on `ℝ≥0 × Ω`, which mixes all of
`𝓕_s`, `s` arbitrary; nothing about it is `𝓕_b`-measurable on its own. What is true is a **trace**
statement (`measurableSet_inter_band`): intersected with the band `(a,b] × Ω`, every predictable
set is `Borel(ℝ≥0) ⊗ 𝓕_b`-measurable — on a generator `(c,d] × F` the coefficient's index `c` is
either `≤ b`, and then `F ∈ 𝓕_c ⊆ 𝓕_b`, or `> b`, and then the intersection is empty. Both cases
are decided by the *left* endpoint, which is exactly the asymmetry predictability buys.

Clamping the squared representative to the band therefore makes it product-measurable at `b`
(`measurable_bandSqClamped`), and integrating the time variable out
(`StronglyMeasurable.integral_prod_right'`) leaves an honestly `𝓕_b`-measurable function of `ω`.

## What that unlocks

`bracketProcess t = ⟨M⟩_{t∧T}` is then a genuine adapted process (`bracketProcess_adapted`), a.e.
nondecreasing and starting at `0`, and the conditional identity rearranges into the compensator
statement above: expand `(M_b − M_a)²`, pull `M_a` out of the cross term with the martingale
property `μ[M_b|𝓕_a] =ᵐ M_a`, and replace `⟨M⟩_b − ⟨M⟩_a` by its increment using band additivity.

## Honest scope

Still no pathwise quadratic variation: `⟨M⟩` is the ω-wise `∫φ²`, and nothing here identifies it
with a limit of sums along partitions. `bracketProcess` is adapted and a.e. nondecreasing; it is
not claimed continuous, and `M² − ⟨M⟩` is delivered as the conditional identity, not as a bundled
`Martingale` structure (the `Lp`-valued `M` supplies only a.e. adaptedness, which `Martingale`
does not accept — see `MarketCompletenessInPrice.pricePathCondExp` for the standing workaround).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal
open ItoIntegralL2 ItoIntegralCLM ItoIntegralAgainstMartingale
open ItoIntegralProcessGeneral PointwiseBracket

namespace BracketCompensator

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The trace of the predictable σ-algebra on a band -/

/-- The product σ-algebra `Borel(ℝ≥0) ⊗ 𝓕_b` — the one in which "clamped to `(·,b]`" makes a
predictable integrand measurable. Reducible, so it is transparent to defeq. -/
@[reducible] private noncomputable def bandAlg (hBmeas : ∀ t, Measurable (B t)) (b : ℝ≥0) :
    MeasurableSpace (ℝ≥0 × Ω) :=
  @Prod.instMeasurableSpace ℝ≥0 Ω _ (natFiltration hBmeas b)

omit [IsProbabilityMeasure μ] in
/-- The band `(a,b] × Ω` is `Borel(ℝ≥0) ⊗ 𝓕_b`-measurable. -/
private theorem measurableSet_band (hBmeas : ∀ t, Measurable (B t)) (a b : ℝ≥0) :
    MeasurableSet[bandAlg (mΩ := mΩ) hBmeas b] (Set.Ioc a b ×ˢ (Set.univ : Set Ω)) :=
  @MeasurableSet.prod ℝ≥0 Ω _ (natFiltration hBmeas b) _ _ measurableSet_Ioc
    (@MeasurableSet.univ Ω (natFiltration hBmeas b))

/-- **The trace σ-algebra**: the sets whose intersection with the band `(a,b] × Ω` is
`Borel(ℝ≥0) ⊗ 𝓕_b`-measurable. It is a σ-algebra because intersecting with a fixed measurable
band commutes with countable unions and turns complements into differences — which is what lets
the trace statement below be proved by `generateFrom_le` on the predictable generators, with no
induction over `MeasurableSet` at all. -/
@[reducible] private def traceAlg (hBmeas : ∀ t, Measurable (B t)) (a b : ℝ≥0) :
    MeasurableSpace (ℝ≥0 × Ω) where
  MeasurableSet' S :=
    MeasurableSet[bandAlg (mΩ := mΩ) hBmeas b] (S ∩ Set.Ioc a b ×ˢ (Set.univ : Set Ω))
  measurableSet_empty := by
    rw [Set.empty_inter]; exact @MeasurableSet.empty _ (bandAlg (mΩ := mΩ) hBmeas b)
  measurableSet_compl S hS := by
    rw [show Sᶜ ∩ Set.Ioc a b ×ˢ (Set.univ : Set Ω)
        = Set.Ioc a b ×ˢ (Set.univ : Set Ω) \ (S ∩ Set.Ioc a b ×ˢ (Set.univ : Set Ω)) from by
      ext z; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]; tauto]
    exact (measurableSet_band hBmeas a b).diff hS
  measurableSet_iUnion f hf := by
    rw [Set.iUnion_inter]; exact MeasurableSet.iUnion hf

omit [IsProbabilityMeasure μ] in
/-- **Predictable sets, traced onto `(a,b] × Ω`, are product-measurable at `b`.** On a generator
`(c,d] × F` the coefficient index `c` decides: either `c ≤ b`, and then `F ∈ 𝓕_c ⊆ 𝓕_b`, or
`c > b`, and then `(c,d] ∩ (a,b] = ∅`. The `{0} × F₀` generator meets the band nowhere, since
`0 ∉ (a,b]` in `ℝ≥0`. This asymmetry — the *left* endpoint carrying the measurability — is
exactly what predictability buys, and it is the only reason the bracket ends up adapted. -/
private theorem predictable_le_traceAlg (hBmeas : ∀ t, Measurable (B t)) (a b : ℝ≥0) :
    (natFiltration (mΩ := mΩ) hBmeas).predictable ≤ traceAlg (mΩ := mΩ) hBmeas a b := by
  rw [← generateFrom_predictableRect hBmeas]
  refine MeasurableSpace.generateFrom_le ?_
  rintro S (⟨F₀, _hF₀, rfl⟩ | ⟨c, d, _hcd, F, hF, rfl⟩)
  · change MeasurableSet[bandAlg (mΩ := mΩ) hBmeas b]
      (({(0 : ℝ≥0)} ×ˢ F₀) ∩ Set.Ioc a b ×ˢ (Set.univ : Set Ω))
    rw [Set.prod_inter_prod,
      show ({(0 : ℝ≥0)} ∩ Set.Ioc a b : Set ℝ≥0) = ∅ from
        Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
          absurd (hx.1 ▸ hx.2.1 : a < (0 : ℝ≥0)) (by simp),
      Set.empty_prod]
    exact @MeasurableSet.empty _ (bandAlg (mΩ := mΩ) hBmeas b)
  · change MeasurableSet[bandAlg (mΩ := mΩ) hBmeas b]
      ((Set.Ioc c d ×ˢ F) ∩ Set.Ioc a b ×ˢ (Set.univ : Set Ω))
    rw [Set.prod_inter_prod, Set.Ioc_inter_Ioc, Set.inter_univ]
    by_cases hcb : c ≤ b
    · exact @MeasurableSet.prod ℝ≥0 Ω _ (natFiltration hBmeas b) _ _ measurableSet_Ioc
        ((natFiltration hBmeas).mono hcb F hF)
    · push Not at hcb
      rw [show Set.Ioc (max c a) (min d b) = (∅ : Set ℝ≥0) from
        Set.Ioc_eq_empty (not_lt.mpr (((min_le_right d b).trans hcb.le).trans
          (le_max_left c a))), Set.empty_prod]
      exact @MeasurableSet.empty _ (bandAlg (mΩ := mΩ) hBmeas b)

omit [IsProbabilityMeasure μ] in
/-- The squared representative clamped to the band is `Borel(ℝ≥0) ⊗ 𝓕_b`-measurable: the trace
statement, read through preimages of the indicator. -/
private theorem measurable_bandSqClamped (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (a b : ℝ≥0) :
    Measurable[bandAlg (mΩ := mΩ) hBmeas b]
      ((Set.Ioc a b ×ˢ (Set.univ : Set Ω)).indicator
        fun z ↦ ((φ : ℝ≥0 × Ω → ℝ) z) ^ 2) := by
  have hsq : Measurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      (fun z : ℝ≥0 × Ω ↦ ((φ : ℝ≥0 × Ω → ℝ) z) ^ 2) :=
    ((Lp.stronglyMeasurable φ).pow 2).measurable
  intro A hA
  rw [Set.indicator_preimage]
  refine MeasurableSet.union ?_ ?_
  · have h : MeasurableSet[bandAlg (mΩ := mΩ) hBmeas b]
        ((fun z : ℝ≥0 × Ω ↦ ((φ : ℝ≥0 × Ω → ℝ) z) ^ 2) ⁻¹' A
          ∩ Set.Ioc a b ×ˢ (Set.univ : Set Ω)) :=
      predictable_le_traceAlg (mΩ := mΩ) hBmeas a b _ (hsq hA)
    exact h
  · by_cases h0 : (0 : ℝ) ∈ A
    · rw [show (0 : ℝ≥0 × Ω → ℝ) ⁻¹' A = Set.univ from Set.eq_univ_of_forall fun _ ↦ h0,
        ← Set.compl_eq_univ_sdiff]
      exact (measurableSet_band hBmeas a b).compl
    · rw [show (0 : ℝ≥0 × Ω → ℝ) ⁻¹' A = ∅ from
        Set.eq_empty_iff_forall_notMem.mpr fun _ hx ↦ h0 hx, Set.empty_sdiff]
      exact @MeasurableSet.empty _ (bandAlg (mΩ := mΩ) hBmeas b)

/-! ### The bracket is adapted -/

/-- Integrating the time variable out of a `Borel(ℝ≥0) ⊗ m`-measurable integrand leaves an
`m`-measurable function of the sample. Stated for a bare `m` on a bare type, so that no `μ`- or
`mΩ`-typed term is in scope while the ambient instance is swapped. -/
private theorem measurable_integral_section {Ω' : Type*} (m : MeasurableSpace Ω')
    (g : ℝ≥0 × Ω' → ℝ)
    (hg : Measurable[@Prod.instMeasurableSpace ℝ≥0 Ω' _ m] g) :
    Measurable[m] fun ω ↦ ∫ u, g (u, ω) ∂ItoIntegralL2.timeMeasure := by
  letI : MeasurableSpace Ω' := m
  exact ((hg.comp measurable_swap).stronglyMeasurable.integral_prod_right').measurable

omit [IsProbabilityMeasure μ] in
/-- **The bracket increment is `𝓕_b`-measurable.** Clamp the squared representative to the band,
where it is product-measurable at `b` (`measurable_bandSqClamped`), then integrate the time
variable out. No hypothesis relating `b` to `T`: the band is what it is. -/
theorem measurable_bracketRep (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (a b : ℝ≥0) :
    Measurable[natFiltration hBmeas b] (bracketRep (μ := μ) T hBmeas φ a b) := by
  have hfun : bracketRep (μ := μ) T hBmeas φ a b
      = fun ω ↦ ∫ u, (Set.Ioc a b ×ˢ (Set.univ : Set Ω)).indicator
          (fun z ↦ ((φ : ℝ≥0 × Ω → ℝ) z) ^ 2) (u, ω) ∂ItoIntegralL2.timeMeasure := by
    funext ω
    show (∫ u in Set.Ioc a b, ((φ : ℝ≥0 × Ω → ℝ) (u, ω)) ^ 2 ∂ItoIntegralL2.timeMeasure)
      = ∫ u, (Set.Ioc a b ×ˢ (Set.univ : Set Ω)).indicator
          (fun z ↦ ((φ : ℝ≥0 × Ω → ℝ) z) ^ 2) (u, ω) ∂ItoIntegralL2.timeMeasure
    rw [← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    show (Set.Ioc a b).indicator (fun u' ↦ ((φ : ℝ≥0 × Ω → ℝ) (u', ω)) ^ 2) u
      = (Set.Ioc a b ×ˢ (Set.univ : Set Ω)).indicator
          (fun z ↦ ((φ : ℝ≥0 × Ω → ℝ) z) ^ 2) (u, ω)
    by_cases hu : u ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem
        (show (u, ω) ∈ Set.Ioc a b ×ˢ (Set.univ : Set Ω) from ⟨hu, Set.mem_univ ω⟩)]
    · rw [Set.indicator_of_notMem hu,
        Set.indicator_of_notMem (fun h ↦ hu (Set.mem_prod.mp h).1)]
  rw [hfun]
  exact measurable_integral_section (natFiltration hBmeas b) _
    (measurable_bandSqClamped T hBmeas φ a b)

/-- **The bracket as a process**: `⟨M⟩_t = ∫₀^{t∧T} φ_u(ω)² du`. Clamped at `T` because the
representative of `φ` carries no information past the horizon. -/
noncomputable def bracketProcess (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  bracketRep (μ := μ) T hBmeas φ 0 (min t T) ω

omit [IsProbabilityMeasure μ] in
/-- `bracketProcess` unfolded — the clamped bracket increment from the origin. -/
theorem bracketProcess_def (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (t : ℝ≥0) :
    bracketProcess (μ := μ) T hBmeas φ t = bracketRep (μ := μ) T hBmeas φ 0 (min t T) := rfl

omit [IsProbabilityMeasure μ] in
/-- On `[0,T]` the process is the bracket increment from the origin. -/
theorem bracketProcess_eq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {t : ℝ≥0} (htT : t ≤ T) :
    bracketProcess (μ := μ) T hBmeas φ t = bracketRep (μ := μ) T hBmeas φ 0 t := by
  rw [bracketProcess_def, min_eq_left htT]

omit [IsProbabilityMeasure μ] in
/-- **The bracket process is adapted** — the point of this file's first half. -/
theorem bracketProcess_adapted (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Adapted (natFiltration hBmeas) (bracketProcess (μ := μ) T hBmeas φ) := by
  intro t
  exact (measurable_bracketRep T hBmeas φ 0 (min t T)).mono
    ((natFiltration hBmeas).mono (min_le_left t T)) le_rfl

omit [IsProbabilityMeasure μ] in
/-- The bracket process starts at zero. -/
@[simp] theorem bracketProcess_zero (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (ω : Ω) :
    bracketProcess (μ := μ) T hBmeas φ 0 ω = 0 := by
  show bracketRep (μ := μ) T hBmeas φ 0 (min 0 T) ω = 0
  rw [min_eq_left (show (0 : ℝ≥0) ≤ T from bot_le), bracketRep, Set.Ioc_self,
    Measure.restrict_empty, integral_zero_measure]

/-- The bracket process is a.e. nondecreasing: its increments are the nonnegative
`bracketRep`. -/
theorem bracketProcess_mono (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) :
    ∀ᵐ ω ∂μ, bracketProcess (μ := μ) T hBmeas φ s ω
      ≤ bracketProcess (μ := μ) T hBmeas φ t ω := by
  rw [bracketProcess_eq T hBmeas φ (hst.trans htT), bracketProcess_eq T hBmeas φ htT]
  exact bracketRep_mono T hBmeas φ (show (0 : ℝ≥0) ≤ s from bot_le) hst htT

/-! ### The compensator identity -/

/-- **`M² − ⟨M⟩` is a martingale.** For `M = φ●B` on `[0,T]` and `a ≤ b ≤ T`,

  `μ[M_b² − ⟨M⟩_b | 𝓕_a] =ᵐ M_a² − ⟨M⟩_a`,

which is what makes `⟨M⟩` *the* compensator of `M²` rather than a formula with a suggestive name.

Three inputs meet here. Expanding `M_b² = (M_b − M_a)² + 2(M_b M_a − M_a²) + M_a²`, the middle
term has vanishing conditional expectation: `μ[M_b·M_a | 𝓕_a] =ᵐ M_a·μ[M_b|𝓕_a] =ᵐ M_a²` by
pull-out and the martingale property `itoIntegralProcessGen_isMartingale`. The first term is
`condExp_band_second_moment`, the conditional bracket identity. And `⟨M⟩_b − ⟨M⟩_a` may be split
off the conditional expectation only because `⟨M⟩_a` is now **adapted**
(`measurable_bracketRep`) — the step this file's first half exists for. -/
theorem condExp_sq_sub_bracket (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) :
    (μ[fun ω ↦ (⇑(itoProcessCLM hB T b hBmeas φ) ω) ^ 2
        - bracketProcess (μ := μ) T hBmeas φ b ω | natFiltration hBmeas a])
      =ᵐ[μ] fun ω ↦ (⇑(itoProcessCLM hB T a hBmeas φ) ω) ^ 2
        - bracketProcess (μ := μ) T hBmeas φ a ω := by
  have haT : a ≤ T := hab.trans hbT
  rw [bracketProcess_eq T hBmeas φ hbT, bracketProcess_eq T hBmeas φ haT]
  set Ma : Ω → ℝ := ⇑(itoProcessCLM hB T a hBmeas φ) with hMadef
  set Mb : Ω → ℝ := ⇑(itoProcessCLM hB T b hBmeas φ) with hMbdef
  set Aa : Ω → ℝ := bracketRep (μ := μ) T hBmeas φ 0 a with hAadef
  set Ab : Ω → ℝ := bracketRep (μ := μ) T hBmeas φ 0 b with hAbdef
  have hMa2 : Integrable (fun ω ↦ Ma ω ^ 2) μ :=
    (Lp.memLp (itoProcessCLM hB T a hBmeas φ)).integrable_sq
  have hMb2 : Integrable (fun ω ↦ Mb ω ^ 2) μ :=
    (Lp.memLp (itoProcessCLM hB T b hBmeas φ)).integrable_sq
  have hMbi : Integrable Mb μ :=
    (Lp.memLp (itoProcessCLM hB T b hBmeas φ)).integrable one_le_two
  have hcross : Integrable (fun ω ↦ Mb ω * Ma ω) μ :=
    (MemLp.mul (hf := (Lp.memLp (itoProcessCLM hB T a hBmeas φ)))
      (hφ := (Lp.memLp (itoProcessCLM hB T b hBmeas φ)))).integrable le_rfl
  have hAai : Integrable Aa μ := integrable_bracketRep T hBmeas φ haT
  have hAbi : Integrable Ab μ := integrable_bracketRep T hBmeas φ hbT
  have hCi : Integrable (fun ω ↦ Mb ω * Ma ω - Ma ω ^ 2) μ := hcross.sub hMa2
  have hdiff : Integrable (fun ω ↦ (Mb ω - Ma ω) ^ 2) μ := by
    rw [show (fun ω ↦ (Mb ω - Ma ω) ^ 2)
        = fun ω ↦ Mb ω ^ 2 - (Mb ω * Ma ω + Mb ω * Ma ω) + Ma ω ^ 2 from
      funext fun ω ↦ by ring]
    exact (hMb2.sub (hcross.add hcross)).add hMa2
  have hMaAe : AEStronglyMeasurable[natFiltration hBmeas a] Ma μ :=
    itoProcessCLM_aeStronglyMeasurable hB T a hBmeas φ
  have hAaAe : AEStronglyMeasurable[natFiltration hBmeas a] Aa μ :=
    (measurable_bracketRep T hBmeas φ 0 a).stronglyMeasurable.aestronglyMeasurable
  -- the cross term collapses onto `M_a²` by pull-out plus the martingale property
  have e1 : (μ[fun ω ↦ Mb ω * Ma ω | natFiltration hBmeas a]) =ᵐ[μ] fun ω ↦ Ma ω * Ma ω := by
    refine (condExp_mul_of_aestronglyMeasurable_right hMaAe hcross hMbi).trans ?_
    filter_upwards [itoIntegralProcessGen_isMartingale hB T hBmeas φ hab] with ω hω
    show (μ[Mb | natFiltration hBmeas a]) ω * Ma ω = Ma ω * Ma ω
    rw [hω]
  have e2 : (μ[fun ω ↦ Ma ω ^ 2 | natFiltration hBmeas a]) =ᵐ[μ] fun ω ↦ Ma ω ^ 2 :=
    condExp_of_aestronglyMeasurable' ((natFiltration hBmeas).le a) (hMaAe.pow 2) hMa2
  have e3 : (μ[Aa | natFiltration hBmeas a]) =ᵐ[μ] Aa :=
    condExp_of_aestronglyMeasurable' ((natFiltration hBmeas).le a) hAaAe hAai
  have eC : (μ[fun ω ↦ Mb ω * Ma ω - Ma ω ^ 2 | natFiltration hBmeas a])
      =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
    refine (condExp_sub hcross hMa2 _).trans ?_
    filter_upwards [e1, e2] with ω h1 h2
    show (μ[fun ω ↦ Mb ω * Ma ω | natFiltration hBmeas a]) ω
        - (μ[fun ω ↦ Ma ω ^ 2 | natFiltration hBmeas a]) ω = 0
    rw [h1, h2, sq]
    ring
  -- the bracket increment splits off, because `⟨M⟩_a` is adapted
  have eB : (μ[bracketRep (μ := μ) T hBmeas φ a b | natFiltration hBmeas a])
      =ᵐ[μ] fun ω ↦ (μ[Ab | natFiltration hBmeas a]) ω - Aa ω := by
    refine (condExp_congr_ae ?_).trans ((condExp_sub hAbi hAai _).trans ?_)
    · filter_upwards [bracketRep_add T hBmeas φ (show (0 : ℝ≥0) ≤ a from bot_le) hab hbT]
        with ω h
      show bracketRep (μ := μ) T hBmeas φ a b ω
          = bracketRep (μ := μ) T hBmeas φ 0 b ω - bracketRep (μ := μ) T hBmeas φ 0 a ω
      linarith
    · filter_upwards [e3] with ω h
      show (μ[Ab | natFiltration hBmeas a]) ω - (μ[Aa | natFiltration hBmeas a]) ω
          = (μ[Ab | natFiltration hBmeas a]) ω - Aa ω
      rw [h]
  -- `M_b² = (M_b − M_a)² + C + (C + M_a²)`, and `μ[C|𝓕_a] = 0`
  have eS : (μ[fun ω ↦ Mb ω ^ 2 | natFiltration hBmeas a])
      =ᵐ[μ] fun ω ↦ (μ[fun ω ↦ (Mb ω - Ma ω) ^ 2 | natFiltration hBmeas a]) ω + Ma ω ^ 2 := by
    rw [show (fun ω ↦ Mb ω ^ 2)
        = ((fun ω ↦ (Mb ω - Ma ω) ^ 2) + (fun ω ↦ Mb ω * Ma ω - Ma ω ^ 2))
            + ((fun ω ↦ Mb ω * Ma ω - Ma ω ^ 2) + (fun ω ↦ Ma ω ^ 2)) from
      funext fun ω ↦ by simp only [Pi.add_apply]; ring]
    refine (condExp_add (hdiff.add hCi) (hCi.add hMa2) _).trans ?_
    filter_upwards [condExp_add hdiff hCi (natFiltration hBmeas a),
      condExp_add hCi hMa2 (natFiltration hBmeas a), eC, e2] with ω h1 h2 h3 h4
    simp only [Pi.add_apply] at h1 h2 ⊢
    rw [h1, h2, h3, h4]
    ring
  refine (condExp_sub hMb2 hAbi _).trans ?_
  filter_upwards [eS, condExp_band_second_moment hB T hBmeas φ hab hbT, eB] with ω h1 h2 h3
  show (μ[fun ω ↦ Mb ω ^ 2 | natFiltration hBmeas a]) ω
      - (μ[Ab | natFiltration hBmeas a]) ω = Ma ω ^ 2 - Aa ω
  rw [h1, h2, h3]; ring

end BracketCompensator
end MathFin
