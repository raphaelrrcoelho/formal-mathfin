/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralLocality
public import MathFin.Foundations.PredictableDensityGeneral

/-! # The Itô integral against an Itô integral, and the chain rule

For a fixed predictable `φ ∈ L²(trim_T)` write `M := φ●B` for the Itô integral process
`M_t = (φ●B)_t`. This file integrates *against* `M`.

In the standard theory `M` is a continuous `L²` martingale with bracket `d⟨M⟩ = φ² ds ⊗ dμ`, so
the integrands square-integrable against it are `L²(⟨M⟩) = L²(φ²·trim_T)`. That is the
motivation for `bracketMeasure` below, and it is worth being exact about its status here: the
library has no quadratic-variation *object*, so `bracketMeasure` is *defined* as `φ²·trim_T`
and "bracket" is a name for it. What earns the name is `norm_sq_increment_eq_bracket`: the
unconditional second moment of an increment is the measure of its time band,

  `𝔼[(M_b − M_a)²] = ⟨M⟩((a,b] × Ω)`,

which is the defining property quadratic variation is for, at the level of expectations. The
conditional refinement (`𝔼[(M_b−M_a)² | 𝓕_a] = 𝔼[⟨M⟩_b−⟨M⟩_a | 𝓕_a]`) is not claimed *here* but
does ship, in `PointwiseBracket` (`condExp_band_second_moment`) and `BracketCompensator`
(`condExp_sq_sub_bracket`). What is claimed nowhere yet is a pathwise bracket; pathwise continuity of `M` lives in `ItoIntegralProcessContinuousModification`,
not here. The integral itself is

  `∫ψ dM := ∫ ψφ dB`,

obtained by composing the multiplication isometry `ψ ↦ ψφ` of `LpMulIsometry` with
`itoIntegralCLM_T`. Because both factors are isometries, so is the composite:

  `‖∫ψ dM‖_{L²(μ)} = ‖ψ‖_{L²(⟨M⟩)}`,

which is the Itô isometry against `M`. That identity is the reason the weighted space is the
right domain, and it is what would come out wrong if the integral were defined on the flat
`L²(trim_T)` instead.

## Why this is the stochastic integral and not a notation

Defining `∫ψ dM` by a formula proves nothing on its own. What earns the name is
`itoIntegralAgainst_elementary`: on an elementary integrand `Z·1_{(a,b]}` with `Z` bounded and
`𝓕_a`-measurable, the definition returns

  `Z·(M_b − M_a)`,

the Riemann–Stieltjes sum one would have written down by hand. So the formula is a
construction, and the elementary identity is what identifies it.

**Uniqueness against the sums.** The band identity is summed over a simple process's
rectangles in `itoIntegralAgainst_simpleProcess`, so `itoIntegralAgainst_unique_of_riemannStieltjes`
takes the hypothesis one wants — agreement with the *explicitly written* Riemann–Stieltjes sums
`∑ₚ V(p)·(M_{p.2} − M_{p.1})` — and concludes equality. Nothing in that hypothesis mentions the
integral being characterised. (`itoIntegralAgainst_unique`, agreement on the simple processes,
remains as the density statement it is built from.)

The proof of the elementary identity is short because the locality machinery already exists:
`1_{(a,b]}·φ` is `restrictAfterCLM a φ − restrictAfterCLM b φ`, and its integral is `M_b − M_a`
by `itoIntegralCLM_T_bandRestrict`; the `𝓕_a`-measurable factor `Z` passes through by
`itoIntegralCLM_T_smulAdapted`.

## Upstream

Degenne's package carries an axiomatic characterisation of the stochastic integral
(`IsRiemannStieltjesExtension`, `IsStochasticIntegral`), whose uniqueness clause is the same
idea in a wider frame (dominated convergence rather than `L²` density). It exists only on
`v4.33.0-rc1`, so `itoIntegralAgainst_unique` is proved here in the `L²` frame; instantiating
the upstream predicate is a follow-up for the next stable pin bump.

## Result

* `bracketMeasure` — `d⟨M⟩ = φ²·trim_T`, and its finiteness.
* `norm_sq_increment_eq_bracket` — **the bracket earns its name**:
  `𝔼[(M_b − M_a)²] = ⟨M⟩((a,b] × Ω)`.
* `itoIntegralCLM_T_bandRestrict` — the band integral: `∫ 𝟙_{(a,b]}·φ dB = M_b − M_a`.
* `itoIntegralAgainstCLM` — `∫· dM`, as a CLM on `L²(⟨M⟩)`.
* `itoIntegralAgainst_eq_itoIntegral` — **the chain rule**: `∫ψ dM = ∫ ψφ dB`.
* `norm_itoIntegralAgainstCLM` — the Itô isometry against `M`.
* `itoIntegralAgainst_elementary` — **the identification**, on a single band:
  `∫ Z·1_{(a,b]} dM = Z·(M_b − M_a)`.
* `itoIntegralAgainst_simpleProcess` — **the summed identity**: on a simple process,
  `∫V dM = ∑ₚ V(p)·(M_{p.2} − M_{p.1})`.
* `itoIntegralAgainst_unique_of_riemannStieltjes` — **uniqueness against those sums**; and
  `itoIntegralAgainst_unique`, the density statement it factors through.
* `bracketMeasure_mulLI` — `d⟨ψ●M⟩ = ψ² d⟨M⟩`: the construction is closed under itself, the
  brackets composing the way the integrands do.
-/

@[expose] public section

namespace MathFin
namespace ItoIntegralAgainstMartingale

open MeasureTheory ProbabilityTheory Filter ItoIntegralL2 ItoIntegralCLM LpMulIsometry
  PredictableDensityGeneral ItoIntegralProcessGeneral
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {hB : IsPreBrownianReal B μ}

/-! ### The bracket measure -/

/-- The measure `φ²·trim_T` on the predictable σ-algebra — the domain of integration against
`M = φ●B`. It is `d⟨M⟩` of the standard theory, and the name is earned at the level the tower
states things: `norm_sq_increment_eq_bracket` proves `𝔼[(M_b − M_a)²] = ⟨M⟩((a,b] × Ω)`, the
unconditional second-moment property of a bracket. What is *not* constructed here is a pathwise
quadratic variation, or the conditional form of that identity. Also proved: the isometry
`norm_itoIntegralAgainstCLM`, and `bracketMeasure_mulLI`, that it composes the way a bracket
should. -/
noncomputable def bracketMeasure (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    @Measure (ℝ≥0 × Ω)
      (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable :=
  sqWeight (trimMeasure_T (μ := μ) T hBmeas) (⇑φ)

omit [IsProbabilityMeasure μ] in
/-- `bracketMeasure` unfolded — the bridge to `LpMulIsometry`'s generic API. -/
theorem bracketMeasure_eq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    bracketMeasure (μ := μ) T hBmeas φ
      = sqWeight (trimMeasure_T (μ := μ) T hBmeas) (⇑φ) := rfl

omit [IsProbabilityMeasure μ] in
/-- The bracket measure is finite, with total mass `‖φ‖²` — the energy of the driver. -/
instance instIsFiniteMeasureBracketMeasure (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    IsFiniteMeasure (bracketMeasure (μ := μ) T hBmeas φ) :=
  isFiniteMeasure_sqWeight T hBmeas (Lp.memLp φ)

/-! ### The integral against `M` -/

/-- **The Itô integral against `M = φ●B`**, as a continuous linear map from the integrands
square-integrable against the bracket. It is `itoIntegralCLM_T` precomposed with
multiplication by the driver, so the chain rule holds by construction and the isometry is
inherited from the two factors. -/
noncomputable def itoIntegralAgainstCLM (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ) →L[ℝ] Lp ℝ 2 μ :=
  (itoIntegralCLM_T hB T hBmeas).comp
    (mulLI (trimMeasure_T (μ := μ) T hBmeas)
      (Lp.stronglyMeasurable φ).measurable).toContinuousLinearMap

/-- **The chain rule, in bundled form**: integrating `ψ` against `M` is integrating `ψφ`
against `B`. -/
theorem itoIntegralAgainstCLM_apply (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ)) :
    itoIntegralAgainstCLM hB T hBmeas φ ψ
      = itoIntegralCLM_T hB T hBmeas
          (mulLI (trimMeasure_T (μ := μ) T hBmeas)
            (Lp.stronglyMeasurable φ).measurable ψ) := rfl

/-- **The chain rule** in the form a caller uses it: if `χ` is any predictable `L²` integrand
a.e. equal to `φ·ψ`, then `∫ψ dM = ∫χ dB`. -/
theorem itoIntegralAgainst_eq_itoIntegral (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ))
    (χ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (hχ : ⇑χ =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
      fun z ↦ (φ : ℝ≥0 × Ω → ℝ) z * (ψ : ℝ≥0 × Ω → ℝ) z) :
    itoIntegralAgainstCLM hB T hBmeas φ ψ = itoIntegralCLM_T hB T hBmeas χ := by
  rw [itoIntegralAgainstCLM_apply]
  congr 1
  refine Lp.ext ?_
  exact (coeFn_mulLI _ (Lp.stronglyMeasurable φ).measurable ψ).trans hχ.symm

/-- **The Itô isometry against `M`**: `‖∫ψ dM‖_{L²(μ)} = ‖ψ‖_{L²(⟨M⟩)}`. Both factors of the
composite are isometries. -/
theorem norm_itoIntegralAgainstCLM (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ)) :
    ‖itoIntegralAgainstCLM hB T hBmeas φ ψ‖ = ‖ψ‖ := by
  rw [itoIntegralAgainstCLM_apply, itoIntegralCLM_T_norm]
  exact LinearIsometry.norm_map _ _

/-! ### The elementary identity that earns the name -/

/-- `1_{(a,b]}·φ`, as an element of the flat predictable `L²`: the difference of the two
restrictions the locality file already provides. -/
noncomputable def bandRestrict (T a b : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  restrictAfterCLM T a hBmeas φ - restrictAfterCLM T b hBmeas φ

omit [IsProbabilityMeasure μ] in
/-- `bandRestrict` is what its name says: `φ` cut down to the time band `(a, b]`. -/
theorem coeFn_bandRestrict (T a b : ℝ≥0) (hab : a ≤ b) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ⇑(bandRestrict (μ := μ) T a b hBmeas φ) =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
      fun z ↦ (Set.Ioc a b).indicator (fun _ ↦ (1 : ℝ)) z.1 * (φ : ℝ≥0 × Ω → ℝ) z := by
  simp only [bandRestrict]
  filter_upwards [Lp.coeFn_sub (restrictAfterCLM T a hBmeas φ) (restrictAfterCLM T b hBmeas φ),
    coeFn_restrictAfterCLM T a hBmeas φ, coeFn_restrictAfterCLM T b hBmeas φ] with z hsub ha hb
  rw [hsub, Pi.sub_apply, ha, hb]
  by_cases hza : a < z.1
  · by_cases hzb : b < z.1
    · rw [if_pos hza, if_pos hzb, sub_self,
        Set.indicator_of_notMem (fun hmem ↦ absurd hmem.2 (not_le.mpr hzb)), zero_mul]
    · rw [if_pos hza, if_neg hzb, sub_zero,
        Set.indicator_of_mem (by exact ⟨hza, not_lt.mp hzb⟩), one_mul]
  · have hzb : ¬ b < z.1 := fun h ↦ hza (lt_of_le_of_lt hab h)
    rw [if_neg hza, if_neg hzb, sub_zero,
      Set.indicator_of_notMem (fun hmem ↦ hza hmem.1), zero_mul]

omit [IsProbabilityMeasure μ] in
/-- `bandRestrict` vanishes on `[0, a]`, which is the support hypothesis the `𝓕_a`-linearity
of the Itô integral asks for. -/
theorem bandRestrict_eq_zero_of_le (T a b : ℝ≥0) (hab : a ≤ b)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), z.1 ≤ a →
      (bandRestrict (μ := μ) T a b hBmeas φ : ℝ≥0 × Ω → ℝ) z = 0 := by
  filter_upwards [coeFn_bandRestrict (μ := μ) T a b hab hBmeas φ] with z hz hza
  rw [hz, Set.indicator_of_notMem (fun hmem ↦ absurd hmem.1 (not_lt.mpr hza)), zero_mul]

/-- **The band integral**: restricting an integrand to `(a,b]` integrates to the increment,

  `∫₀ᵀ 𝟙_{(a,b]}·φ dB = M_b − M_a`,

by locality (`itoIntegralCLM_T_restrictAfterCLM`, applied to each endpoint). Wanted twice:
inside the elementary identification below, and for the second moment
`norm_sq_increment_eq_bracket`. -/
theorem itoIntegralCLM_T_bandRestrict (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) :
    itoIntegralCLM_T hB T hBmeas (bandRestrict (μ := μ) T a b hBmeas φ)
      = itoProcessCLM hB T b hBmeas φ - itoProcessCLM hB T a hBmeas φ := by
  simp only [bandRestrict]
  rw [map_sub,
    itoIntegralCLM_T_restrictAfterCLM (hB := hB) T a (hab.trans hbT) hBmeas φ,
    itoIntegralCLM_T_restrictAfterCLM (hB := hB) T b hbT hBmeas φ]
  abel

/-- **The characterisation.** On an elementary integrand `Z·1_{(a,b]}` with `Z` bounded and
`𝓕_a`-measurable, the integral against `M` is the increment `Z·(M_b − M_a)` — the
Riemann–Stieltjes sum. This is what makes `itoIntegralAgainstCLM` the stochastic integral
against `M` rather than a name for a formula. -/
theorem itoIntegralAgainst_elementary (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T)
    (Z : Ω → ℝ) (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C)
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ))
    (hψ : ⇑ψ =ᵐ[bracketMeasure (μ := μ) T hBmeas φ] elemIntegrand a b Z) :
    ⇑(itoIntegralAgainstCLM hB T hBmeas φ ψ) =ᵐ[μ]
      fun ω ↦ Z ω * (itoProcessCLM hB T b hBmeas φ ω - itoProcessCLM hB T a hBmeas φ ω) := by
  -- the scaled band integrand, as an `L²` class
  set W := smulAdapted T a hBmeas Z hZm C hZb (bandRestrict (μ := μ) T a b hBmeas φ) with hW
  -- `mulLI ψ` and `W` are the same integrand
  have hmul : itoIntegralAgainstCLM hB T hBmeas φ ψ = itoIntegralCLM_T hB T hBmeas W := by
    refine itoIntegralAgainst_eq_itoIntegral T hBmeas φ ψ W ?_
    -- move the a.e. hypothesis across the weight: it is only `bracketMeasure`-a.e.
    have hcross : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas),
        (φ : ℝ≥0 × Ω → ℝ) z ≠ 0 → (ψ : ℝ≥0 × Ω → ℝ) z = elemIntegrand a b Z z := by
      have := (ae_withDensity_iff (μ := trimMeasure_T (μ := μ) T hBmeas)
        (measurable_sqDensity (Lp.stronglyMeasurable φ).measurable)).1 hψ
      filter_upwards [this] with z hz hφz
      exact hz (sqDensity_ne_zero hφz)
    filter_upwards [hcross,
      coeFn_smulAdapted T a hBmeas Z hZm C hZb (bandRestrict (μ := μ) T a b hBmeas φ)
        (bandRestrict_eq_zero_of_le (μ := μ) T a b hab hBmeas φ),
      coeFn_bandRestrict (μ := μ) T a b hab hBmeas φ] with z hz hWz hbz
    simp only [hW, hWz, hbz]
    by_cases hφz : (φ : ℝ≥0 × Ω → ℝ) z = 0
    · rw [hφz, mul_zero, mul_zero, zero_mul]
    · simp only [hz hφz, elemIntegrand]
      ring
  rw [hmul]
  -- pull `Z` out, then read the band integral off `itoIntegralCLM_T_bandRestrict`
  have hband := itoIntegralCLM_T_bandRestrict (hB := hB) T hBmeas φ hab hbT
  filter_upwards [itoIntegralCLM_T_smulAdapted (hB := hB) T a hBmeas Z hZm C hZb
      (bandRestrict (μ := μ) T a b hBmeas φ)
      (bandRestrict_eq_zero_of_le (μ := μ) T a b hab hBmeas φ),
    Lp.coeFn_sub (itoProcessCLM hB T b hBmeas φ) (itoProcessCLM hB T a hBmeas φ)] with ω h1 h2
  rw [hW, h1, hband, h2, Pi.sub_apply]

/-! ### A simple process is a finite sum of bands

The single-band identity is summed over a simple process here. A simple process *is* the finite
sum of its bands: `ItoIntegralL2.rectTerm` is the elementary integrand at the band `p`, by
definition, and the a.e. decomposition is `uncurry_ae_eq_sum_rectTerm_of_ae_fst_ne_zero`, which
holds for any measure charging the time origin nothing — the bracket measure among them. What is
added here is its `Lp` form. -/

omit mΩ in
/-- `Z·1_{(a,b]}` is a difference of two `afterFactor`s. This is how the band inherits
predictable measurability, `afterFactor` being predictable by `measurable_afterFactor`. -/
theorem elemIntegrand_eq_sub {a b : ℝ≥0} (hab : a ≤ b) (Z : Ω → ℝ) :
    elemIntegrand a b Z = afterFactor a Z - afterFactor b Z := by
  funext z
  show (Set.Ioc a b).indicator (fun _ ↦ (1 : ℝ)) z.1 * Z z.2
      = (if a < z.1 then Z z.2 else 0) - (if b < z.1 then Z z.2 else 0)
  by_cases h1 : a < z.1
  · by_cases h2 : b < z.1
    · rw [Set.indicator_of_notMem (fun hm ↦ absurd hm.2 (not_le.mpr h2)), zero_mul,
        if_pos h1, if_pos h2, sub_self]
    · rw [Set.indicator_of_mem (show z.1 ∈ Set.Ioc a b from ⟨h1, not_lt.mp h2⟩), one_mul,
        if_pos h1, if_neg h2, sub_zero]
  · have h2 : ¬ b < z.1 := fun h ↦ h1 (lt_of_le_of_lt hab h)
    rw [Set.indicator_of_notMem (fun hm ↦ h1 hm.1), zero_mul, if_neg h1, if_neg h2, sub_zero]

omit [IsProbabilityMeasure μ] in
/-- The band is predictable. -/
theorem measurable_elemIntegrand (hBmeas : ∀ t, Measurable (B t)) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : Ω → ℝ} (hZm : Measurable[ItoIntegralL2.natFiltration hBmeas a] Z) :
    Measurable[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable]
      (elemIntegrand a b Z) := by
  rw [elemIntegrand_eq_sub hab Z]
  exact (measurable_afterFactor hBmeas hZm).sub
    (measurable_afterFactor hBmeas
      (hZm.mono ((ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).mono hab) le_rfl))

omit mΩ in
/-- The band inherits a bound on its coefficient: the indicator only ever switches it off. -/
theorem norm_elemIntegrand_le {a b : ℝ≥0} {Z : Ω → ℝ} {C : ℝ} (hZb : ∀ ω, ‖Z ω‖ ≤ C)
    (z : ℝ≥0 × Ω) : ‖elemIntegrand a b Z z‖ ≤ C := by
  simp only [elemIntegrand, Set.indicator_apply]
  split_ifs with h
  · rw [one_mul]; exact hZb z.2
  · rw [zero_mul, norm_zero]; exact le_trans (norm_nonneg (Z z.2)) (hZb z.2)

omit [IsProbabilityMeasure μ] in
/-- A band of a simple process is `L²` against the bracket: it is bounded, and the bracket
measure is finite. -/
theorem memLp_elemIntegrand_of_mem_support (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (V : TBoundedSP T hBmeas)
    {p : ℝ≥0 × ℝ≥0} (hp : p ∈ V.val.value.support) :
    MemLp (elemIntegrand p.1 p.2 (V.val.value p)) 2
      (bracketMeasure (μ := μ) T hBmeas φ) := by
  obtain ⟨C, hC⟩ := V.val.bounded_value
  exact MemLp.of_bound
    (measurable_elemIntegrand hBmeas (V.val.le_of_mem_support_value p hp)
      (V.val.measurable_value p)).stronglyMeasurable.aestronglyMeasurable C
    (Eventually.of_forall fun z ↦ norm_elemIntegrand_le (fun ω ↦ hC p hp ω) z)

open scoped Classical in
/-- **The band of `V` at the rectangle `p`, as an element of `L²(⟨M⟩)`.** Total by
construction: off the support of `V.value` the hypotheses that make the band `L²` are
unavailable, and the band is `0` there anyway. -/
noncomputable def bandLp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (V : TBoundedSP T hBmeas)
    (p : ℝ≥0 × ℝ≥0) : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ) :=
  if h : MemLp (elemIntegrand p.1 p.2 (V.val.value p)) 2
      (bracketMeasure (μ := μ) T hBmeas φ) then h.toLp _ else 0

omit [IsProbabilityMeasure μ] in
open scoped Classical in
/-- On the support, `bandLp` is the band. -/
theorem coeFn_bandLp (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (V : TBoundedSP T hBmeas)
    {p : ℝ≥0 × ℝ≥0} (hp : p ∈ V.val.value.support) :
    ⇑(bandLp T hBmeas φ V p) =ᵐ[bracketMeasure (μ := μ) T hBmeas φ]
      elemIntegrand p.1 p.2 (V.val.value p) := by
  rw [bandLp, dif_pos (memLp_elemIntegrand_of_mem_support T hBmeas φ V hp)]
  exact MemLp.coeFn_toLp _

/-- **A simple process is the sum of its bands**, in `L²(⟨M⟩)`. This is what lets the
single-band identity above be summed into a statement about a whole simple process — and hence
what connects it to the dense family of `PredictableDensityGeneral`. -/
theorem simpleAssemblyOfMeasure_eq_sum_bands (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (V : TBoundedSP T hBmeas) :
    simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ) V
      = ∑ p ∈ V.val.value.support, bandLp T hBmeas φ V p := by
  refine Lp.ext ?_
  have hbot : ∀ᵐ z ∂(bracketMeasure (μ := μ) T hBmeas φ), z.1 ≠ 0 :=
    (withDensity_absolutelyContinuous (trimMeasure_T (μ := μ) T hBmeas)
      (fun z ↦ ‖(φ : ℝ≥0 × Ω → ℝ) z‖ₑ ^ 2)).ae_le (ae_fst_ne_zero T hBmeas)
  have hsum : ⇑(∑ p ∈ V.val.value.support, bandLp T hBmeas φ V p)
      =ᵐ[bracketMeasure (μ := μ) T hBmeas φ]
      fun z ↦ ∑ p ∈ V.val.value.support, elemIntegrand p.1 p.2 (V.val.value p) z := by
    refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
    have hall : ∀ᵐ z ∂(bracketMeasure (μ := μ) T hBmeas φ),
        ∀ q : {x // x ∈ V.val.value.support},
          (bandLp T hBmeas φ V q.1 : ℝ≥0 × Ω → ℝ) z
            = elemIntegrand (q.1).1 (q.1).2 (V.val.value q.1) z :=
      ae_all_iff.mpr fun q ↦ coeFn_bandLp T hBmeas φ V q.2
    filter_upwards [hall] with z hz
    exact Finset.sum_congr rfl fun p hp ↦ hz ⟨p, hp⟩
  refine ((coeFn_simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ) V).trans
    (uncurry_ae_eq_sum_rectTerm_of_ae_fst_ne_zero hbot hBmeas V.val)).trans hsum.symm

/-! ### The summed identity, and uniqueness -/

/-- **The Riemann–Stieltjes identity, for a whole simple process.** Integrating `V` against `M`
returns the sum of its band increments,

  `∫V dM = ∑ₚ V(p)·(M_{p.2} − M_{p.1})`,

the sum one would write down by hand. This is `itoIntegralAgainst_elementary` summed over
`simpleAssemblyOfMeasure_eq_sum_bands`. -/
theorem itoIntegralAgainst_simpleProcess (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (V : TBoundedSP T hBmeas) :
    ⇑(itoIntegralAgainstCLM hB T hBmeas φ
        (simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ) V))
      =ᵐ[μ] fun ω ↦ ∑ p ∈ V.val.value.support, V.val.value p ω
          * ((itoProcessCLM hB T p.2 hBmeas φ : Ω → ℝ) ω
              - (itoProcessCLM hB T p.1 hBmeas φ : Ω → ℝ) ω) := by
  obtain ⟨C, hC⟩ := V.val.bounded_value
  rw [simpleAssemblyOfMeasure_eq_sum_bands, map_sum]
  have hterm : ∀ q : {x // x ∈ V.val.value.support},
      ∀ᵐ ω ∂μ, (itoIntegralAgainstCLM hB T hBmeas φ (bandLp T hBmeas φ V q.1) : Ω → ℝ) ω
        = V.val.value q.1 ω * ((itoProcessCLM hB T (q.1).2 hBmeas φ : Ω → ℝ) ω
            - (itoProcessCLM hB T (q.1).1 hBmeas φ : Ω → ℝ) ω) :=
    fun q ↦ itoIntegralAgainst_elementary (hB := hB) T hBmeas φ
      (V.val.le_of_mem_support_value q.1 q.2) (V.property q.1 q.2) (V.val.value q.1)
      (V.val.measurable_value q.1) C (fun ω ↦ by simpa [Real.norm_eq_abs] using hC q.1 q.2 ω)
      (bandLp T hBmeas φ V q.1) (coeFn_bandLp T hBmeas φ V q.2)
  refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
  filter_upwards [ae_all_iff.mpr hterm] with ω hω
  exact Finset.sum_congr rfl fun p hp ↦ hω ⟨p, hp⟩

/-- **Uniqueness.** A continuous linear map out of `L²(⟨M⟩)` that agrees with
`itoIntegralAgainstCLM` on the simple processes is `itoIntegralAgainstCLM`. With
`itoIntegralAgainst_elementary` identifying those values as the Riemann–Stieltjes sums, this
says the integral against `M` is the unique continuous linear extension of them. -/
theorem itoIntegralAgainst_unique (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (I : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ) →L[ℝ] Lp ℝ 2 μ)
    (hI : ∀ V : TBoundedSP T hBmeas,
      I (simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ) V)
        = itoIntegralAgainstCLM hB T hBmeas φ
            (simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ) V)) :
    I = itoIntegralAgainstCLM hB T hBmeas φ := by
  -- instance search does not unfold `bracketMeasure`, so hand it the unfolded form
  haveI : IsFiniteMeasure (sqWeight (trimMeasure_T (μ := μ) T hBmeas) (⇑φ)) :=
    instIsFiniteMeasureBracketMeasure (μ := μ) T hBmeas φ
  refine ContinuousLinearMap.ext fun ψ ↦ ?_
  exact congrFun (DenseRange.equalizer
    (simpleAssembly_sqWeight_denseRange T hBmeas (Lp.stronglyMeasurable φ).measurable)
    I.continuous (itoIntegralAgainstCLM hB T hBmeas φ).continuous (funext hI)) ψ

/-- **Uniqueness, against the written-out sums.** A continuous linear map out of `L²(⟨M⟩)` whose
value on every simple process is that process's Riemann–Stieltjes sum against `M` is
`itoIntegralAgainstCLM`. The hypothesis names no stochastic integral: it is the finite sum of
increments, which is what "the integral extends the elementary one" means. -/
theorem itoIntegralAgainst_unique_of_riemannStieltjes (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (I : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ) →L[ℝ] Lp ℝ 2 μ)
    (hI : ∀ V : TBoundedSP T hBmeas,
      ⇑(I (simpleAssemblyOfMeasure T hBmeas (bracketMeasure (μ := μ) T hBmeas φ) V))
        =ᵐ[μ] fun ω ↦ ∑ p ∈ V.val.value.support, V.val.value p ω
            * ((itoProcessCLM hB T p.2 hBmeas φ : Ω → ℝ) ω
                - (itoProcessCLM hB T p.1 hBmeas φ : Ω → ℝ) ω)) :
    I = itoIntegralAgainstCLM hB T hBmeas φ :=
  itoIntegralAgainst_unique T hBmeas φ I fun V ↦
    Lp.ext ((hI V).trans (itoIntegralAgainst_simpleProcess T hBmeas φ V).symm)

/-! ### The construction is closed under itself -/

omit [IsProbabilityMeasure μ] in
/-- **`d⟨ψ●M⟩ = ψ² d⟨M⟩`.** The driver of `∫ψ dM` is `ψφ`, so its bracket measure is
`(ψφ)²·trim_T` — which is `ψ²` weighting `φ²·trim_T`, the bracket of `M`. So integrating against
an integral-against-an-integral is integrating against the product, and the tower closes on
itself rather than needing a new construction at each level.

Densities multiply (`LpMulIsometry.sqWeight_sqWeight`); the only care is that the driver is an
`Lp` class, so the weight has to be moved along an a.e. identity first. -/
theorem bracketMeasure_mulLI (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas))
    (ψ : Lp ℝ 2 (bracketMeasure (μ := μ) T hBmeas φ)) :
    bracketMeasure (μ := μ) T hBmeas
        (mulLI (trimMeasure_T (μ := μ) T hBmeas) (Lp.stronglyMeasurable φ).measurable ψ)
      = sqWeight (bracketMeasure (μ := μ) T hBmeas φ) (⇑ψ) :=
  -- a bare term, deliberately: both `rw [bracketMeasure]` and a `show` fail here. `rw` cannot
  -- unfold a `def`, and `show` produces a goal that is type-correct only at default transparency
  -- (`ψ`'s type names `bracketMeasure`, the rewritten form names `sqWeight`), which then breaks
  -- `rw`'s motive. Term-mode unification handles the defeq and never builds a motive.
  (sqWeight_congr_ae (coeFn_mulLI (trimMeasure_T (μ := μ) T hBmeas)
      (Lp.stronglyMeasurable φ).measurable ψ)).trans
    (sqWeight_sqWeight (ν := trimMeasure_T (μ := μ) T hBmeas)
      (Lp.stronglyMeasurable φ).measurable (Lp.stronglyMeasurable ψ).measurable).symm

/-! ### The second moment: the bracket earns its name -/

omit [IsProbabilityMeasure μ] in
/-- **Squared `L²` norms are lower integrals**: `‖W‖² = (∫⁻ ‖W‖ₑ² ∂ν).toReal`. This is the
bridge by which a second moment meets a measure of a set — consumed by
`norm_sq_increment_eq_bracket`, where both sides are read as integrals over a time band. -/
private theorem lpNorm_sq_eq_lintegral_enorm_sq {α : Type*} {mα : MeasurableSpace α}
    {ν : Measure α} (W : Lp ℝ 2 ν) :
    ‖W‖ ^ 2 = (∫⁻ x, ‖(W : α → ℝ) x‖ₑ ^ 2 ∂ν).toReal := by
  have hrpow : eLpNorm (W : α → ℝ) 2 ν
      = (∫⁻ x, ‖(W : α → ℝ) x‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂ν) ^ (1 / ((2 : ℝ≥0∞).toReal)) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
  have hIeq : (∫⁻ x, ‖(W : α → ℝ) x‖ₑ ^ ((2 : ℝ≥0∞).toReal) ∂ν)
      = (∫⁻ x, ‖(W : α → ℝ) x‖ₑ ^ 2 ∂ν) :=
    lintegral_congr fun x ↦ by
      rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [Lp.norm_def, hrpow, hIeq,
    show ((1 : ℝ) / ((2 : ℝ≥0∞).toReal)) = 1 / 2 from by norm_num,
    ← ENNReal.toReal_rpow, pow_two,
    ← Real.sqrt_eq_rpow, Real.mul_self_sqrt ENNReal.toReal_nonneg]

/-- **The bracket earns its name.** The unconditional second moment of an increment of
`M = φ●B` is the bracket measure of the time band,

  `𝔼[(M_b − M_a)²] = ⟨M⟩((a,b] × Ω) = ∫_{(a,b] × Ω} φ² d(s ⊗ μ)`.

With the isometry this is the defining property quadratic variation is *for* — stated here at
the level of expectations, the form the tower supports. The conditional refinement
(`𝔼[(M_b − M_a)² | 𝓕_a] = 𝔼[⟨M⟩_b − ⟨M⟩_a | 𝓕_a]`) remains unclaimed: it needs a from-scratch
construction of the integral against `M`, not the composition with `∫·dB` used here.

The proof is one band: the increment is the integral of `bandRestrict`
(`itoIntegralCLM_T_bandRestrict`), the isometry turns its norm into an integral, and the band
representative (`coeFn_bandRestrict`) reads that integral off `(a,b] × Ω` — which is exactly
how `bracketMeasure` weights the set (`withDensity_apply`). -/
theorem norm_sq_increment_eq_bracket (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) :
    ‖itoProcessCLM hB T b hBmeas φ - itoProcessCLM hB T a hBmeas φ‖ ^ 2
      = ((bracketMeasure (μ := μ) T hBmeas φ)
          (Set.Ioc a b ×ˢ (Set.univ : Set Ω))).toReal := by
  have hset : MeasurableSet[(ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable]
      (Set.Ioc a b ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod a b MeasurableSet.univ
  rw [← itoIntegralCLM_T_bandRestrict (hB := hB) T hBmeas φ hab hbT, itoIntegralCLM_T_norm,
    lpNorm_sq_eq_lintegral_enorm_sq]
  refine congrArg ENNReal.toReal ?_
  calc ∫⁻ z, ‖(bandRestrict (μ := μ) T a b hBmeas φ : ℝ≥0 × Ω → ℝ) z‖ₑ ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas)
      = ∫⁻ z, (Set.Ioc a b ×ˢ (Set.univ : Set Ω)).indicator
            (fun z' ↦ ‖(φ : ℝ≥0 × Ω → ℝ) z'‖ₑ ^ 2) z
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
        refine lintegral_congr_ae ?_
        filter_upwards [coeFn_bandRestrict (μ := μ) T a b hab hBmeas φ] with z hz
        by_cases hmem : z.1 ∈ Set.Ioc a b
        · rw [hz, Set.indicator_of_mem hmem, one_mul,
            Set.indicator_of_mem (show z ∈ Set.Ioc a b ×ˢ (Set.univ : Set Ω) from
              ⟨hmem, Set.mem_univ _⟩)]
        · rw [hz, Set.indicator_of_notMem hmem, zero_mul, enorm_zero, zero_pow two_ne_zero,
            Set.indicator_of_notMem (fun hprod ↦ hmem hprod.1)]
    _ = ∫⁻ z in Set.Ioc a b ×ˢ (Set.univ : Set Ω), ‖(φ : ℝ≥0 × Ω → ℝ) z‖ₑ ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := lintegral_indicator hset _
    _ = (bracketMeasure (μ := μ) T hBmeas φ)
          (Set.Ioc a b ×ˢ (Set.univ : Set Ω)) := by
        rw [bracketMeasure_eq]
        simp only [sqWeight, withDensity_apply _ hset]

end ItoIntegralAgainstMartingale
end MathFin
