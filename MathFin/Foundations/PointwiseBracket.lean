/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralAgainstMartingale
public import MathFin.Foundations.GaussianMoments

/-! # The pointwise bracket and the conditional second moment

`bracketMeasure` (`ItoIntegralAgainstMartingale`) weights time-and-sample by `φ²`, which
integrates `ω` out: it can record *unconditional* second moments only. The bracket of the
standard theory is a *process*, `⟨M⟩_t(ω) = ∫₀ᵗ φ_s(ω)² ds`, and this file builds exactly that
much of it — enough for the conditional identity the measure-level object cannot state:

  `μ[(M_b − M_a)² | 𝓕_a] = μ[fun ω ↦ ∫ u in a..b, (⇑φ(u,ω))² du | 𝓕_a]`,

for `M = φ●B` on `[0,T]` and `a ≤ b ≤ T`. This is the defining property quadratic variation
is *for*, now conditionally — what `norm_sq_increment_eq_bracket` delivered unconditionally.

## Route: the conditional identity **is** the Itô isometry, localised

An identity between conditional expectations of two integrable variables is an identity of their
`𝓕_a`-set integrals, and on such a set the Itô integral already localises. For `F ∈ 𝓕_a` the
indicator `𝟙_F` is a bounded `𝓕_a`-measurable factor, so `itoIntegralCLM_T_smulAdapted` folds
`𝟙_F·(M_b − M_a)` back into a *single* Itô integral, that of `𝟙_F·𝟙_{(a,b]}·φ`. The isometry then
reads its second moment straight off the integrand — squaring the indicator costs nothing —

  `∫_F (M_b − M_a)² dμ = ‖𝟙_F·𝟙_{(a,b]}·φ‖²_{L²(trim_T)} = ∫_{(a,b]×F} φ² d trim_T`,

while Tonelli through the trim (`integral_trim`, then `integral_prod`) turns that same rectangle
integral into `∫_F (∫_a^b φ(u,ω)² du) dμ`. The two set-integrals agree for every `F ∈ 𝓕_a`, which
is what `ae_eq_condExp_of_forall_setIntegral_eq` consumes.

So there is no density argument, no polarisation of the quadratic form and no ε-extension: the
localisation lemma the library already had for the *first* moment carries the second one. The two
computations meet at `∫_{(a,b]×F} φ² d trim_T` (`setIntegral_sq_increment`,
`setIntegral_bracketRep`), which is also what keeps each a.e. argument on its native side —
representatives are compared under `trim_T`, and ω-sections are taken only of an explicitly
written integrand (`bandSq`), never of an `Lp` class.

## The conditional Brownian kernels, and the elementary integrand

Beside the general identity the file states the classical facts it is the abstraction of:

* **Kernels** — functions of a Brownian increment condition on the past as constants:
  `μ[B_v − B_u | 𝓕_u] =ᵐ 0`, `μ[(B_v−B_u)² | 𝓕_u] =ᵐ v−u`; tower + pull-out upgrade these to
  `𝓕_a`-adapted coefficients (`condExp_adapted_mul_increment_zero`,
  `condExp_adapted_mul_increment_sq`). These reach *further* than the general theorem in one
  direction: they ask only that the coefficient be integrable against the increment, where routing
  it through the general theorem means exhibiting `Z·1_{(c,d]}` as an `L²(trim_T)` class, and this
  file's constructor for that (`bandGen`) wants `Z` bounded (`condExp_increment_sq_of_adapted`).
* **Generators** — a single band `Z·1_{(c,d]}` as a predictable `L²` class (`bandGen`). Its
  support at both ends (`bandGen_support`, `bandGen_support_after`) is exactly what the locality
  file's time-locality consumes, so the integral *process* is pinned down: `0` up to `c`
  (`itoProcessCLM_bandGen_eq_zero`) and the explicit Riemann–Stieltjes term `Z·(B_d − B_c)` from
  `d` on (`itoProcessCLM_bandGen_eq_increment`, `eval_bandGen`). Composed with the kernels this
  gives `condExp_bandGen_second_moment`, which carries the general identity's own left-hand side
  on this integrand and the classical `(d−c)·μ[Z²|𝓕_a]` on the right — the witness that the
  abstract statement says the classical thing here. `bracketRep_bandGen` closes the loop by
  evaluating this integrand's pathwise bracket as `Z²·(d−c)`, so the two right-hand sides are the
  same object and not merely the same by inspection.

## Honest scope

The bracket process is delivered through its increments' conditional expectations. What *this file*
names is `bracketRep`, the ω-wise integral of the squared representative, with its nonnegativity,
band additivity (`bracketRep_add`) and the monotonicity that follows (`bracketRep_mono`) — not a
packaged adapted process. The packaging is done downstream: `BracketCompensator.bracketProcess`
is `⟨M⟩_{t∧T}` as a genuine adapted process (`bracketProcess_adapted`, axiom-audited). What is
still constructed nowhere is a *pathwise* quadratic variation — and it cannot currently be
imported either, since BM's `predQuadVariation` routes through the `sorry`-backed
`IsLocalSubmartingale.doob_meyer`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal
open ItoIntegralL2 ItoIntegralCLM ItoIsometryAdapted
open ItoIntegralAgainstMartingale LpMulIsometry ItoIntegralBrownian
open ItoIntegralProcessGeneral

namespace PointwiseBracket

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- Trims of the natural Brownian filtration are σ-finite: `μ` is a probability measure,
so its restriction to any sub-σ-algebra is finite, hence σ-finite. Side-condition shim for
the tower property of the conditional expectation (`condExp_condExp_of_le`). -/
private instance instSigmaFiniteTrimNatFiltration {hBmeas : ∀ t, Measurable (B t)}
    {u : ℝ≥0} : SigmaFinite (μ.trim ((natFiltration hBmeas).le u)) :=
  haveI : IsFiniteMeasure (μ.trim ((natFiltration hBmeas).le u)) :=
    MeasureTheory.isFiniteMeasure_trim _
  inferInstance

/-- For `s ≤ t : ℝ≥0`, the truncated increment variance `max (t-s) (s-t)` is the
`ℝ≥0`-nndistance of the coerced times. -/
private lemma maxSub_eq_nndist {s t : ℝ≥0} (hst : s ≤ t) :
    (max (t - s) (s - t) : ℝ≥0) = nndist (t : ℝ) (s : ℝ) := by
  apply NNReal.coe_injective
  have hle : ((s : ℝ) ≤ (t : ℝ)) := by exact_mod_cast hst
  rw [coe_nndist, Real.dist_eq, tsub_eq_zero_of_le hst, max_eq_left zero_le,
    NNReal.coe_sub hst, abs_of_nonneg (sub_nonneg.mpr hle)]

/-- For `s ≤ t : ℝ≥0`, the truncated variance coerces to the real elapsed time. -/
private lemma maxSubCoe {s t : ℝ≥0} (hst : s ≤ t) :
    ((max (t - s) (s - t) : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) := by
  have hst_zero : s - t = (0 : ℝ≥0) := tsub_eq_zero_of_le hst
  rw [hst_zero, max_eq_left zero_le]
  exact NNReal.coe_sub hst

/-! ### The conditional Brownian kernels -/

/-- Functions of a Brownian increment condition on the past as constants: if
`∫ φ(B_v − B_u) dμ = c` then `μ[φ(B_v − B_u) | 𝓕_u] =ᵐ c`. Independence of the increment
from `𝓕_u` (`IsFilteredPreBrownian.indep`) via `condExp_indep_eq`. -/
private theorem condExp_func_increment (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {u v : ℝ≥0} (huv : u ≤ v)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {c : ℝ}
    (h_int : ∫ ω, φ (B v ω - B u ω) ∂μ = c) :
    (μ[fun ω ↦ φ (B v ω - B u ω) | natFiltration hBmeas u]) =ᵐ[μ] fun _ ↦ c := by
  have hd : Measurable (fun ω ↦ B v ω - B u ω) := (hBmeas v).sub (hBmeas u)
  have hcomp : Measurable[
      MeasurableSpace.comap (fun ω ↦ B v ω - B u ω) (borel ℝ)]
      (fun ω ↦ φ (B v ω - B u ω)) :=
    hφ.comp (Measurable.of_comap_le le_rfl)
  obtain ⟨hFB⟩ : Nonempty (IsFilteredPreBrownian B (natFiltration hBmeas) μ) :=
    ⟨hB.isFilteredPreBrownian hBmeas⟩
  have hindep := condExp_indep_eq hd.comap_le ((natFiltration hBmeas).le u)
    hcomp.stronglyMeasurable (hFB.indep u v huv)
  rwa [h_int] at hindep

omit [IsProbabilityMeasure μ] in
/-- **Kernel 1**: the increment has zero conditional mean — `μ[B_v − B_u | 𝓕_u] =ᵐ 0`. -/
theorem condExp_increment_eq_zero (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {u v : ℝ≥0} (huv : u ≤ v) :
    (μ[fun ω ↦ B v ω - B u ω | natFiltration hBmeas u]) =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hL : HasLaw (B v - B u)
      (gaussianReal 0 (max (v - u) (u - v))) μ := by
    rw [maxSub_eq_nndist huv]; exact hB.hasLaw_sub v u
  have hint : ∫ ω, (B v ω - B u ω) ∂μ = 0 := by
    have h_eq : (fun ω ↦ B v ω - B u ω) = (B v - B u : Ω → ℝ) := rfl
    rw [h_eq, hL.integral_eq, integral_id_gaussianReal]
  exact condExp_func_increment hB hBmeas huv measurable_id hint

omit [IsProbabilityMeasure μ] in
/-- **Kernel 2**: the squared increment conditions on the elapsed time —
`μ[(B_v − B_u)² | 𝓕_u] =ᵐ v − u`. -/
theorem condExp_increment_sq (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {u v : ℝ≥0} (huv : u ≤ v) :
    (μ[fun ω ↦ (B v ω - B u ω) ^ 2 | natFiltration hBmeas u])
      =ᵐ[μ] fun _ ↦ (v : ℝ) - u := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hL : HasLaw (B v - B u)
      (gaussianReal 0 (max (v - u) (u - v))) μ := by
    rw [maxSub_eq_nndist huv]; exact hB.hasLaw_sub v u
  have hint : ∫ ω, (B v ω - B u ω) ^ 2 ∂μ = (v : ℝ) - u := by
    have h_change : ∫ ω, (B v ω - B u ω) ^ 2 ∂μ
        = ∫ x, x ^ 2 ∂(gaussianReal 0 (max (v - u) (u - v))) := by
      simpa [Function.comp] using hL.integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
    rw [h_change, integral_sq_gaussianReal]
    exact maxSubCoe huv
  exact condExp_func_increment hB hBmeas huv (measurable_id.pow_const 2) hint

omit [IsProbabilityMeasure μ] in
/-- A Brownian increment lies in `L²(μ)`. -/
private theorem memLp_increment (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {u v : ℝ≥0} (huv : u ≤ v) :
    MemLp (fun ω ↦ B v ω - B u ω) 2 μ := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hL : HasLaw (B v - B u)
      (gaussianReal 0 (max (v - u) (u - v))) μ := by
    rw [maxSub_eq_nndist huv]; exact hB.hasLaw_sub v u
  have hd : Measurable (fun ω ↦ B v ω - B u ω) := (hBmeas v).sub (hBmeas u)
  rw [show (fun ω ↦ B v ω - B u ω) = (B v - B u : Ω → ℝ) from rfl]
  exact ((hL.map_eq ▸ memLp_id_gaussianReal 2 :
    MemLp (id : ℝ → ℝ) 2 (Measure.map (B v - B u) μ))).comp_of_map hd.aemeasurable

omit [IsProbabilityMeasure μ] in
/-- **Kernel 3 (adapted diagonal)**: an `𝓕_c`-measurable coefficient times a squared
increment conditions on the elapsed time —
`μ[χ·(B_d−B_c)² | 𝓕_a] =ᵐ (d−c) · μ[χ | 𝓕_a]` for `a ≤ c ≤ d`. Tower through `𝓕_c`,
pull-out, Kernel 2; the product-integrability hypothesis is discharged by independence at
the call sites (`Indep.integrable_mul`). -/
theorem condExp_adapted_mul_increment_sq (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (_hprob : IsProbabilityMeasure μ)
    {a c d : ℝ≥0} (hac : a ≤ c) (hcd : c ≤ d)
    {χ : Ω → ℝ} (hχm : StronglyMeasurable[natFiltration hBmeas c] χ)
    (hχi : Integrable χ μ)
    (hint : Integrable (fun ω ↦ χ ω * (B d ω - B c ω) ^ 2) μ) :
    (μ[fun ω ↦ χ ω * (B d ω - B c ω) ^ 2 | natFiltration hBmeas a])
      =ᵐ[μ] fun ω ↦ ((d : ℝ) - c) * (μ[χ | natFiltration hBmeas a]) ω := by
  have hsq_int : Integrable (fun ω ↦ (B d ω - B c ω) ^ 2) μ :=
    (memLp_increment hB hBmeas hcd).integrable_sq
  have hinner : (μ[fun ω ↦ χ ω * (B d ω - B c ω) ^ 2 | natFiltration hBmeas c])
      =ᵐ[μ] fun ω ↦ χ ω * ((d : ℝ) - c) :=
    (condExp_mul_of_stronglyMeasurable_left hχm hint hsq_int).trans
      (by filter_upwards [condExp_increment_sq hB hBmeas hcd] with ω hω
          exact congrArg (χ ω * ·) hω)
  have hint' : Integrable (fun ω ↦ χ ω * ((d : ℝ) - c)) μ :=
    integrable_condExp.congr hinner
  calc (μ[fun ω ↦ χ ω * (B d ω - B c ω) ^ 2 | natFiltration hBmeas a])
      =ᵐ[μ] (μ[μ[fun ω ↦ χ ω * (B d ω - B c ω) ^ 2 | natFiltration hBmeas c]
          | natFiltration hBmeas a]) :=
        (condExp_condExp_of_le ((natFiltration hBmeas).mono hac)
          ((natFiltration hBmeas).le c)).symm
    _ =ᵐ[μ] (μ[(fun ω ↦ χ ω * ((d : ℝ) - c)) | natFiltration hBmeas a]) :=
        condExp_congr_ae hinner
    _ =ᵐ[μ] fun ω ↦ ((d : ℝ) - c) * (μ[χ | natFiltration hBmeas a]) ω :=
        (condExp_mul_of_aestronglyMeasurable_right
          stronglyMeasurable_const.aestronglyMeasurable hint' hχi).trans
          (Filter.Eventually.of_forall fun ω ↦ mul_comm _ _)

omit [IsProbabilityMeasure μ] in
/-- **Kernel 4 (adapted cross term)**: an `𝓕_u`-measurable coefficient times an increment
after `u` has zero conditional expectation given the further past —
`μ[X·(B_v−B_u) | 𝓕_a] =ᵐ 0` for `a ≤ u ≤ v`. Tower through `𝓕_u`, pull-out, Kernel 1. -/
theorem condExp_adapted_mul_increment_zero (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (_hprob : IsProbabilityMeasure μ)
    {a u v : ℝ≥0} (hau : a ≤ u) (huv : u ≤ v)
    {X : Ω → ℝ} (hXm : StronglyMeasurable[natFiltration hBmeas u] X)
    (hint : Integrable (fun ω ↦ X ω * (B v ω - B u ω)) μ) :
    (μ[fun ω ↦ X ω * (B v ω - B u ω) | natFiltration hBmeas a]) =ᵐ[μ] fun _ ↦ 0 := by
  have hinner : (μ[fun ω ↦ X ω * (B v ω - B u ω) | natFiltration hBmeas u])
      =ᵐ[μ] fun _ ↦ (0 : ℝ) :=
    (condExp_mul_of_stronglyMeasurable_left hXm hint
      ((memLp_increment hB hBmeas huv).integrable one_le_two)).trans
      (by filter_upwards [condExp_increment_eq_zero hB hBmeas huv] with ω hω
          show (X * μ[fun ω ↦ B v ω - B u ω | natFiltration hBmeas u]) ω = 0
          rw [Pi.mul_apply, hω, mul_zero])
  have houter : (μ[μ[fun ω ↦ X ω * (B v ω - B u ω) | natFiltration hBmeas u]
      | natFiltration hBmeas a]) =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
    refine (condExp_congr_ae hinner).trans ?_
    exact Filter.EventuallyEq.of_eq condExp_zero
  calc (μ[fun ω ↦ X ω * (B v ω - B u ω) | natFiltration hBmeas a])
      =ᵐ[μ] (μ[μ[fun ω ↦ X ω * (B v ω - B u ω) | natFiltration hBmeas u]
          | natFiltration hBmeas a]) :=
        (condExp_condExp_of_le ((natFiltration hBmeas).mono hau)
          ((natFiltration hBmeas).le u)).symm
    _ =ᵐ[μ] fun _ ↦ (0 : ℝ) := houter


theorem coeFn_bandAssembly {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t))
    {c d : ℝ≥0} (hcd : c ≤ d) (hdT : d ≤ T)
    {Z : Ω → ℝ} (hZm : Measurable[natFiltration hBmeas c] Z) {C : ℝ}
    (hZb : ∀ ω, |Z ω| ≤ C) :
    ⇑(simpleAssembly_T (μ := μ) T hBmeas (stepSP hBmeas hcd hdT hZm hZb))
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas]
        fun p ↦ (Set.Ioc c d).indicator (fun _ ↦ (1 : ℝ)) p.1 * Z p.2 := by
  refine (MemLp.coeFn_toLp (memLp_uncurry_trim_T T hBmeas
    (stepSP hBmeas hcd hdT hZm hZb).val)).trans
    (Filter.Eventually.of_forall fun p ↦ ?_)
  obtain ⟨t, ω⟩ := p
  show ⇑(stepSP hBmeas hcd hdT hZm hZb).val t ω
      = (Set.Ioc c d).indicator (fun _ ↦ (1 : ℝ)) t * Z ω
  rw [SimpleProcess.apply_eq]
  have hb0 : (stepSP hBmeas hcd hdT hZm hZb).val.valueBot = fun _ ↦ (0 : ℝ) := rfl
  have hbot : ({⊥} : Set ℝ≥0).indicator
      (fun _ ↦ (stepSP hBmeas hcd hdT hZm hZb).val.valueBot ω) t = 0 := by
    rw [hb0]
    by_cases h : t = ⊥ <;> simp [h]
  rw [hbot, zero_add,
    show (stepSP hBmeas hcd hdT hZm hZb).val.value
        = Finsupp.single (c, d) Z from rfl,
    Finsupp.sum_single_index (by simp)]
  by_cases hm : t ∈ Set.Ioc c d
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, one_mul]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul]

/-- **The single-band generator** `Z·1_{(c,d]×Ω}`, as a predictable `L²(trim_T)` class:
the assembly of the single-step process. For `a ≤ c`, these span the post-`a`-supported
part of `L²` (`dense_postA_span`), their integrals evaluate to the explicit increments
(`eval_bandGen`), and their pairwise conditional second moments vanish against each other
except through the time-overlap (`condExp_pair_bands`). -/
noncomputable def bandGen (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {c d : ℝ≥0} (hcd : c ≤ d) (hdT : d ≤ T)
    {Z : Ω → ℝ} (hZm : Measurable[natFiltration hBmeas c] Z) (C : ℝ)
    (hZb : ∀ ω, |Z ω| ≤ C) :
    Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
  simpleAssembly_T (μ := μ) T hBmeas (stepSP hBmeas hcd hdT hZm hZb)

/-- Band generators vanish before their left endpoint. -/
theorem bandGen_support {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t))
    {c d : ℝ≥0} (hcd : c ≤ d) (hdT : d ≤ T)
    {Z : Ω → ℝ} (hZm : Measurable[natFiltration hBmeas c] Z) (C : ℝ)
    (hZb : ∀ ω, |Z ω| ≤ C) :
    ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ c →
      (bandGen (μ := μ) T hBmeas hcd hdT hZm C hZb : ℝ≥0 × Ω → ℝ) p = 0 := by
    filter_upwards [coeFn_bandAssembly (T := T) hBmeas hcd hdT hZm hZb] with p hcoe hpc
    show ⇑(simpleAssembly_T (μ := μ) T hBmeas (stepSP hBmeas hcd hdT hZm hZb)) p = 0
    rw [hcoe]
    show (Set.Ioc c d).indicator (fun _ ↦ (1 : ℝ)) p.1 * Z p.2 = 0
    rw [Set.indicator_of_notMem (fun hc ↦ absurd hc.1 (not_lt.mpr hpc)), zero_mul]

/-- Band generators vanish after their right endpoint — the companion of `bandGen_support`, and
what says the elementary integral has finished by `d`. -/
theorem bandGen_support_after {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t))
    {c d : ℝ≥0} (hcd : c ≤ d) (hdT : d ≤ T)
    {Z : Ω → ℝ} (hZm : Measurable[natFiltration hBmeas c] Z) (C : ℝ)
    (hZb : ∀ ω, |Z ω| ≤ C) :
    ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), d < p.1 →
      (bandGen (μ := μ) T hBmeas hcd hdT hZm C hZb : ℝ≥0 × Ω → ℝ) p = 0 := by
  filter_upwards [coeFn_bandAssembly (T := T) hBmeas hcd hdT hZm hZb] with p hcoe hpd
  show ⇑(simpleAssembly_T (μ := μ) T hBmeas (stepSP hBmeas hcd hdT hZm hZb)) p = 0
  rw [hcoe]
  show (Set.Ioc c d).indicator (fun _ ↦ (1 : ℝ)) p.1 * Z p.2 = 0
  rw [Set.indicator_of_notMem (fun hc ↦ absurd hc.2 (not_le.mpr hpd)), zero_mul]

/-- **The band generator's integral is the explicit increment**: integrating
`Z·1_{(c,d]} dB` over `[0,T]` returns `Z·(B_d − B_c)` — the Riemann–Stieltjes term. -/
theorem eval_bandGen (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {c d : ℝ≥0} (hcd : c ≤ d) (hdT : d ≤ T)
    {Z : Ω → ℝ} (hZm : Measurable[natFiltration hBmeas c] Z) (C : ℝ)
    (hZb : ∀ ω, |Z ω| ≤ C) :
    ⇑(itoIntegralCLM_T hB T hBmeas (bandGen (μ := μ) T hBmeas hcd hdT hZm C hZb))
      =ᵐ[μ] fun ω ↦ Z ω * (B d ω - B c ω) := by
  rw [bandGen, itoIntegralCLM_T_simpleAssembly_T hB T hBmeas
    (stepSP hBmeas hcd hdT hZm hZb)]
  refine (MemLp.coeFn_toLp (memLp_itoSimple hB hBmeas
    (stepSP hBmeas hcd hdT hZm hZb).val)).trans
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  rw [itoSimple_stepSP hBmeas hcd hdT hZm hZb]

/-! ### The bracket, read ω-wise -/

/-- **The bracket increment, pathwise**: `⟨M⟩_b(ω) − ⟨M⟩_a(ω) = ∫_a^b φ_u(ω)² du`, taken on the
`Lp` class's own (strongly predictable) representative. This is the object `bracketMeasure`
cannot be, because it integrates `ω` out; it is *not* claimed here to be adapted (see the
module's honest scope). -/
noncomputable def bracketRep (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (a b : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ u in Set.Ioc a b, ((φ : ℝ≥0 × Ω → ℝ) (u, ω)) ^ 2 ∂timeMeasure

/-- The squared representative cut to the rectangle `(a,b] × F`: the one explicitly written
integrand of this file, and the only function ω-sections are ever taken of. -/
private noncomputable def bandSq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (a b : ℝ≥0) (F : Set Ω) :
    ℝ≥0 × Ω → ℝ :=
  (Set.Ioc a b ×ˢ F).indicator fun z ↦ ((φ : ℝ≥0 × Ω → ℝ) z) ^ 2

omit [IsProbabilityMeasure μ] in
/-- A predictable `L²` class is `L²` for the *untrimmed* product measure: `eLpNorm` does not
see the trim on a strongly predictable function. -/
private theorem memLp_prod (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    MemLp (⇑φ) 2 ((timeMeasure_T T).prod μ) :=
  ⟨((Lp.stronglyMeasurable φ).mono
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod).aestronglyMeasurable, by
    rw [← eLpNorm_trim (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod
      (Lp.stronglyMeasurable φ)]
    exact (Lp.memLp φ).2⟩

omit [IsProbabilityMeasure μ] in
/-- The ω-section of `bandSq` at a sample point of `F`: the band indicator of the squared time
section. Every section statement below is this identity plus a case on `ω ∈ F`. -/
private theorem bandSq_section (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (a b : ℝ≥0) {F : Set Ω} {ω : Ω}
    (hω : ω ∈ F) (u : ℝ≥0) :
    bandSq (μ := μ) T hBmeas φ a b F (u, ω)
      = (Set.Ioc a b).indicator (fun u' ↦ ((φ : ℝ≥0 × Ω → ℝ) (u', ω)) ^ 2) u := by
  by_cases hu : u ∈ Set.Ioc a b
  · rw [bandSq, Set.indicator_of_mem (show (u, ω) ∈ Set.Ioc a b ×ˢ F from ⟨hu, hω⟩),
      Set.indicator_of_mem hu]
  · rw [bandSq, Set.indicator_of_notMem (fun h ↦ hu h.1), Set.indicator_of_notMem hu]

/-- The band `(a,b]` sits inside the horizon, so the time measure may be restricted to it
directly. The one place `b ≤ T` is used. -/
private theorem restrict_timeMeasure_T (T : ℝ≥0) {a b : ℝ≥0} (hbT : b ≤ T) :
    (timeMeasure_T T).restrict (Set.Ioc a b) = timeMeasure.restrict (Set.Ioc a b) := by
  rw [timeMeasure_T, Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioc,
    max_eq_left (show (0 : ℝ≥0) ≤ a from bot_le), min_eq_left hbT]

omit [IsProbabilityMeasure μ] in
/-- The ω-section integral of `bandSq`: the band integral on `F`, zero off it. Pointwise in `ω`,
so it serves both the set-integral identity and the integrability of `bracketRep`. -/
private theorem integral_section_bandSq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {a b : ℝ≥0} (hbT : b ≤ T)
    (F : Set Ω) (ω : Ω) :
    ∫ u, bandSq (μ := μ) T hBmeas φ a b F (u, ω) ∂(timeMeasure_T T)
      = F.indicator (fun ω' ↦ bracketRep (μ := μ) T hBmeas φ a b ω') ω := by
  by_cases hω : ω ∈ F
  · rw [Set.indicator_of_mem hω]
    simp only [bandSq_section T hBmeas φ a b hω]
    rw [integral_indicator measurableSet_Ioc, restrict_timeMeasure_T T hbT, bracketRep]
  · have hpt : ∀ u : ℝ≥0, bandSq (μ := μ) T hBmeas φ a b F (u, ω) = 0 := fun u ↦ by
      rw [bandSq, Set.indicator_of_notMem (fun h ↦ hω h.2)]
    simp only [hpt, integral_zero, Set.indicator_of_notMem hω]

omit [IsProbabilityMeasure μ] in
/-- `bandSq` is a product-integrable function: it is `φ²` cut down to a predictable rectangle. -/
private theorem integrable_bandSq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (a b : ℝ≥0) {F : Set Ω}
    (hF : MeasurableSet[natFiltration hBmeas a] F) :
    Integrable (bandSq (μ := μ) T hBmeas φ a b F) ((timeMeasure_T T).prod μ) :=
  (memLp_prod T hBmeas φ).integrable_sq.indicator
    ((natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod _
      (MeasureTheory.measurableSet_predictable_Ioc_prod a b hF))

/-- The band integral of `φ²` is `μ`-integrable: Fubini applied to `bandSq` over the whole
sample space. -/
theorem integrable_bracketRep (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {a b : ℝ≥0} (hbT : b ≤ T) :
    Integrable (bracketRep (μ := μ) T hBmeas φ a b) μ :=
  (integrable_bandSq T hBmeas φ a b
    (MeasurableSet.univ (α := Ω))).integral_prod_right.congr
    (Filter.Eventually.of_forall fun ω ↦ by
      show ∫ u, bandSq (μ := μ) T hBmeas φ a b Set.univ (u, ω) ∂(timeMeasure_T T)
          = bracketRep (μ := μ) T hBmeas φ a b ω
      rw [integral_section_bandSq T hBmeas φ hbT Set.univ ω,
        Set.indicator_of_mem (Set.mem_univ ω)])

omit [IsProbabilityMeasure μ] in
/-- The pathwise bracket increment is nonnegative — it is an integral of a square. -/
theorem bracketRep_nonneg (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) (a b : ℝ≥0) (ω : Ω) :
    0 ≤ bracketRep (μ := μ) T hBmeas φ a b ω :=
  integral_nonneg fun _ ↦ sq_nonneg _

/-- For a.e. `ω` the squared section is integrable on the band — the ω-side of the product
integrability of `bandSq`, and the one hypothesis splitting a band in two needs. -/
private theorem ae_integrableOn_section (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {a b : ℝ≥0} (hbT : b ≤ T) :
    ∀ᵐ ω ∂μ, IntegrableOn (fun u ↦ ((φ : ℝ≥0 × Ω → ℝ) (u, ω)) ^ 2) (Set.Ioc a b) timeMeasure := by
  filter_upwards [(integrable_bandSq (μ := μ) T hBmeas φ a b
    (MeasurableSet.univ (α := Ω))).swap.prod_right_ae] with ω hω
  show Integrable (fun u ↦ ((φ : ℝ≥0 × Ω → ℝ) (u, ω)) ^ 2)
    (timeMeasure.restrict (Set.Ioc a b))
  rw [← restrict_timeMeasure_T T hbT]
  exact (integrable_indicator_iff measurableSet_Ioc).mp
    (hω.congr (Filter.Eventually.of_forall
      (bandSq_section T hBmeas φ a b (Set.mem_univ ω))))

/-- **Band additivity**, a.e.: the pathwise bracket increments of `(a,b]` and `(b,c]` add to that
of `(a,c]`. This is what makes `t ↦ bracketRep 0 t` a process whose increments are the objects
the conditional identity below is about. -/
theorem bracketRep_add (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {a b c : ℝ≥0}
    (hab : a ≤ b) (hbc : b ≤ c) (hcT : c ≤ T) :
    ∀ᵐ ω ∂μ, bracketRep (μ := μ) T hBmeas φ a b ω + bracketRep (μ := μ) T hBmeas φ b c ω
      = bracketRep (μ := μ) T hBmeas φ a c ω := by
  filter_upwards [ae_integrableOn_section (a := a) (b := c) T hBmeas φ hcT] with ω hsec
  simp only [bracketRep]
  rw [← Set.Ioc_union_Ioc_eq_Ioc hab hbc]
  exact (setIntegral_union
    (Set.disjoint_left.mpr fun u hu1 hu2 ↦ absurd hu2.1 (not_lt.mpr hu1.2)) measurableSet_Ioc
    (hsec.mono_set (Set.Ioc_subset_Ioc_right hbc))
    (hsec.mono_set (Set.Ioc_subset_Ioc_left hab))).symm

/-- Monotone in the band, a.e.: the increments are nonnegative and additive. -/
theorem bracketRep_mono (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {a b c : ℝ≥0}
    (hab : a ≤ b) (hbc : b ≤ c) (hcT : c ≤ T) :
    ∀ᵐ ω ∂μ, bracketRep (μ := μ) T hBmeas φ a b ω ≤ bracketRep (μ := μ) T hBmeas φ a c ω := by
  filter_upwards [bracketRep_add T hBmeas φ hab hbc hcT] with ω hω
  rw [← hω]
  exact le_add_of_nonneg_right (bracketRep_nonneg T hBmeas φ b c ω)

/-! ### The two set-integrals, and their meeting point -/

/-- **Tonelli side.** The `𝓕_a`-set integral of the pathwise bracket increment is the rectangle
integral of `φ²` over `(a,b] × F` — Fubini for the product measure, then `integral_trim`, which
a strongly predictable integrand crosses for free. -/
theorem setIntegral_bracketRep (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {a b : ℝ≥0} (hbT : b ≤ T)
    {F : Set Ω} (hF : MeasurableSet[natFiltration hBmeas a] F) :
    ∫ ω in F, bracketRep (μ := μ) T hBmeas φ a b ω ∂μ
      = ∫ z in Set.Ioc a b ×ˢ F, ((φ : ℝ≥0 × Ω → ℝ) z) ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  have hRpred : MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      (Set.Ioc a b ×ˢ F) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod a b hF
  have hgsm : StronglyMeasurable[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      (bandSq (μ := μ) T hBmeas φ a b F) :=
    ((Lp.stronglyMeasurable φ).pow 2).indicator hRpred
  have hint := integrable_bandSq (μ := μ) T hBmeas φ a b hF
  calc ∫ ω in F, bracketRep (μ := μ) T hBmeas φ a b ω ∂μ
      = ∫ ω, F.indicator (fun ω' ↦ bracketRep (μ := μ) T hBmeas φ a b ω') ω ∂μ :=
        (integral_indicator ((natFiltration hBmeas).le a F hF)).symm
    _ = ∫ ω, ∫ u, bandSq (μ := μ) T hBmeas φ a b F (u, ω) ∂(timeMeasure_T T) ∂μ := by
        simp only [integral_section_bandSq T hBmeas φ hbT F]
    _ = ∫ z, bandSq (μ := μ) T hBmeas φ a b F z ∂((timeMeasure_T T).prod μ) := by
        rw [integral_prod _ hint]
        exact integral_integral_swap hint.swap
    _ = ∫ z, bandSq (μ := μ) T hBmeas φ a b F z ∂(trimMeasure_T (μ := μ) T hBmeas) := by
        rw [show trimMeasure_T (μ := μ) T hBmeas
            = ((timeMeasure_T T).prod μ).trim
                (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod from rfl,
          integral_trim _ hgsm]
    _ = ∫ z in Set.Ioc a b ×ˢ F, ((φ : ℝ≥0 × Ω → ℝ) z) ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := integral_indicator hRpred

/-- **Isometry side.** The `𝓕_a`-set integral of the squared increment is the *same* rectangle
integral. `𝟙_F` is bounded and `𝓕_a`-measurable and the band integrand vanishes on `[0,a]`, so
`itoIntegralCLM_T_smulAdapted` folds it inside the integral; the isometry then turns the norm of
`𝟙_F·𝟙_{(a,b]}·φ` into the rectangle integral, `𝟙_F² = 𝟙_F` costing nothing on either side. -/
theorem setIntegral_sq_increment (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {a b : ℝ≥0} (hab : a ≤ b)
    {F : Set Ω} (hF : MeasurableSet[natFiltration hBmeas a] F) :
    ∫ ω in F, (⇑(itoIntegralCLM_T hB T hBmeas (bandRestrict (μ := μ) T a b hBmeas φ)) ω) ^ 2 ∂μ
      = ∫ z in Set.Ioc a b ×ˢ F, ((φ : ℝ≥0 × Ω → ℝ) z) ^ 2
          ∂(trimMeasure_T (μ := μ) T hBmeas) := by
  set Zf : Ω → ℝ := F.indicator (fun _ ↦ (1 : ℝ)) with hZf
  have hZm : Measurable[natFiltration hBmeas a] Zf := measurable_const.indicator hF
  have hZb : ∀ ω, |Zf ω| ≤ 1 := fun ω ↦ by by_cases h : ω ∈ F <;> simp [hZf, h]
  set χ := bandRestrict (μ := μ) T a b hBmeas φ with hχdef
  have hχ0 : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), p.1 ≤ a → (χ : ℝ≥0 × Ω → ℝ) p = 0 :=
    bandRestrict_eq_zero_of_le T a b hab hBmeas φ
  set ψ := smulAdapted T a hBmeas Zf hZm 1 hZb χ with hψdef
  have hRpred : MeasurableSet[(natFiltration (mΩ := mΩ) hBmeas).predictable]
      (Set.Ioc a b ×ˢ F) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod a b hF
  have hL : ‖itoIntegralCLM_T hB T hBmeas ψ‖ ^ 2
      = ∫ ω in F, (⇑(itoIntegralCLM_T hB T hBmeas χ) ω) ^ 2 ∂μ := by
    rw [lp_two_norm_sq, ← integral_indicator ((natFiltration hBmeas).le a F hF)]
    refine integral_congr_ae ?_
    filter_upwards [itoIntegralCLM_T_smulAdapted hB T a hBmeas Zf hZm 1 hZb χ hχ0] with ω hω
    rw [hω, hZf]
    by_cases h : ω ∈ F <;> simp [h]
  have hR : ‖ψ‖ ^ 2 = ∫ z in Set.Ioc a b ×ˢ F, ((φ : ℝ≥0 × Ω → ℝ) z) ^ 2
      ∂(trimMeasure_T (μ := μ) T hBmeas) := by
    rw [lp_two_norm_sq, ← integral_indicator hRpred]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_smulAdapted T a hBmeas Zf hZm 1 hZb χ hχ0,
      coeFn_bandRestrict (μ := μ) T a b hab hBmeas φ] with z e1 e2
    rw [e1, e2, hZf]
    by_cases hz1 : z.1 ∈ Set.Ioc a b <;> by_cases hz2 : z.2 ∈ F <;>
      simp [Set.mem_prod, hz1, hz2]
  rw [← hL, ← hR, itoIntegralCLM_T_norm]

/-! ### The conditional second moment -/

/-- **The bracket is conditional.** For `M = φ●B` on `[0,T]` and `a ≤ b ≤ T`,

  `μ[(M_b − M_a)² | 𝓕_a] =ᵐ μ[⟨M⟩_b − ⟨M⟩_a | 𝓕_a]`,

with `⟨M⟩_b − ⟨M⟩_a` the pathwise `∫_a^b φ_u(ω)² du`. This is the defining property quadratic
variation exists for, in the form `bracketMeasure` cannot state: `norm_sq_increment_eq_bracket`
integrates `ω` out, and conditioning on `𝓕_a` is exactly what that loses.

Both sides are compared through their `𝓕_a`-set integrals, which meet at the rectangle integral
`∫_{(a,b]×F} φ²` — `setIntegral_sq_increment` by localisation and the isometry,
`setIntegral_bracketRep` by Tonelli. -/
theorem condExp_band_second_moment (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) {a b : ℝ≥0} (hab : a ≤ b) (hbT : b ≤ T) :
    (μ[fun ω ↦ (⇑(itoProcessCLM hB T b hBmeas φ) ω
        - ⇑(itoProcessCLM hB T a hBmeas φ) ω) ^ 2 | natFiltration hBmeas a])
      =ᵐ[μ] (μ[bracketRep (μ := μ) T hBmeas φ a b | natFiltration hBmeas a]) := by
  have hcoe : ⇑(itoIntegralCLM_T hB T hBmeas (bandRestrict (μ := μ) T a b hBmeas φ))
      =ᵐ[μ] fun ω ↦ ⇑(itoProcessCLM hB T b hBmeas φ) ω
        - ⇑(itoProcessCLM hB T a hBmeas φ) ω := by
    rw [itoIntegralCLM_T_bandRestrict (hB := hB) T hBmeas φ hab hbT]
    exact Lp.coeFn_sub _ _
  have hXeq : (fun ω ↦ (⇑(itoProcessCLM hB T b hBmeas φ) ω
        - ⇑(itoProcessCLM hB T a hBmeas φ) ω) ^ 2)
      =ᵐ[μ] fun ω ↦
        (⇑(itoIntegralCLM_T hB T hBmeas (bandRestrict (μ := μ) T a b hBmeas φ)) ω) ^ 2 := by
    filter_upwards [hcoe] with ω hω
    rw [hω]
  refine (condExp_congr_ae hXeq).trans ?_
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((natFiltration hBmeas).le a)
    ((Lp.memLp (itoIntegralCLM_T hB T hBmeas
      (bandRestrict (μ := μ) T a b hBmeas φ))).integrable_sq)
    (fun s _ _ ↦ integrable_condExp.integrableOn) (fun s hs _ ↦ ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  rw [setIntegral_condExp ((natFiltration hBmeas).le a)
    (integrable_bracketRep T hBmeas φ hbT) hs]
  exact (setIntegral_bracketRep T hBmeas φ hbT hs).trans
    (setIntegral_sq_increment hB T hBmeas φ hab hs).symm

/-! ### The pointwise reading on an elementary integrand -/

omit [IsProbabilityMeasure μ] in
/-- **The elementary Riemann–Stieltjes term, with an integrable coefficient.** For `a ≤ c ≤ d`
and `Z` measurable at `c`, `μ[(Z·(B_d − B_c))² | 𝓕_a] =ᵐ (d−c)·μ[Z² | 𝓕_a]`. Kernel 3 at
`χ = Z²`; it asks only that `Z²` and `(Z·ΔB)²` be integrable, where routing the same coefficient
through `condExp_band_second_moment` means exhibiting `Z·1_{(c,d]}` as an `L²(trim_T)` class, and
this file's constructor for that, `bandGen`, wants `Z` bounded. -/
theorem condExp_increment_sq_of_adapted (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hprob : IsProbabilityMeasure μ)
    {a c d : ℝ≥0} (hac : a ≤ c) (hcd : c ≤ d)
    {Z : Ω → ℝ} (hZm : Measurable[natFiltration hBmeas c] Z)
    (hZsq : Integrable (fun ω ↦ Z ω ^ 2) μ)
    (hint : Integrable (fun ω ↦ (Z ω * (B d ω - B c ω)) ^ 2) μ) :
    (μ[fun ω ↦ (Z ω * (B d ω - B c ω)) ^ 2 | natFiltration hBmeas a])
      =ᵐ[μ] fun ω ↦ ((d : ℝ) - c) * (μ[fun ω ↦ Z ω ^ 2 | natFiltration hBmeas a]) ω := by
  have heq : (fun ω ↦ (Z ω * (B d ω - B c ω)) ^ 2)
      = fun ω ↦ Z ω ^ 2 * (B d ω - B c ω) ^ 2 := funext fun ω ↦ by ring
  rw [heq] at hint ⊢
  exact condExp_adapted_mul_increment_sq hB hBmeas hprob hac hcd
    (hZm.pow_const 2).stronglyMeasurable hZsq hint

/-! #### The band generator as a process -/

/-- **Nothing before the band opens.** The elementary integral process of `Z·1_{(c,d]}` is `0` at
every time up to `c`: `bandGen_support` is exactly the hypothesis time-locality consumes. -/
theorem itoProcessCLM_bandGen_eq_zero (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) {c d : ℝ≥0} (hcd : c ≤ d) (hdT : d ≤ T)
    {Z : Ω → ℝ} (hZm : Measurable[natFiltration hBmeas c] Z) (C : ℝ)
    (hZb : ∀ ω, |Z ω| ≤ C) {t : ℝ≥0} (htc : t ≤ c) :
    itoProcessCLM hB T t hBmeas (bandGen (μ := μ) T hBmeas hcd hdT hZm C hZb) = 0 := by
  refine itoProcessCLM_eq_zero_of_vanishes_before (hB := hB) T t
    (htc.trans (hcd.trans hdT)) hBmeas _ ?_
  filter_upwards [bandGen_support hBmeas hcd hdT hZm C hZb] with p hp hpt
  exact hp (hpt.trans htc)

/-- **Everything once it closes.** From `d` on the process holds its terminal value
`Z·(B_d − B_c)`: `bandGen_support_after` says the integrand is spent, so the terminal integral is
already the process at `t`, and `eval_bandGen` names it. -/
theorem itoProcessCLM_bandGen_eq_increment (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) {c d : ℝ≥0} (hcd : c ≤ d) (hdT : d ≤ T)
    {Z : Ω → ℝ} (hZm : Measurable[natFiltration hBmeas c] Z) (C : ℝ)
    (hZb : ∀ ω, |Z ω| ≤ C) {t : ℝ≥0} (hdt : d ≤ t) (htT : t ≤ T) :
    ⇑(itoProcessCLM hB T t hBmeas (bandGen (μ := μ) T hBmeas hcd hdT hZm C hZb))
      =ᵐ[μ] fun ω ↦ Z ω * (B d ω - B c ω) := by
  have hafter : ∀ᵐ p ∂(trimMeasure_T (μ := μ) T hBmeas), t < p.1 →
      (bandGen (μ := μ) T hBmeas hcd hdT hZm C hZb : ℝ≥0 × Ω → ℝ) p = 0 := by
    filter_upwards [bandGen_support_after hBmeas hcd hdT hZm C hZb] with p hp hpt
    exact hp (hdt.trans_lt hpt)
  rw [← itoIntegralCLM_T_eq_itoProcessCLM_of_vanishes_after (hB := hB) T t htT hBmeas _ hafter]
  exact eval_bandGen hB T hBmeas hcd hdT hZm C hZb

omit [IsProbabilityMeasure μ] in
/-- **The general identity, on the integrands one can write down.** Take `M = (Z·1_{(c,d]})●B`
with `Z` bounded and `𝓕_c`-measurable, and a band `(a,b]` containing `(c,d]`. Then

  `μ[(M_b − M_a)² | 𝓕_a] =ᵐ (d − c)·μ[Z² | 𝓕_a]`,

whose left-hand side is literally `condExp_band_second_moment`'s, on the one integrand whose Itô
integral is written out — and whose right-hand side is the classical `(d−c)·μ[Z²|𝓕_a]`. The
process ends supply the increment (`itoProcessCLM_bandGen_eq_zero`,
`itoProcessCLM_bandGen_eq_increment`) and the kernels close it, so the derivation is independent
of the general theorem — but the two statements are now the *same* statement, because
`bracketRep_bandGen` evaluates this integrand's pathwise bracket over `(a,b]` as `Z²·(d−c)`. -/
theorem condExp_bandGen_second_moment (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hprob : IsProbabilityMeasure μ)
    {a b c d : ℝ≥0} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) (hbT : b ≤ T)
    {Z : Ω → ℝ} (hZm : Measurable[natFiltration hBmeas c] Z) (C : ℝ)
    (hZb : ∀ ω, |Z ω| ≤ C) :
    (μ[fun ω ↦ (⇑(itoProcessCLM hB T b hBmeas
          (bandGen (μ := μ) T hBmeas hcd (hdb.trans hbT) hZm C hZb)) ω
        - ⇑(itoProcessCLM hB T a hBmeas
          (bandGen (μ := μ) T hBmeas hcd (hdb.trans hbT) hZm C hZb)) ω) ^ 2
        | natFiltration hBmeas a])
      =ᵐ[μ] fun ω ↦ ((d : ℝ) - c) * (μ[fun ω ↦ Z ω ^ 2 | natFiltration hBmeas a]) ω := by
  have hZmΩ : Measurable Z := hZm.mono ((natFiltration hBmeas).le c) le_rfl
  have hZinf : MemLp Z ∞ μ :=
    MemLp.of_bound hZmΩ.aestronglyMeasurable C
      (Eventually.of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hZb ω)
  have hZsq : Integrable (fun ω ↦ Z ω ^ 2) μ :=
    (MemLp.of_bound (μ := μ) hZmΩ.aestronglyMeasurable C
      (Eventually.of_forall fun ω ↦ by
        simpa [Real.norm_eq_abs] using hZb ω) : MemLp Z 2 μ).integrable_sq
  have hint : Integrable (fun ω ↦ (Z ω * (B d ω - B c ω)) ^ 2) μ :=
    (MemLp.mul (hf := hZinf) (hφ := memLp_increment hB hBmeas hcd)).integrable_sq.congr
      (Filter.Eventually.of_forall fun ω ↦ by
        show (((fun ω ↦ B d ω - B c ω) * Z) ω) ^ 2 = (Z ω * (B d ω - B c ω)) ^ 2
        rw [Pi.mul_apply, mul_comm])
  have hzero : ⇑(itoProcessCLM hB T a hBmeas
      (bandGen (μ := μ) T hBmeas hcd (hdb.trans hbT) hZm C hZb)) =ᵐ[μ] 0 := by
    rw [itoProcessCLM_bandGen_eq_zero hB T hBmeas hcd (hdb.trans hbT) hZm C hZb hac]
    exact Lp.coeFn_zero ℝ 2 μ
  refine (condExp_congr_ae ?_).trans
    (condExp_increment_sq_of_adapted hB hBmeas hprob hac hcd hZm hZsq hint)
  filter_upwards [hzero, itoProcessCLM_bandGen_eq_increment hB T hBmeas hcd (hdb.trans hbT)
    hZm C hZb hdb hbT] with ω h0 hb
  rw [h0, hb, Pi.zero_apply, sub_zero]

end PointwiseBracket
end MathFin
