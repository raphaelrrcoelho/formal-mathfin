/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import BrownianMotion.Gaussian.BrownianMotion
import BrownianMotion.StochasticIntegral.SimpleProcess
import QuantFin.Foundations.ItoIsometryAdapted

/-!
# The L²-adapted Itô isometry, anchored on Degenne's `SimpleProcess`

This file establishes the **Itô isometry for adapted simple processes** — the substantive
analytic content of the L² Itô integral — built on Degenne's
`BrownianMotion.StochasticIntegral` objects (the maximally-coherent choice). The cornerstone
is that the cross-terms vanish by the **weak Markov property** (`rect_increment_pairing`,
from `ItoIsometryAdapted.lean`), *not* by deterministic covariance — the precise distinction
between the Itô integral (random adapted integrands) and the Wiener integral (deterministic
integrands, `WienerIntegralL2.lean`). Degenne's `SimpleProcess` allows *overlapping*
intervals, which is exactly why `rect_increment_pairing` is the right tool.

## Results

* `natFiltration` — the natural Brownian filtration `𝓕ᴮ_t = σ(B_u : u ≤ t)`.
* `adaptedAt_of_measurable_natural` — the bridge from `natural B`-measurability (which
  `SimpleProcess.value` carries) to `ItoIsometryAdapted.AdaptedAt` (factoring through the
  past process), via Doob–Dynkin (`Measurable.exists_eq_measurable_comp`). This is what
  lets the `AdaptedAt`-stated isometry core consume Degenne's `SimpleProcess`.
* `itoSimple` / `itoSimple_apply` — the elementary Itô integral
  `(V ● B)_⊤ = ∑ₚ V(p)·(B_{p.2}−B_{p.1})` (Degenne's `SimpleProcess.integral` against
  multiplication, at the terminal time `⊤`).
* `memLp_itoSimple` / `itoSimpleLp` — it lies in `L²(μ)`.
* `itoSimple_sq_integral` / `itoSimpleLp_norm_sq` — **the Itô isometry**:
  `‖itoSimpleLp V‖² = ∫ (itoSimple V)² dμ = Σ_{p,q} E[V(p)·V(q)] · vol((p]∩(q])`.

## Scope (why this stops at the isometry)

The continuous extension to a CLM `L2Predictable ν μ →L[ℝ] Lp ℝ 2 μ` (density of simple
processes in the predictable `L²` via `generateFrom_eq_predictable` + `LinearMap.extendOfNorm`)
is **deliberately not built**. It is standard L²-completion packaging with no consumer in
this library: pricing here goes through static Gaussian methods (the static-Girsanov/Esscher
EMM, Black–Scholes, Margrabe — leaps 1–3 bypass the Itô integral entirely). A continuous Itô
*integral* only pays off as the base of a full continuous-time Itô-*calculus* layer (Itô's
lemma, SDEs, continuous Girsanov) — a separate, upstream-Mathlib-scale program. The isometry
above is the self-contained cornerstone of the L²-adapted construction. The verified `ν`
midpoint and the full CLM resume-plan are preserved in `docs/ito-integral-clm-deferred.md`.
-/

namespace QuantFin
namespace ItoIntegralL2

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- The **natural Brownian filtration** `𝓕ᴮ_t = σ(B_u : u ≤ t)`. -/
noncomputable def natFiltration (hBmeas : ∀ t, Measurable (B t)) : Filtration ℝ≥0 mΩ :=
  Filtration.natural B (fun t => (hBmeas t).stronglyMeasurable)

/-- **Bridge to the past-process encoding.** A function measurable with respect to
the natural Brownian filtration at `s` is `ItoIsometryAdapted.AdaptedAt B s` —
it factors through the past process `ω ↦ (B u ω)_{u ≤ s}`. This is the
Doob–Dynkin factorisation (`Measurable.exists_eq_measurable_comp`, valid since
ℝ is a standard Borel space), and it is what makes the `AdaptedAt`-stated
isometry core (`rect_increment_pairing` et al.) applicable to Degenne's
`SimpleProcess`, whose `value` is `𝓕 p.1`-measurable. -/
theorem adaptedAt_of_measurable_natural (hBmeas : ∀ t, Measurable (B t)) {s : ℝ≥0}
    {f : Ω → ℝ} (hf : Measurable[natFiltration hBmeas s] f) :
    ItoIsometryAdapted.AdaptedAt B s f := by
  -- `natural B s = ⨆ u ≤ s, comap (B u) ≤ comap (pastProcess B s)`, since each
  -- `B u` (u ≤ s) factors as `eval_u ∘ pastProcess`.
  have hle : (natFiltration hBmeas s) ≤
      MeasurableSpace.comap (ItoIsometryAdapted.pastProcess B s) inferInstance := by
    refine iSup₂_le fun u hu => ?_
    have hBu : B u
        = (fun p : Set.Iic s → ℝ => p ⟨u, hu⟩) ∘ ItoIsometryAdapted.pastProcess B s := rfl
    rw [hBu, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp (measurable_pi_apply _))
  obtain ⟨g, hg, hgeq⟩ := (hf.mono hle le_rfl).exists_eq_measurable_comp
  exact ⟨g, hg, hgeq⟩

/-- The **elementary Itô integral** of a simple process `V` against Brownian motion
`B`, evaluated at the terminal time: `(V ● B)_⊤`. Built from Degenne's
`SimpleProcess.integral` against the multiplication bilinear map. -/
noncomputable def itoSimple (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) : Ω → ℝ :=
  SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ) V B ⊤

/-- The terminal Itô integral as the explicit increment sum
`(V ● B)_⊤ ω = ∑ₚ V(p) ω · (B_{p.2} ω − B_{p.1} ω)`. -/
lemma itoSimple_apply (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (ω : Ω) :
    itoSimple hBmeas V ω
      = V.value.sum fun p v => v ω * (B p.2 ω - B p.1 ω) := by
  simp only [itoSimple, SimpleProcess.integral_top, ContinuousLinearMap.mul_apply']

variable [hB : IsPreBrownian B μ]

/-- **Step 1 — `L²` membership.** The terminal Itô integral of a simple process is in
`L²(μ)`: it is the finite sum `∑ₚ V(p)·(B_{p.2}−B_{p.1})`, and each summand is in `L²`
by `memLp_adapted_mul_increment` — the coefficient `V(p)` is `𝓕_{p.1}`-measurable (hence
`AdaptedAt` by the bridge) and bounded (hence `L²` on the probability space). -/
theorem memLp_itoSimple (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    MemLp (itoSimple hBmeas V) 2 μ := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rw [show itoSimple hBmeas V
        = fun ω => ∑ p ∈ V.value.support, V.value p ω * (B p.2 ω - B p.1 ω)
      from funext fun ω => by rw [itoSimple_apply]; rfl]
  refine memLp_finsetSum V.value.support (fun p hp => ?_)
  refine ItoIsometryAdapted.memLp_adapted_mul_increment hBmeas (V.le_of_mem_support_value p hp)
    (adaptedAt_of_measurable_natural hBmeas (V.measurable_value p)) ?_
  exact MemLp.of_bound
    ((V.measurable_value p).mono ((natFiltration hBmeas).le p.1) le_rfl).aestronglyMeasurable
    V.valueBound (ae_of_all _ (V.value_le_valueBound p))

/-- The terminal Itô integral of a simple process as an element of `Lp ℝ 2 μ`. -/
noncomputable def itoSimpleLp (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) : Lp ℝ 2 μ :=
  (memLp_itoSimple hBmeas V).toLp _

/-- **Step 2 — the Itô isometry on simple processes** (the predictable-rectangle double
sum). For a simple process `V`,

  `∫ (itoSimple V)² dμ = Σ_{p,q} E[V(p)·V(q)] · vol((p.1,p.2] ∩ (q.1,q.2])`,

where `vol((p.1,p.2] ∩ (q.1,q.2]) = max 0 (min p.2 q.2 − max p.1 q.1)`. The square of the
increment sum expands into a double sum whose every term collapses by
`rect_increment_pairing` — the genuinely-stochastic content (cross terms vanish by the
weak Markov property, diagonal terms give the deterministic overlap). The right-hand side
is exactly `‖V‖²` in the predictable `L²` space, so this is the Itô isometry. -/
theorem itoSimple_sq_integral (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    ∫ ω, (itoSimple hBmeas V ω) ^ 2 ∂μ
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  classical
  set a : (ℝ≥0 × ℝ≥0) → Ω → ℝ := fun p ω => V.value p ω * (B p.2 ω - B p.1 ω) with ha_def
  have ha_L2 : ∀ p ∈ V.value.support, MemLp (a p) 2 μ := fun p hp =>
    ItoIsometryAdapted.memLp_adapted_mul_increment hBmeas (V.le_of_mem_support_value p hp)
      (adaptedAt_of_measurable_natural hBmeas (V.measurable_value p))
      (MemLp.of_bound
        ((V.measurable_value p).mono ((natFiltration hBmeas).le p.1) le_rfl).aestronglyMeasurable
        V.valueBound (ae_of_all _ (V.value_le_valueBound p)))
  have hint : ∀ p ∈ V.value.support, ∀ q ∈ V.value.support,
      Integrable (fun ω => a p ω * a q ω) μ :=
    fun p hp q hq => (ha_L2 p hp).integrable_mul (ha_L2 q hq)
  calc ∫ ω, (itoSimple hBmeas V ω) ^ 2 ∂μ
      = ∫ ω, ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, a p ω * a q ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show itoSimple hBmeas V ω ^ 2
          = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, a p ω * a q ω
        rw [show itoSimple hBmeas V ω = ∑ p ∈ V.value.support, a p ω from by
              rw [itoSimple_apply]; rfl, sq, Finset.sum_mul_sum]
    _ = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, ∫ ω, a p ω * a q ω ∂μ := by
        rw [integral_finsetSum _ (fun p hp => integrable_finsetSum _ fun q hq => hint p hp q hq)]
        exact Finset.sum_congr rfl fun p hp =>
          integral_finsetSum _ (fun q hq => hint p hp q hq)
    _ = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
        refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
        exact ItoIsometryAdapted.rect_increment_pairing hBmeas
          (adaptedAt_of_measurable_natural hBmeas (V.measurable_value p))
          (adaptedAt_of_measurable_natural hBmeas (V.measurable_value q))
          (fun ω => by rw [← Real.norm_eq_abs]; exact V.value_le_valueBound p ω)
          (fun ω => by rw [← Real.norm_eq_abs]; exact V.value_le_valueBound q ω)
          (V.le_of_mem_support_value p hp) (V.le_of_mem_support_value q hq)

omit [hB : IsPreBrownian B μ] in
/-- For `g : Lp ℝ 2 μ`, `‖g‖² = ∫ (g ω)² ∂μ` (the real `L²` norm-square as an integral). -/
private lemma lp_two_norm_sq (g : Lp ℝ 2 μ) : ‖g‖ ^ 2 = ∫ ω, (g ω) ^ 2 ∂μ := by
  have h : ⟪g, g⟫_ℝ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  rw [L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with ω
  show (g ω) * (g ω) = (g ω) ^ 2
  ring

/-- **The Itô isometry in `Lp`-norm form.** `‖itoSimpleLp V‖²` equals the predictable-
rectangle double sum — i.e. `‖V‖²` in the predictable `L²` space. This is the norm
identity that `extendOfNorm` consumes to build the continuous Itô integral. -/
theorem itoSimpleLp_norm_sq (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    ‖(itoSimpleLp hBmeas V : Lp ℝ 2 μ)‖ ^ 2
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  rw [lp_two_norm_sq, ← itoSimple_sq_integral hBmeas V]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_itoSimple hBmeas V).coeFn_toLp] with ω hω
  rw [show (itoSimpleLp hBmeas V : Ω → ℝ) ω = itoSimple hBmeas V ω from hω]

end ItoIntegralL2
end QuantFin
