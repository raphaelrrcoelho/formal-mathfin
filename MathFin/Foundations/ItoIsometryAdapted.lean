/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import BrownianMotion.Gaussian.BrownianMotion

/-!
# The adapted Itô isometry (the increment-independence cornerstone)

The Wiener integral (`Foundations/WienerIntegralL2.lean`) handles
*deterministic* integrands: there the cross-terms vanish by the BM
covariance `E[(B_t-B_s)(B_v-B_u)] = vol((s,t]∩(u,v])`. That is *not* the
Itô integral. The Itô integral allows a **random, adapted** integrand
`φ`, and the cross-terms vanish for a different, deeper reason: the next
increment `B_{t₁} - B_{t₀}` is *independent of the past* `𝓕_{t₀}` (the weak
Markov property `IsPreBrownian.indepFun_shift`), and has mean zero.

This file builds that genuinely-stochastic core, grounded directly on
Degenne's `IsPreBrownian.indepFun_shift` and `hasLaw_sub`. Adaptedness is
encoded faithfully as factoring through the *past process*
`fun (t : Set.Iic t₀) ↦ B t ω` — the natural Brownian filtration, which is
exactly what `indepFun_shift` is stated against.

## Crux results

* `adapted_indepFun_increment` — an integrand adapted to `𝓕_{t₀}` is
  independent of the forward increment `B_{t₁} - B_{t₀}`.
* `integral_adapted_mul_increment` — **martingale-difference property**:
  `E[φ · (B_{t₁} - B_{t₀})] = 0` for `φ` adapted and integrable. This is
  the discrete statement that the Itô integral is a martingale.
* `integral_adapted_mul_increment_sq` — **isometry kernel**:
  `E[χ · (B_{t₁} - B_{t₀})²] = E[χ] · (t₁ - t₀)` (with the square form
  `integral_adapted_sq_mul_increment_sq` as the `χ = φ²` corollary).

## Coherence with upstream and the Wiener layer

Degenne's `BrownianMotion/StochasticIntegral/` already abstracts the
simple-predictable-integrand objects (`SimpleProcess`, `ElementaryPredictableSet`,
`L2Predictable`) — but proves **no** isometry; that is the gap this file fills.
We re-encode adaptedness concretely as `AdaptedAt` (factoring through
`pastProcess`) so that the weak-Markov independence `IsPreBrownian.indepFun_shift`
applies directly. Likewise `integral_two_increment` / `integral_increment_sq`
are the shared-start (`s = u`) and diagonal instances of
`WienerIntegralL2.covariance_increment_aux`, re-derived here only because this
(non-`module`) file does not yet import that layer. Unifying onto the package's
`SimpleProcess`/`L2Predictable`, adopting the `module` convention of
`WienerIntegral*.lean`, and extracting the single shared increment-covariance
lemma are deferred to the continuous-integral build that consumes both layers.
-/

namespace MathFin
namespace ItoIsometryAdapted

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} [hB : IsPreBrownian B μ]

/-- The past process up to time `t₀`: `ω ↦ (fun t : Iic t₀ ↦ B t ω)`.
This is the random variable generating the natural filtration `𝓕_{t₀}`. -/
def pastProcess (B : ℝ≥0 → Ω → ℝ) (t₀ : ℝ≥0) : Ω → (Set.Iic t₀ → ℝ) :=
  fun ω t => B t ω

/-- A function `φ : Ω → ℝ` is **adapted at `t₀`** if it factors through the
past process via a measurable map — i.e. it is `𝓕_{t₀}`-measurable in the
natural Brownian filtration. -/
def AdaptedAt (B : ℝ≥0 → Ω → ℝ) (t₀ : ℝ≥0) (φ : Ω → ℝ) : Prop :=
  ∃ g : (Set.Iic t₀ → ℝ) → ℝ, Measurable g ∧ φ = g ∘ pastProcess B t₀

/-- Measurability of an adapted integrand (factors through the measurable
past process). -/
theorem AdaptedAt.measurable (hBmeas : ∀ t, Measurable (B t)) {t₀ : ℝ≥0}
    {φ : Ω → ℝ} (hφ : AdaptedAt B t₀ φ) : Measurable φ := by
  obtain ⟨g, hg, rfl⟩ := hφ
  exact hg.comp (measurable_pi_lambda _ fun _ => hBmeas _)

/-! ### Adaptedness algebra (the natural Brownian filtration `𝓕_{t₀}`)

`AdaptedAt B t₀` behaves as a `𝓕_{t₀}`-measurability predicate: it contains
each `B u` for `u ≤ t₀`, is monotone in `t₀`, and is closed under products
and differences. This is exactly the closure needed to certify that the
cross-term factor `φⱼ · ΔBⱼ · φₖ` is `𝓕_{tₖ}`-measurable. -/

/-- `B u` is adapted at any later time `t₀ ≥ u`. -/
theorem adaptedAt_eval {t₀ u : ℝ≥0} (hu : u ≤ t₀) : AdaptedAt B t₀ (B u) :=
  ⟨fun p => p ⟨u, hu⟩, measurable_pi_apply _, rfl⟩

/-- Adaptedness is monotone in the time index. -/
theorem AdaptedAt.mono {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) {φ : Ω → ℝ}
    (hφ : AdaptedAt B t₀ φ) : AdaptedAt B t₁ φ := by
  obtain ⟨g, hg, rfl⟩ := hφ
  exact ⟨g ∘ fun p : Set.Iic t₁ → ℝ => fun s : Set.Iic t₀ => p ⟨(s : ℝ≥0), le_trans s.2 ht⟩,
    hg.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _), rfl⟩

/-- Products of adapted integrands are adapted. -/
theorem AdaptedAt.mul {t₀ : ℝ≥0} {φ ψ : Ω → ℝ}
    (hφ : AdaptedAt B t₀ φ) (hψ : AdaptedAt B t₀ ψ) :
    AdaptedAt B t₀ (fun ω => φ ω * ψ ω) := by
  obtain ⟨g, hg, rfl⟩ := hφ
  obtain ⟨h, hh, rfl⟩ := hψ
  exact ⟨fun p => g p * h p, hg.mul hh, rfl⟩

/-- Differences of adapted integrands are adapted. -/
theorem AdaptedAt.sub {t₀ : ℝ≥0} {φ ψ : Ω → ℝ}
    (hφ : AdaptedAt B t₀ φ) (hψ : AdaptedAt B t₀ ψ) :
    AdaptedAt B t₀ (fun ω => φ ω - ψ ω) := by
  obtain ⟨g, hg, rfl⟩ := hφ
  obtain ⟨h, hh, rfl⟩ := hψ
  exact ⟨fun p => g p - h p, hg.sub hh, rfl⟩

/-- An adapted integrand is independent of the forward increment. The deep
content: `B_{t₁} - B_{t₀}` is independent of `𝓕_{t₀}` (weak Markov,
`IsPreBrownian.indepFun_shift`), and `φ` is `𝓕_{t₀}`-measurable. -/
theorem adapted_indepFun_increment
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : AdaptedAt B t₀ φ) :
    IndepFun φ (fun ω => B t₁ ω - B t₀ ω) μ := by
  obtain ⟨g, hg, rfl⟩ := hφ
  -- Forward increment process is independent of the past process.
  have hshift := hB.indepFun_shift hBmeas t₀
  -- `B t₁ - B t₀ = eval_(t₁-t₀) ∘ fwd`, with `t₀ + (t₁-t₀) = t₁`.
  have hΔ : t₀ + (t₁ - t₀) = t₁ := add_tsub_cancel_of_le ht
  have hfun : (fun ω => B t₁ ω - B t₀ ω) =
      (fun p : ℝ≥0 → ℝ => p (t₁ - t₀)) ∘ (fun ω t => B (t₀ + t) ω - B t₀ ω) := by
    funext ω
    simp only [Function.comp_apply, hΔ]
  rw [hfun]
  exact hshift.symm.comp hg (measurable_pi_apply _)

/-- **Martingale-difference property of the Itô integral** (discrete form):
for `φ` adapted to `𝓕_{t₀}`, the integrand times the next Brownian increment
has mean zero, `E[φ · (B_{t₁} - B_{t₀})] = 0`. This is the reason the Itô
integral is a martingale — and it holds for *random* `φ`, where the Wiener
(deterministic) covariance argument does not apply. -/
theorem integral_adapted_mul_increment
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : AdaptedAt B t₀ φ) :
    ∫ ω, φ ω * (B t₁ ω - B t₀ ω) ∂μ = 0 := by
  have hindep := adapted_indepFun_increment (μ := μ) hBmeas ht hφ
  have hφm : Measurable φ := hφ.measurable hBmeas
  have hΔm : Measurable (fun ω => B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  rw [hindep.integral_fun_mul_eq_mul_integral hφm.aestronglyMeasurable
        hΔm.aestronglyMeasurable]
  have hmean : ∫ ω, (B t₁ ω - B t₀ ω) ∂μ = 0 := by
    have h := (hB.hasLaw_sub t₁ t₀).integral_eq
    rwa [integral_id_gaussianReal] at h
  rw [hmean, mul_zero]

/-- The forward increment has second moment `E[(B_{t₁} - B_{t₀})²] = t₁ - t₀`
(mean zero, variance `t₁ - t₀`). -/
theorem integral_increment_sq
    {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) (hBmeas : ∀ t, Measurable (B t)) :
    ∫ ω, (B t₁ ω - B t₀ ω) ^ 2 ∂μ = (t₁ : ℝ) - t₀ := by
  have hΔm : Measurable (fun ω => B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  have hmean : ∫ ω, (B t₁ ω - B t₀ ω) ∂μ = 0 := by
    have h := (hB.hasLaw_sub t₁ t₀).integral_eq
    rwa [integral_id_gaussianReal] at h
  have hmax : (max (t₁ - t₀) (t₀ - t₁) : ℝ≥0) = t₁ - t₀ :=
    max_eq_left (by rw [tsub_eq_zero_of_le ht]; exact zero_le)
  rw [← variance_of_integral_eq_zero hΔm.aemeasurable hmean]
  show Var[B t₁ - B t₀; μ] = (t₁ : ℝ) - t₀
  rw [(hB.hasLaw_sub t₁ t₀).variance_eq, variance_id_gaussianReal, hmax, NNReal.coe_sub ht]

/-- **General isometry kernel**: for `χ` adapted to `𝓕_{t₀}`,
`E[χ · (B_{t₁} - B_{t₀})²] = E[χ] · (t₁ - t₀)`. The increment's square is
independent of the past (weak Markov) and has mean `t₁ - t₀`. Specialises to
`integral_adapted_sq_mul_increment_sq` (take `χ = φ²`); supplies the *diagonal*
term of the bilinear isometry below (`χ = φₖ · ψₖ`). -/
theorem integral_adapted_mul_increment_sq
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {χ : Ω → ℝ} (hχ : AdaptedAt B t₀ χ) :
    ∫ ω, χ ω * (B t₁ ω - B t₀ ω) ^ 2 ∂μ = (∫ ω, χ ω ∂μ) * ((t₁ : ℝ) - t₀) := by
  have hχm : Measurable χ := hχ.measurable hBmeas
  have hΔm : Measurable (fun ω => B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  have hindep := adapted_indepFun_increment (μ := μ) hBmeas ht hχ
  have hindep2 := hindep.comp (φ := (id : ℝ → ℝ)) (ψ := fun x : ℝ => x ^ 2)
    measurable_id (by fun_prop)
  have key := hindep2.integral_fun_mul_eq_mul_integral
    hχm.aestronglyMeasurable (hΔm.pow_const 2).aestronglyMeasurable
  simp only [Function.comp_apply, id_eq] at key
  rw [key, integral_increment_sq (μ := μ) ht hBmeas]

/-- **Isometry kernel** (the diagonal term of the Itô isometry): for `φ`
adapted to `𝓕_{t₀}`, `E[φ² · (B_{t₁} - B_{t₀})²] = E[φ²] · (t₁ - t₀)`. The
`χ = φ²` instance of `integral_adapted_mul_increment_sq`. -/
theorem integral_adapted_sq_mul_increment_sq
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : AdaptedAt B t₀ φ) :
    ∫ ω, (φ ω) ^ 2 * (B t₁ ω - B t₀ ω) ^ 2 ∂μ =
      (∫ ω, (φ ω) ^ 2 ∂μ) * ((t₁ : ℝ) - t₀) := by
  have hχ : AdaptedAt B t₀ (fun ω => (φ ω) ^ 2) := by
    obtain ⟨g, hg, rfl⟩ := hφ
    exact ⟨fun p => (g p) ^ 2, hg.pow_const 2, rfl⟩
  exact integral_adapted_mul_increment_sq hBmeas ht hχ

/-- If `φ` is adapted to `𝓕_{t₀}` and in `L²`, then `φ · (B_{t₁} - B_{t₀})` is
in `L²`: the increment is in `L²` and independent of `φ`, so the product's
square is integrable. This is the `L²`-membership of a single term of an
adapted simple integral. -/
theorem memLp_adapted_mul_increment
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : AdaptedAt B t₀ φ) (hφL2 : MemLp φ 2 μ) :
    MemLp (fun ω => φ ω * (B t₁ ω - B t₀ ω)) 2 μ := by
  have hindep := adapted_indepFun_increment (μ := μ) hBmeas ht hφ
  have hφm : Measurable φ := hφ.measurable hBmeas
  have hΔm : Measurable (fun ω => B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  have hφsq : Integrable (fun ω => (φ ω) ^ 2) μ := hφL2.integrable_sq
  have hΔsq : Integrable (fun ω => (B t₁ ω - B t₀ ω) ^ 2) μ :=
    (hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two).integrable_sq
  have hindep2 := hindep.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
    (by fun_prop) (by fun_prop)
  have hprod : Integrable
      (fun ω => (φ ω) ^ 2 * (B t₁ ω - B t₀ ω) ^ 2) μ := by
    have h := hindep2.integrable_mul hφsq hΔsq
    simpa [Function.comp, Pi.mul_apply] using h
  refine (memLp_two_iff_integrable_sq (hφm.mul hΔm).aestronglyMeasurable).mpr ?_
  simpa [mul_pow] using hprod

/-! ### The discrete Itô isometry over a partition -/

/-- **Bilinear cross terms vanish.** For two adapted integrand families `φ`,
`ψ` and `j < k`, `E[(φⱼ·ΔBⱼ)·(ψₖ·ΔBₖ)] = 0`. The factor `φⱼ·ΔBⱼ·ψₖ` is
`𝓕_{tₖ}`-measurable, and `ΔBₖ` is independent of it with mean zero. -/
theorem integral_cross_increment_bilinear_eq_zero
    (hBmeas : ∀ s, Measurable (B s)) {t : ℕ → ℝ≥0} (hmono : Monotone t)
    {φ ψ : ℕ → Ω → ℝ} (hφ : ∀ n, AdaptedAt B (t n) (φ n))
    (hψ : ∀ n, AdaptedAt B (t n) (ψ n)) {j k : ℕ} (hjk : j < k) :
    ∫ ω, (φ j ω * (B (t (j + 1)) ω - B (t j) ω)) *
          (ψ k ω * (B (t (k + 1)) ω - B (t k) ω)) ∂μ = 0 := by
  have hΦ : AdaptedAt B (t k)
      (fun ω => φ j ω * (B (t (j + 1)) ω - B (t j) ω) * ψ k ω) :=
    (((hφ j).mono (hmono hjk.le)).mul
      ((adaptedAt_eval (hmono hjk)).sub (adaptedAt_eval (hmono hjk.le)))).mul (hψ k)
  have hstep : t k ≤ t (k + 1) := hmono (Nat.le_succ k)
  have h0 := integral_adapted_mul_increment (μ := μ) hBmeas hstep hΦ
  rw [show (fun ω => (φ j ω * (B (t (j + 1)) ω - B (t j) ω)) *
        (ψ k ω * (B (t (k + 1)) ω - B (t k) ω)))
      = (fun ω => (φ j ω * (B (t (j + 1)) ω - B (t j) ω) * ψ k ω) *
        (B (t (k + 1)) ω - B (t k) ω)) from by funext ω; ring]
  exact h0

/-- **The bilinear discrete Itô isometry** (the inner-product/polarised form).
For adapted `L²` integrand families `φ`, `ψ` over a partition `t`,

  `E[(Σₖ φₖ·ΔBₖ)·(Σₖ ψₖ·ΔBₖ)] = Σₖ E[φₖ·ψₖ]·(t_{k+1} − t_k)`.

This is the workhorse for the continuous Itô isometry: the inner product of two
adapted simple integrals is the `L²(Ω × [0,T])` inner product of the integrands.
The diagonal terms give the mixed kernel `integral_adapted_mul_increment_sq`;
the off-diagonal terms vanish by `integral_cross_increment_bilinear_eq_zero`. -/
theorem ito_isometry_discrete_bilinear
    (hBmeas : ∀ s, Measurable (B s)) {N : ℕ} {t : ℕ → ℝ≥0} (hmono : Monotone t)
    {φ ψ : ℕ → Ω → ℝ} (hφ : ∀ n, AdaptedAt B (t n) (φ n))
    (hψ : ∀ n, AdaptedAt B (t n) (ψ n))
    (hφL2 : ∀ n, MemLp (φ n) 2 μ) (hψL2 : ∀ n, MemLp (ψ n) 2 μ) :
    ∫ ω, (∑ k ∈ Finset.range N, φ k ω * (B (t (k + 1)) ω - B (t k) ω)) *
          (∑ k ∈ Finset.range N, ψ k ω * (B (t (k + 1)) ω - B (t k) ω)) ∂μ =
      ∑ k ∈ Finset.range N, (∫ ω, φ k ω * ψ k ω ∂μ) * ((t (k + 1) : ℝ) - t k) := by
  classical
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  set a : ℕ → Ω → ℝ := fun k ω => φ k ω * (B (t (k + 1)) ω - B (t k) ω) with ha_def
  set b : ℕ → Ω → ℝ := fun k ω => ψ k ω * (B (t (k + 1)) ω - B (t k) ω) with hb_def
  have ha_L2 : ∀ k, MemLp (a k) 2 μ := fun k =>
    memLp_adapted_mul_increment hBmeas (hmono (Nat.le_succ k)) (hφ k) (hφL2 k)
  have hb_L2 : ∀ k, MemLp (b k) 2 μ := fun k =>
    memLp_adapted_mul_increment hBmeas (hmono (Nat.le_succ k)) (hψ k) (hψL2 k)
  have hint : ∀ j k, Integrable (fun ω => a j ω * b k ω) μ := fun j k =>
    (ha_L2 j).integrable_mul (hb_L2 k)
  -- Diagonal term = mixed variance kernel.
  have hdiag : ∀ k, ∫ ω, a k ω * b k ω ∂μ =
      (∫ ω, φ k ω * ψ k ω ∂μ) * ((t (k + 1) : ℝ) - t k) := by
    intro k
    have hstep : t k ≤ t (k + 1) := hmono (Nat.le_succ k)
    have hχ : AdaptedAt B (t k) (fun ω => φ k ω * ψ k ω) := (hφ k).mul (hψ k)
    rw [show (fun ω => a k ω * b k ω)
          = (fun ω => (φ k ω * ψ k ω) * (B (t (k + 1)) ω - B (t k) ω) ^ 2) from by
            funext ω; simp only [ha_def, hb_def]; ring]
    exact integral_adapted_mul_increment_sq (μ := μ) hBmeas hstep hχ
  -- Off-diagonal terms vanish.
  have hcross : ∀ j ∈ Finset.range N, ∀ k ∈ Finset.range N, j ≠ k →
      ∫ ω, a j ω * b k ω ∂μ = 0 := by
    intro j _ k _ hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact integral_cross_increment_bilinear_eq_zero hBmeas hmono hφ hψ h
    · rw [show (fun ω => a j ω * b k ω) = (fun ω => b k ω * a j ω) from by funext ω; ring]
      exact integral_cross_increment_bilinear_eq_zero hBmeas hmono hψ hφ h
  calc ∫ ω, (∑ k ∈ Finset.range N, a k ω) * (∑ k ∈ Finset.range N, b k ω) ∂μ
      = ∫ ω, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, a j ω * b k ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show (∑ k ∈ Finset.range N, a k ω) * (∑ k ∈ Finset.range N, b k ω)
          = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, a j ω * b k ω
        rw [Finset.sum_mul_sum]
    _ = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, ∫ ω, a j ω * b k ω ∂μ := by
        rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
        exact Finset.sum_congr rfl
          (fun j _ => integral_finsetSum _ (fun k _ => hint j k))
    _ = ∑ j ∈ Finset.range N, ∫ ω, a j ω * b j ω ∂μ := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        exact Finset.sum_eq_single j (fun k hk hkj => hcross j hj k hk (Ne.symm hkj))
          (fun hj' => absurd hj hj')
    _ = ∑ k ∈ Finset.range N, (∫ ω, φ k ω * ψ k ω ∂μ) * ((t (k + 1) : ℝ) - t k) :=
        Finset.sum_congr rfl (fun k _ => hdiag k)

/-- **The discrete Itô isometry** (adapted simple integrands):
`E[(Σₖ φₖ·(B_{t_{k+1}} − B_{t_k}))²] = Σₖ E[φₖ²]·(t_{k+1} − t_k)`. The genuine
Itô isometry — the integrand is *random*. It is the `ψ = φ` diagonal of the
inner-product form `ito_isometry_discrete_bilinear` (`x² = x·x`). -/
theorem ito_isometry_discrete
    (hBmeas : ∀ s, Measurable (B s)) {N : ℕ} {t : ℕ → ℝ≥0} (hmono : Monotone t)
    {φ : ℕ → Ω → ℝ} (hadapt : ∀ n, AdaptedAt B (t n) (φ n))
    (hL2 : ∀ n, MemLp (φ n) 2 μ) :
    ∫ ω, (∑ k ∈ Finset.range N, φ k ω * (B (t (k + 1)) ω - B (t k) ω)) ^ 2 ∂μ =
      ∑ k ∈ Finset.range N, (∫ ω, (φ k ω) ^ 2 ∂μ) * ((t (k + 1) : ℝ) - t k) := by
  simp only [pow_two]
  exact ito_isometry_discrete_bilinear hBmeas hmono hadapt hadapt hL2 hL2

/-- `E[B_s²] = s` (mean zero, variance `s`). -/
theorem integral_eval_sq (hBmeas : ∀ s, Measurable (B s)) (s : ℝ≥0) :
    ∫ ω, (B s ω) ^ 2 ∂μ = (s : ℝ) := by
  rw [← variance_of_integral_eq_zero (hBmeas s).aemeasurable (hB.integral_eval s)]
  show Var[B s; μ] = (s : ℝ)
  rw [(hB.hasLaw_eval s).variance_eq, variance_id_gaussianReal]

/-- **The discrete `∫₀ᵀ B dB` isometry** — the canonical instance, with *no*
remaining hypotheses beyond measurability. Taking the adapted `L²` integrand
`φₖ = B(tₖ)`,

  `E[(Σₖ B(tₖ)·(B_{t_{k+1}} − B_{t_k}))²] = Σₖ t_k·(t_{k+1} − t_k)`,

the Riemann-sum form of the Itô isometry `E[(∫₀ᵀ B dB)²] = ∫₀ᵀ t dt`. -/
theorem ito_isometry_brownian_self
    (hBmeas : ∀ s, Measurable (B s)) {N : ℕ} {t : ℕ → ℝ≥0} (hmono : Monotone t) :
    ∫ ω, (∑ k ∈ Finset.range N, B (t k) ω * (B (t (k + 1)) ω - B (t k) ω)) ^ 2 ∂μ =
      ∑ k ∈ Finset.range N, (t k : ℝ) * ((t (k + 1) : ℝ) - t k) := by
  rw [ito_isometry_discrete (μ := μ) hBmeas hmono (φ := fun k => B (t k))
    (fun n => adaptedAt_eval le_rfl)
    (fun n => (hB.isGaussianProcess.hasGaussianLaw_eval (t n)).memLp_two)]
  exact Finset.sum_congr rfl (fun k _ => by rw [integral_eval_sq hBmeas])

/-! ### Pairing identity for predictable rectangles

The bridge to the *continuous* Itô integral. For an adapted indicator `f`
(`𝓕_s`-measurable) and `g` (`𝓕_{s'}`-measurable),

  `E[f·(B_t − B_s) · g·(B_{t'} − B_{s'})] = E[f·g] · vol((s,t] ∩ (s',t'])`.

This is the adapted generalisation of `WienerIntegralL2.covariance_increment_aux`
(take `f = g = 1`). It is the inner-product identity that makes the assembly of
predictable simple integrands an isometry into `L²(Ω × [0,T])`. The split-at-the-
later-start argument: the pre-overlap part pairs to zero (martingale difference),
and the post-overlap part has both increments *forward* of the later start, so the
adapted coefficient factors out (weak Markov), leaving the deterministic overlap
covariance `integral_two_increment`. -/

/-- An adapted integrand is independent of *any* measurable functional of the
forward increment process `u ↦ B_{t₀+u} − B_{t₀}` (weak Markov,
`IsPreBrownian.indepFun_shift`). Generalises `adapted_indepFun_increment` from a
single forward evaluation to functionals of several future increments. -/
theorem adapted_indepFun_forward
    (hBmeas : ∀ t, Measurable (B t)) {t₀ : ℝ≥0}
    {φ : Ω → ℝ} (hφ : AdaptedAt B t₀ φ)
    {H : (ℝ≥0 → ℝ) → ℝ} (hH : Measurable H) :
    IndepFun φ (fun ω => H (fun u => B (t₀ + u) ω - B t₀ ω)) μ := by
  obtain ⟨g, hg, rfl⟩ := hφ
  exact (hB.indepFun_shift hBmeas t₀).symm.comp hg hH

/-- Two increments sharing a start: `E[(B_t − B_a)(B_{t'} − B_a)] = min t t' − a`
for `a ≤ t`, `a ≤ t'`. Both increments are forward of `a`, so this is the
deterministic covariance; the stochastic content lives in `rect_increment_pairing`. -/
theorem integral_two_increment
    (hBmeas : ∀ s, Measurable (B s)) {a t t' : ℝ≥0} (hat : a ≤ t) (hat' : a ≤ t') :
    ∫ ω, (B t ω - B a ω) * (B t' ω - B a ω) ∂μ = ((min t t' : ℝ≥0) : ℝ) - a := by
  have hincr : ∀ b c : ℝ≥0, MemLp (fun ω => B b ω - B c ω) 2 μ := fun b c =>
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  rcases le_total t t' with htt' | htt'
  · have e2 : ∫ ω, (B t ω - B a ω) * (B t' ω - B t ω) ∂μ = 0 :=
      integral_adapted_mul_increment (μ := μ) hBmeas htt'
        ((adaptedAt_eval le_rfl).sub (adaptedAt_eval hat))
    have hi1 : Integrable (fun ω => (B t ω - B a ω) ^ 2) μ := (hincr t a).integrable_sq
    have hi2 : Integrable (fun ω => (B t ω - B a ω) * (B t' ω - B t ω)) μ :=
      (hincr t a).integrable_mul (hincr t' t)
    have hsum : ∫ ω, (B t ω - B a ω) * (B t' ω - B a ω) ∂μ
        = (∫ ω, (B t ω - B a ω) ^ 2 ∂μ) + ∫ ω, (B t ω - B a ω) * (B t' ω - B t ω) ∂μ := by
      rw [← integral_add hi1 hi2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [hsum, e2, add_zero, integral_increment_sq (μ := μ) hat hBmeas, min_eq_left htt']
  · have e2 : ∫ ω, (B t' ω - B a ω) * (B t ω - B t' ω) ∂μ = 0 :=
      integral_adapted_mul_increment (μ := μ) hBmeas htt'
        ((adaptedAt_eval le_rfl).sub (adaptedAt_eval hat'))
    have hi1 : Integrable (fun ω => (B t' ω - B a ω) ^ 2) μ := (hincr t' a).integrable_sq
    have hi2 : Integrable (fun ω => (B t' ω - B a ω) * (B t ω - B t' ω)) μ :=
      (hincr t' a).integrable_mul (hincr t t')
    have hsum : ∫ ω, (B t ω - B a ω) * (B t' ω - B a ω) ∂μ
        = (∫ ω, (B t' ω - B a ω) ^ 2 ∂μ) + ∫ ω, (B t' ω - B a ω) * (B t ω - B t' ω) ∂μ := by
      rw [← integral_add hi1 hi2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [hsum, e2, add_zero, integral_increment_sq (μ := μ) hat' hBmeas, min_eq_right htt']

/-- Integrability of `h · ΔB · ΔB'` for `h` bounded (the products that appear
when splitting the rectangle pairing). -/
private lemma integrable_bdd_two_increment
    {h : Ω → ℝ} (hhm : Measurable h)
    {C : ℝ} (hhb : ∀ ω, |h ω| ≤ C) (a b c d : ℝ≥0) :
    Integrable (fun ω => h ω * ((B b ω - B a ω) * (B d ω - B c ω))) μ := by
  have hprod : Integrable (fun ω => (B b ω - B a ω) * (B d ω - B c ω)) μ :=
    (hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two).integrable_mul
      (hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two)
  exact hprod.bdd_mul hhm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hhb ω)

/-- Pairing identity, oriented case `s ≤ s'`. -/
private lemma rect_increment_pairing_aux
    (hBmeas : ∀ s, Measurable (B s)) {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : AdaptedAt B s f) (hg : AdaptedAt B s' g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (_hst : s ≤ t) (hst' : s' ≤ t') (hss' : s ≤ s') :
    ∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ =
      (∫ ω, f ω * g ω ∂μ) * max 0 ((min (t : ℝ) t') - max (s : ℝ) s') := by
  have hfm : Measurable f := hf.measurable hBmeas
  have hgm : Measurable g := hg.measurable hBmeas
  have hfg : AdaptedAt B s' (fun ω => f ω * g ω) := (hf.mono hss').mul hg
  have hfgm : Measurable (fun ω => f ω * g ω) := hfm.mul hgm
  have hfgb : ∀ ω, |f ω * g ω| ≤ Cf * Cg := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hfb ω) (hgb ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hfb ω))
  have hmaxss' : max (s : ℝ) s' = (s' : ℝ) := max_eq_right (by exact_mod_cast hss')
  rw [hmaxss']
  by_cases htle : t ≤ s'
  · -- Disjoint intervals: the whole pairing is a forward increment with mean zero.
    have hχ : AdaptedAt B s' (fun ω => f ω * (B t ω - B s ω) * g ω) :=
      ((hf.mono hss').mul ((adaptedAt_eval htle).sub (adaptedAt_eval hss'))).mul hg
    have h0 := integral_adapted_mul_increment (μ := μ) hBmeas hst' hχ
    have hzero : max (0 : ℝ) ((min (t : ℝ) t') - s') = 0 := by
      refine max_eq_left ?_
      have : (min (t : ℝ) t') ≤ (s' : ℝ) :=
        le_trans (min_le_left _ _) (by exact_mod_cast htle)
      linarith
    rw [hzero, mul_zero, ← h0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  · -- Overlapping intervals: split the first increment at the later start `s'`.
    replace htle := not_le.mp htle
    have hT1 : ∫ ω, f ω * g ω * ((B s' ω - B s ω) * (B t' ω - B s' ω)) ∂μ = 0 := by
      have hχ : AdaptedAt B s' (fun ω => f ω * g ω * (B s' ω - B s ω)) :=
        hfg.mul ((adaptedAt_eval le_rfl).sub (adaptedAt_eval hss'))
      have h0 := integral_adapted_mul_increment (μ := μ) hBmeas hst' hχ
      rw [← h0]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    have hindep : IndepFun (fun ω => f ω * g ω)
        (fun ω => (B t ω - B s' ω) * (B t' ω - B s' ω)) μ := by
      have hH : Measurable (fun p : ℝ≥0 → ℝ => p (t - s') * p (t' - s')) := by fun_prop
      have hi := adapted_indepFun_forward (μ := μ) hBmeas hfg hH
      have heq : (fun ω => (fun p : ℝ≥0 → ℝ => p (t - s') * p (t' - s'))
            (fun u => B (s' + u) ω - B s' ω))
          = (fun ω => (B t ω - B s' ω) * (B t' ω - B s' ω)) := by
        funext ω
        simp only [add_tsub_cancel_of_le htle.le, add_tsub_cancel_of_le hst']
      rwa [heq] at hi
    have hXm : Measurable (fun ω => (B t ω - B s' ω) * (B t' ω - B s' ω)) :=
      ((hBmeas t).sub (hBmeas s')).mul ((hBmeas t').sub (hBmeas s'))
    have hT2 : ∫ ω, f ω * g ω * ((B t ω - B s' ω) * (B t' ω - B s' ω)) ∂μ
        = (∫ ω, f ω * g ω ∂μ) * (((min t t' : ℝ≥0) : ℝ) - s') := by
      rw [hindep.integral_fun_mul_eq_mul_integral hfgm.aestronglyMeasurable
            hXm.aestronglyMeasurable,
          integral_two_increment (μ := μ) hBmeas htle.le hst']
    have hsum : ∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ
        = (∫ ω, f ω * g ω * ((B s' ω - B s ω) * (B t' ω - B s' ω)) ∂μ)
          + ∫ ω, f ω * g ω * ((B t ω - B s' ω) * (B t' ω - B s' ω)) ∂μ := by
      rw [← integral_add (integrable_bdd_two_increment hfgm hfgb s s' s' t')
                         (integrable_bdd_two_increment hfgm hfgb s' t s' t')]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    have hcoe : ((min t t' : ℝ≥0) : ℝ) = min (t : ℝ) t' := by
      rcases le_total t t' with h | h
      · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
      · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]
    rw [hsum, hT1, hT2, zero_add, hcoe]
    congr 1
    have h1 : (s' : ℝ) ≤ min (t : ℝ) t' :=
      le_min (by exact_mod_cast htle.le) (by exact_mod_cast hst')
    rw [max_eq_right (by linarith)]

/-- **Pairing identity for predictable rectangles.** For adapted bounded
integrands `f` (`𝓕_s`-measurable) and `g` (`𝓕_{s'}`-measurable),

  `E[f·(B_t − B_s) · g·(B_{t'} − B_{s'})] = E[f·g] · vol((s,t] ∩ (s',t'])`,

with `vol((s,t] ∩ (s',t']) = max 0 (min t t' − max s s')`. The adapted
generalisation of the Wiener covariance identity, and the inner-product core of
the continuous Itô isometry. -/
theorem rect_increment_pairing
    (hBmeas : ∀ s, Measurable (B s)) {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : AdaptedAt B s f) (hg : AdaptedAt B s' g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (hst : s ≤ t) (hst' : s' ≤ t') :
    ∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ =
      (∫ ω, f ω * g ω ∂μ) * max 0 ((min (t : ℝ) t') - max (s : ℝ) s') := by
  rcases le_total s s' with h | h
  · exact rect_increment_pairing_aux hBmeas hf hg hfb hgb hst hst' h
  · rw [show (∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ)
          = ∫ ω, (g ω * (B t' ω - B s' ω)) * (f ω * (B t ω - B s ω)) ∂μ from
        integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring),
        rect_increment_pairing_aux hBmeas hg hf hgb hfb hst' hst h]
    congr 1
    · exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    · rw [min_comm (t' : ℝ) t, max_comm (s' : ℝ) s]

end ItoIsometryAdapted
end MathFin
