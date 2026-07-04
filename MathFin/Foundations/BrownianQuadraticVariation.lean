/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.GaussianMoments

/-!
# Quadratic variation of Brownian motion (L¹ expectation)

For a real-indexed process `B : ℝ → Ω → ℝ` with measurable sections and
Gaussian increments `B t − B s ∼ N(0, t − s)`, the squared-increment sums
along the equipartition of `[0, t]` with `n + 1` subintervals have
expectation `n t / (n + 1)`, which tends to `t` as `n → ∞`.

This is the L¹ form of `[B, B]_t = t` (Saporito Theorem 6.1.1). It does
not require independence of increments or continuity of paths — purely a
marginal moment computation via `variance_id_gaussianReal`.

## Main results

* `BrownianQuadraticVariation` — hypotheses (measurability + Gaussian
  increments) sufficient for the expectation identity.
* `BrownianQuadraticVariation.qv_equals_t` — the squared-increment-sum
  expectations along the equipartition of `[0, t]` tend to `t`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace MathFin

/-- Hypotheses on a real-indexed process `B : ℝ → Ω → ℝ` that suffice for
the quadratic-variation identity at expectation (Saporito Theorem 6.1.1).

`measurable` is included because `Measure.map` is only meaningful for
(a.e.-)measurable functions; together with `gaussian_increments` it yields
the second-moment integral via `integral_map` + `variance_id_gaussianReal`. -/
structure BrownianQuadraticVariation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : ℝ → Ω → ℝ) : Prop where
  measurable : ∀ t : ℝ, Measurable (B t)
  gaussian_increments : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t →
    ∃ v : NNReal, (v : ℝ) = t - s ∧
      Measure.map (fun ω => B t ω - B s ω) μ = gaussianReal 0 v

namespace BrownianQuadraticVariation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ → Ω → ℝ}

/-- The increment `B t − B s` is measurable. -/
theorem measurable_increment (hB : BrownianQuadraticVariation μ B)
    (s t : ℝ) : Measurable (fun ω => B t ω - B s ω) :=
  (hB.measurable t).sub (hB.measurable s)

/-- Integrability of `x²` under any centered real Gaussian. -/
private lemma integrable_sq_gaussianReal_zero (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
  have h_lp : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := memLp_id_gaussianReal 2
  exact h_lp.integrable_sq

/-- For `s ≤ t`, the squared increment `(B t − B s)²` has expectation `t − s`. -/
theorem integral_sq_increment (hB : BrownianQuadraticVariation μ B)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (B t ω - B s ω) ^ 2 ∂μ = t - s := by
  obtain ⟨v, hv, h_map⟩ := hB.gaussian_increments hs hst
  have h_aem : AEMeasurable (fun ω => B t ω - B s ω) μ :=
    (hB.measurable_increment s t).aemeasurable
  have h_map_int : ∫ y : ℝ, y ^ 2 ∂(Measure.map (fun ω => B t ω - B s ω) μ)
      = ∫ ω, (B t ω - B s ω) ^ 2 ∂μ :=
    integral_map h_aem (by fun_prop)
  rw [← h_map_int, h_map, MathFin.integral_sq_gaussianReal, hv]

/-- The squared increment is integrable. -/
theorem integrable_sq_increment (hB : BrownianQuadraticVariation μ B)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => (B t ω - B s ω) ^ 2) μ := by
  obtain ⟨v, _, h_map⟩ := hB.gaussian_increments hs hst
  have h_aem : AEMeasurable (fun ω => B t ω - B s ω) μ :=
    (hB.measurable_increment s t).aemeasurable
  refine (show Integrable ((fun x : ℝ => x ^ 2) ∘ (fun ω => B t ω - B s ω)) μ from
    Integrable.comp_aemeasurable ?_ h_aem)
  rw [h_map]
  exact integrable_sq_gaussianReal_zero _

/-- **Mean of BM increment is zero**: `E[B_t − B_s] = 0` for `s ≤ t`.
Pushforward law is `gaussianReal 0 v` with `v = t − s`; the first moment of
a centred Gaussian is `0`. -/
theorem integral_increment (hB : BrownianQuadraticVariation μ B)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (B t ω - B s ω) ∂μ = 0 := by
  obtain ⟨v, _hv, h_map⟩ := hB.gaussian_increments hs hst
  have h_aem : AEMeasurable (fun ω => B t ω - B s ω) μ :=
    (hB.measurable_increment s t).aemeasurable
  have h_map_int : ∫ y : ℝ, y ∂(Measure.map (fun ω => B t ω - B s ω) μ)
      = ∫ ω, (B t ω - B s ω) ∂μ :=
    integral_map h_aem (by fun_prop)
  rw [← h_map_int, h_map, integral_id_gaussianReal]

/-- Integrability of the BM increment `B_t − B_s` under a finite measure. -/
theorem integrable_increment [IsFiniteMeasure μ]
    (hB : BrownianQuadraticVariation μ B) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => B t ω - B s ω) μ := by
  obtain ⟨v, _, h_map⟩ := hB.gaussian_increments hs hst
  have h_aem : AEMeasurable (fun ω => B t ω - B s ω) μ :=
    (hB.measurable_increment s t).aemeasurable
  refine (show Integrable ((fun x : ℝ => x) ∘ (fun ω => B t ω - B s ω)) μ from
    Integrable.comp_aemeasurable ?_ h_aem)
  rw [h_map]
  exact (memLp_id_gaussianReal 1).integrable (by norm_num)

/-- Endpoint inequality for the equipartition: `k t / (n + 1) ≤ (k + 1) t / (n + 1)`
when `0 ≤ t`. -/
private lemma equipartition_endpoint_le {t : ℝ} (ht : 0 ≤ t) (n k : ℕ) :
    (k : ℝ) * t / (n + 1) ≤ ((k : ℝ) + 1) * t / (n + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_div_iff_of_pos_right hn]
  nlinarith

/-- Left endpoint of the `k`-th equipartition cell is nonnegative when `0 ≤ t`. -/
private lemma equipartition_start_nonneg {t : ℝ} (ht : 0 ≤ t) (n k : ℕ) :
    (0 : ℝ) ≤ (k : ℝ) * t / (n + 1) :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg k) ht) (by positivity)

/-- Expectation of the squared-increment sum along the equipartition:
`∫ Σ_k (B_{(k+1)t/(n+1)} − B_{kt/(n+1)})² ∂μ = n t / (n + 1)`. -/
private lemma integral_sum_sq_equipartition (hB : BrownianQuadraticVariation μ B)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∫ ω, ∑ k ∈ Finset.range n,
        (B (((k : ℝ) + 1) * t / (n + 1)) ω - B ((k : ℝ) * t / (n + 1)) ω) ^ 2 ∂μ
      = n * t / (n + 1) := by
  rw [integral_finsetSum _
    (fun k _ => hB.integrable_sq_increment (equipartition_start_nonneg ht n k)
      (equipartition_endpoint_le ht n k))]
  have hsum : ∀ k ∈ Finset.range n,
      ∫ ω, (B (((k : ℝ) + 1) * t / (n + 1)) ω - B ((k : ℝ) * t / (n + 1)) ω) ^ 2 ∂μ
        = t / (n + 1) := fun k _ => by
    rw [hB.integral_sq_increment (equipartition_start_nonneg ht n k)
      (equipartition_endpoint_le ht n k)]
    field_simp
    ring
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- Real-analysis fact: `n t / (n + 1) → t` as `n → ∞`. -/
private lemma tendsto_nt_div_succ (t : ℝ) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * t / ((n : ℝ) + 1)) atTop (nhds t) := by
  have h_eq : ∀ n : ℕ, (n : ℝ) * t / ((n : ℝ) + 1) = t - t / ((n : ℝ) + 1) := by
    intro n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [show (fun n : ℕ => (n : ℝ) * t / ((n : ℝ) + 1)) =
    (fun n : ℕ => t - t / ((n : ℝ) + 1)) from funext h_eq]
  have h_one_div : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h_t_div : Filter.Tendsto (fun n : ℕ => t / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)) := by
    have h_const_mul : Filter.Tendsto (fun n : ℕ => t * ((1 : ℝ) / ((n : ℝ) + 1))) atTop
        (nhds (t * 0)) := h_one_div.const_mul t
    rw [mul_zero] at h_const_mul
    refine h_const_mul.congr ?_
    intro n
    ring
  have h_sub : Filter.Tendsto (fun n : ℕ => t - t / ((n : ℝ) + 1)) atTop (nhds (t - 0)) :=
    tendsto_const_nhds.sub h_t_div
  rwa [sub_zero] at h_sub

/-- Saporito Theorem 6.1.1, in L¹ form: for a process with measurable sections and
Gaussian increments, the squared-increment sums along the equipartition of `[0, t]`
with `n + 1` subintervals have expectation tending to `t` as `n → ∞`. -/
theorem qv_equals_t (hB : BrownianQuadraticVariation μ B)
    {t : ℝ} (ht : 0 ≤ t) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ ω, (∑ k ∈ Finset.range n,
          (B ((↑k + 1) * t / (n + 1)) ω - B (↑k * t / (n + 1)) ω) ^ 2) ∂μ)
      atTop (nhds t) :=
  (tendsto_nt_div_succ t).congr fun n =>
    (hB.integral_sum_sq_equipartition ht n).symm

end BrownianQuadraticVariation

/-- **Bridge: a (measurable) pre-Brownian motion is a quadratic-variation
process.** Reparametrising a Mathlib `IsPreBrownianReal` process
`B : ℝ≥0 → Ω → ℝ` to the real line via `Real.toNNReal` (`B' t := B t.toNNReal`),
the result satisfies the `BrownianQuadraticVariation` hypotheses, so the whole
variance-swap tower can be driven from a single `IsPreBrownianReal` hypothesis
(plus evaluation-measurability — `IsPreBrownianReal` supplies only a.e.
measurability). The increment law is read off `IsPreBrownianReal.hasLaw_sub` with
arguments `t' s'` (subject `B t' − B s'`, no negation), mirroring
`Foundations.WienerIntegral.hasLaw_increment`. -/
theorem brownianQuadraticVariation_of_isPreBrownianReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) (hBmeas : ∀ u : ℝ≥0, Measurable (B u)) :
    BrownianQuadraticVariation μ (fun t ω => B t.toNNReal ω) where
  measurable t := hBmeas t.toNNReal
  gaussian_increments := by
    intro s t hs hst
    have ht : (0 : ℝ) ≤ t := hs.trans hst
    have hst' : s.toNNReal ≤ t.toNNReal := Real.toNNReal_mono hst
    refine ⟨t.toNNReal - s.toNNReal, ?_, ?_⟩
    · rw [NNReal.coe_sub hst', Real.coe_toNNReal t ht, Real.coe_toNNReal s hs]
    · have hL := hB.hasLaw_sub t.toNNReal s.toNNReal
      have hvar : nndist (t.toNNReal : ℝ) (s.toNNReal : ℝ)
          = (t.toNNReal - s.toNNReal : ℝ≥0) := by
        apply NNReal.coe_injective
        rw [coe_nndist, Real.dist_eq, NNReal.coe_sub hst',
          abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst'))]
      rw [← hvar]
      exact hL.map_eq

end MathFin
