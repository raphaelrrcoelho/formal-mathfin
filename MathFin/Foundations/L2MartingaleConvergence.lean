/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.DoobLpMaximalInequality
public import BrownianMotion.StochasticIntegral.UniformIntegrable

/-!
# L²-bounded discrete martingales converge in L²

Mathlib's martingale convergence theory gives, for an L¹-bounded
submartingale, almost-everywhere convergence to `ℱ.limitProcess f μ`
(`Submartingale.ae_tendsto_limitProcess`), membership of the limit in `Lᵖ`
under an `Lᵖ` bound (`Submartingale.memLp_limitProcess`), and **L¹**-norm
convergence under uniform integrability
(`Submartingale.tendsto_eLpNorm_one_limitProcess`). It does **not** contain
the classical L² statement: an L²-bounded martingale converges in L²-norm.

This file proves it, and the route is the point: the uniform-integrability
input is manufactured from this library's own **Doob L² maximal inequality**
(`MeasureTheory.Martingale.eLpNorm_norm_runMax_le`,
`Foundations/DoobLpMaximalInequality.lean`):

1. the running maxima `ω ↦ max_{k ≤ n} ‖f k ω‖` are uniformly L²-bounded by
   `2R` (Doob at `p = 2`);
2. by monotone convergence the all-time envelope `G ω = ⨆ n ‖f n ω‖ₑ` is
   square-integrable, and it dominates every `f n`;
3. a single L² dominator makes the family uniformly integrable in L²
   (Chebyshev shrinks the tail sets `{C ≤ ‖f n‖}` uniformly; absolute
   continuity of the indicator seminorm, `MemLp.eLpNorm_indicator_le`,
   converts small measure into small L² mass);
4. Vitali (`tendsto_Lp_finite_of_tendsto_ae`) upgrades the a.e. convergence
   to L²-norm convergence.

## Main result

* `martingale_ae_tendsto_and_eLpNorm_two_tendsto` — for a martingale `f`
  with `eLpNorm (f n) 2 μ ≤ R` for all `n`: a.e. convergence to
  `ℱ.limitProcess f μ` **and** `eLpNorm (f n − ℱ.limitProcess f μ) 2 μ → 0`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace L2MartingaleConvergence

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {R : ℝ≥0}

/-- Partial running maximum of the enorms, `H n ω = max_{k ≤ n} ‖f k ω‖ₑ`. -/
private noncomputable def H (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (Finset.range (n + 1)).sup fun k ↦ ‖f k ω‖ₑ

/-- All-time envelope `G ω = ⨆ n ‖f n ω‖ₑ`. -/
private noncomputable def G (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n, ‖f n ω‖ₑ

private lemma H_mono (ω : Ω) : Monotone fun n ↦ H f n ω := fun _ _ hab ↦
  Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right hab 1))

private lemma G_eq_iSup_H (ω : Ω) : G f ω = ⨆ n, H f n ω := by
  refine le_antisymm (iSup_le fun n ↦ le_iSup_of_le n ?_) (iSup_le fun n ↦ ?_)
  · show ‖f n ω‖ₑ ≤ (Finset.range (n + 1)).sup fun k ↦ ‖f k ω‖ₑ
    exact Finset.le_sup (f := fun k ↦ ‖f k ω‖ₑ) (Finset.self_mem_range_succ n)
  · show ((Finset.range (n + 1)).sup fun k ↦ ‖f k ω‖ₑ) ≤ G f ω
    exact Finset.sup_le fun k _ ↦ le_iSup (fun m ↦ ‖f m ω‖ₑ) k

private lemma measurable_H (hmeas : ∀ n, Measurable (f n)) (n : ℕ) :
    Measurable (H f n) := by
  show Measurable fun ω ↦ (Finset.range (n + 1)).sup fun k ↦ ‖f k ω‖ₑ
  simp only [Finset.sup_eq_iSup]
  exact .iSup fun k ↦ .iSup fun _ ↦ (hmeas k).enorm

private lemma measurable_G (hmeas : ∀ n, Measurable (f n)) : Measurable (G f) :=
  .iSup fun n ↦ (hmeas n).enorm

/-- `∫⁻ ‖g‖ₑ² = (eLpNorm g 2 μ)²`: the seminorm with the rpow peeled off. -/
private lemma lintegral_enorm_sq (g : Ω → ℝ) :
    ∫⁻ ω, ‖g ω‖ₑ ^ (2 : ℕ) ∂μ = eLpNorm g 2 μ ^ (2 : ℕ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num),
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  rw [show (1 / (2 : ℝ≥0∞).toReal * ((2 : ℕ) : ℝ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
  refine lintegral_congr fun ω ↦ ?_
  rw [← ENNReal.rpow_natCast]
  norm_num

/-- The enorm running maximum is the enorm of the real running maximum, so the
Doob bound on the latter transfers. -/
private lemma H_eq_enorm_runMax (n : ℕ) (ω : Ω) :
    H f n ω = ‖(Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ ‖f k ω‖)‖ₑ := by
  show ((Finset.range (n + 1)).sup fun k ↦ ‖f k ω‖ₑ)
    = ‖(Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k ↦ ‖f k ω‖)‖ₑ
  refine le_antisymm (Finset.sup_le fun k hk ↦ ?_) ?_
  · rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      ((Finset.le_sup' (fun m ↦ ‖f m ω‖) hk).trans (Real.le_norm_self _))
  · obtain ⟨k₀, hk₀, heq⟩ := Finset.exists_mem_eq_sup'
      Finset.nonempty_range_add_one (fun k ↦ ‖f k ω‖)
    rw [heq, show ‖(‖f k₀ ω‖)‖ₑ = ‖f k₀ ω‖ₑ from by
      rw [← ofReal_norm, norm_norm, ofReal_norm]]
    exact Finset.le_sup (f := fun k ↦ ‖f k ω‖ₑ) hk₀

/-- Squared partial maxima have uniformly bounded lintegral: this is the
library's Doob L² maximal inequality (`eLpNorm_norm_runMax_le` at `p = 2`). -/
private lemma lintegral_H_sq_le [IsFiniteMeasure μ]
    (hf : Martingale f ℱ μ) (hbdd : ∀ n, eLpNorm (f n) 2 μ ≤ R) (n : ℕ) :
    ∫⁻ ω, H f n ω ^ (2 : ℕ) ∂μ ≤ ((2 : ℝ≥0∞) * R) ^ (2 : ℕ) := by
  have h_doob : eLpNorm (fun ω ↦
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ ‖f k ω‖) 2 μ
      ≤ (2 : ℝ≥0∞) * R := by
    have h := hf.eLpNorm_norm_runMax_le one_lt_two n
    rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by simp] at h
    refine h.trans ?_
    rw [show ((2 : ℝ) / (2 - 1)) = 2 by norm_num,
      show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by simp]
    exact mul_le_mul_right (hbdd n) _
  calc ∫⁻ ω, H f n ω ^ (2 : ℕ) ∂μ
      = eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k ↦ ‖f k ω‖) 2 μ ^ (2 : ℕ) := by
        rw [← lintegral_enorm_sq]
        exact lintegral_congr fun ω ↦ by rw [H_eq_enorm_runMax]
    _ ≤ ((2 : ℝ≥0∞) * R) ^ (2 : ℕ) := pow_le_pow_left' h_doob 2

/-- Monotone convergence: the envelope `G` is square-integrable, with the same
Doob bound. -/
private lemma lintegral_G_sq_le [IsFiniteMeasure μ]
    (hf : Martingale f ℱ μ) (hmeas : ∀ n, Measurable (f n))
    (hbdd : ∀ n, eLpNorm (f n) 2 μ ≤ R) :
    ∫⁻ ω, G f ω ^ (2 : ℕ) ∂μ ≤ ((2 : ℝ≥0∞) * R) ^ (2 : ℕ) := by
  have h_ptwise : ∀ ω, G f ω ^ (2 : ℕ) = ⨆ n, H f n ω ^ (2 : ℕ) := by
    intro ω
    have h2 : Tendsto (fun n ↦ H f n ω ^ (2 : ℕ)) atTop
        (𝓝 ((⨆ n, H f n ω) ^ (2 : ℕ))) :=
      ((ENNReal.continuous_pow 2).tendsto _).comp (tendsto_atTop_iSup (H_mono ω))
    have h3 : Tendsto (fun n ↦ H f n ω ^ (2 : ℕ)) atTop
        (𝓝 (⨆ n, H f n ω ^ (2 : ℕ))) :=
      tendsto_atTop_iSup fun a b hab ↦ pow_le_pow_left' (H_mono ω hab) 2
    rw [G_eq_iSup_H]
    exact tendsto_nhds_unique h2 h3
  calc ∫⁻ ω, G f ω ^ (2 : ℕ) ∂μ
      = ∫⁻ ω, ⨆ n, H f n ω ^ (2 : ℕ) ∂μ := lintegral_congr h_ptwise
    _ = ⨆ n, ∫⁻ ω, H f n ω ^ (2 : ℕ) ∂μ :=
        lintegral_iSup (fun n ↦ (measurable_H hmeas n).pow_const 2)
          fun a b hab ω ↦ pow_le_pow_left' (H_mono ω hab) 2
    _ ≤ ((2 : ℝ≥0∞) * R) ^ (2 : ℕ) := iSup_le fun n ↦ lintegral_H_sq_le hf hbdd n

/-- The real-valued envelope: in `L²` and dominating all `f n`. -/
private lemma exists_dominator [IsFiniteMeasure μ]
    (hf : Martingale f ℱ μ) (hmeas : ∀ n, Measurable (f n))
    (hbdd : ∀ n, eLpNorm (f n) 2 μ ≤ R) :
    ∃ g : Ω → ℝ, Measurable g ∧ MemLp g 2 μ ∧ ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ g ω := by
  have hG_sq_ne : ∫⁻ ω, G f ω ^ (2 : ℕ) ∂μ ≠ ∞ :=
    (lt_of_le_of_lt (lintegral_G_sq_le hf hmeas hbdd) (by finiteness)).ne
  have hG_fin : ∀ᵐ ω ∂μ, G f ω ^ (2 : ℕ) < ∞ :=
    ae_lt_top ((measurable_G hmeas).pow_const 2) hG_sq_ne
  have h_ne : ∀ᵐ ω ∂μ, G f ω ≠ ∞ := by
    filter_upwards [hG_fin] with ω hω
    exact fun hcon ↦ by simp [hcon] at hω
  refine ⟨fun ω ↦ (G f ω).toReal, (measurable_G hmeas).ennreal_toReal, ?_, ?_⟩
  · refine ⟨(measurable_G hmeas).ennreal_toReal.aestronglyMeasurable, ?_⟩
    have h_eq : ∫⁻ ω, ‖(G f ω).toReal‖ₑ ^ (2 : ℕ) ∂μ = ∫⁻ ω, G f ω ^ (2 : ℕ) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [h_ne] with ω hω
      rw [← ofReal_norm, Real.norm_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hω]
    have h_lt : eLpNorm (fun ω ↦ (G f ω).toReal) 2 μ ^ (2 : ℕ) < ∞ := by
      rw [← lintegral_enorm_sq, h_eq]
      exact lt_of_le_of_lt (lintegral_G_sq_le hf hmeas hbdd) (by finiteness)
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon] at h_lt
    simp at h_lt
  · intro n
    filter_upwards [h_ne] with ω hω
    have h2 := ENNReal.toReal_mono hω (le_iSup (fun m ↦ ‖f m ω‖ₑ) n)
    rwa [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] at h2

/-- A single L² dominator makes the family uniformly integrable in L² — this is
Degenne's `uniformIntegrable_of_dominated_singleton` projected to `UnifIntegrable`
via `.unifIntegrable`, superseding a hand-rolled Chebyshev tail argument. -/
private lemma unifIntegrable_of_dominator [IsFiniteMeasure μ]
    (hmeas : ∀ n, Measurable (f n)) {g : Ω → ℝ} (_hgm : Measurable g)
    (hg : MemLp g 2 μ) (hdom : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ g ω) :
    UnifIntegrable f 2 μ :=
  (uniformIntegrable_of_dominated_singleton one_le_two (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    hg (fun n ↦ (hmeas n).aestronglyMeasurable) hdom).unifIntegrable

end L2MartingaleConvergence

open L2MartingaleConvergence in
/-- **L² martingale convergence** (Saporito, Theorem 2.5.1, L² form). A
martingale bounded in L² converges to `ℱ.limitProcess f μ` almost everywhere
**and** in L²-norm. The a.e. half is Mathlib's upcrossing-based convergence;
the L² half is new: uniform integrability in L² is produced by this library's
Doob L² maximal inequality (envelope dominator + Chebyshev), and Vitali's
convergence theorem closes the argument. -/
theorem martingale_ae_tendsto_and_eLpNorm_two_tendsto
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {R : ℝ≥0}
    (hf : Martingale f ℱ μ) (hbdd : ∀ n, eLpNorm (f n) 2 μ ≤ R) :
    (∀ᵐ ω ∂μ, Filter.Tendsto (fun n ↦ f n ω) Filter.atTop
      (nhds (ℱ.limitProcess f μ ω))) ∧
    Filter.Tendsto (fun n ↦ eLpNorm (f n - ℱ.limitProcess f μ) 2 μ)
      Filter.atTop (nhds 0) := by
  have hmeas : ∀ n, Measurable (f n) := fun n ↦
    ((hf.stronglyMeasurable n).mono (ℱ.le n)).measurable
  -- L¹ bound from the L² bound on a finite measure
  have hbdd1 : ∃ R₁ : ℝ≥0, ∀ n, eLpNorm (f n) 1 μ ≤ (R₁ : ℝ≥0∞) := by
    set c : ℝ≥0∞ := μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
      with hc_def
    have hc_ne : c ≠ ∞ := by
      rw [hc_def]
      exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ _)).ne
    refine ⟨((R : ℝ≥0∞) * c).toNNReal, fun n ↦ ?_⟩
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (p := 1) (q := 2)
      one_le_two (hmeas n).aestronglyMeasurable
    rw [ENNReal.coe_toNNReal (by finiteness)]
    exact h.trans (mul_le_mul_left (hbdd n) _)
  obtain ⟨R₁, hR₁⟩ := hbdd1
  have h_ae := hf.submartingale.ae_tendsto_limitProcess hR₁
  have h_memLp : MemLp (ℱ.limitProcess f μ) 2 μ :=
    hf.submartingale.memLp_limitProcess hbdd
  obtain ⟨g, hgm, hg, hdom⟩ := exists_dominator hf hmeas hbdd
  exact ⟨h_ae, tendsto_Lp_finite_of_tendsto_ae one_le_two (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun n ↦ (hmeas n).aestronglyMeasurable) h_memLp
    (unifIntegrable_of_dominator hmeas hgm hg hdom) h_ae⟩

end MathFin
