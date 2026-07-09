/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralRiemannBridge

/-! # Deterministic drift Riemann-convergence (Girsanov α4 brick b-tail)

The stochastic half of the continuous Doléans exponent — `∑ θ(tₖ)·ΔBₖ → ∫₀ᵀ θ dB` in `L²` — is
`ItoIntegralRiemannBridge.itoIntegralCLM_T_of_bdd_adapted_cont`. This file supplies the **drift
half**: for a bounded continuous real function `g` (applied per-`ω` to `s ↦ θ(s,ω)²`), the
left-endpoint uniform-partition Riemann sums converge to the pathwise Lebesgue integral,

`∑_{k<n} g(tₖ)·(t_{k+1} − tₖ) → ∫ s in (0,T], g s ∂timeMeasure`  (`tₖ = unifPart T n k`).

This is the *deterministic* counterpart of the stochastic bridge — no `B`, no probability — and
is proved by the **same** partition-cell collapse (`cell_collapse`) plus dominated convergence,
now on the finite time measure `timeMeasure.restrict (0,T]`. It is the last ingredient of the
continuous Doléans exponent `−∫θdB − ½∫θ²ds`: the drift term `∑ θ(tₖ)²·Δτ` converges per path.

## Main results

* `tendsto_riemannSum_setIntegral` — left-endpoint Riemann sums → the time-integral of a bounded
  continuous integrand.
* `tendsto_driftSq_riemannSum` — the `θ²` specialization consumed by the continuous Doléans exponent.
-/

@[expose] public section

namespace MathFin

open MeasureTheory Filter Topology NNReal ENNReal MathFin.QuadraticVariationL2
open scoped MeasureTheory NNReal ENNReal
open ItoIntegralL2 ItoIntegralBrownian ItoIntegralRiemannBridge

/-- **Left-endpoint Riemann sums converge to the time-integral.** For a bounded (`|g| ≤ C`)
continuous `g : ℝ≥0 → ℝ`, the uniform-partition left-endpoint Riemann sums
`∑_{k<n} g(tₖ)·(t_{k+1} − tₖ)` (with `tₖ = unifPart T n k`) converge to `∫ s in (0,T], g s`.
Proved by rewriting the sum as the integral of the cell-indicator step function, whose paths
collapse to `g` (`cell_collapse` + continuity), then dominated convergence on the finite
measure `timeMeasure.restrict (0,T]` with the constant bound `C`. -/
theorem tendsto_riemannSum_setIntegral {g : ℝ≥0 → ℝ} (hg : Continuous g) {C : ℝ}
    (hbdd : ∀ s, |g s| ≤ C) (T : ℝ≥0) :
    Tendsto (fun n => ∑ k ∈ Finset.range n,
        g (unifPart T n k) * ((unifPart T n (k + 1) : ℝ) - (unifPart T n k : ℝ)))
      atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ≥0) T, g s ∂timeMeasure)) := by
  classical
  haveI : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hC0 : (0 : ℝ) ≤ C := (abs_nonneg (g 0)).trans (hbdd 0)
  -- the sum equals the integral of the cell-indicator step function
  have hsum : ∀ n, (∑ k ∈ Finset.range n,
        g (unifPart T n k) * ((unifPart T n (k + 1) : ℝ) - (unifPart T n k : ℝ)))
      = ∫ s in Set.Ioc (0 : ℝ≥0) T, (∑ k ∈ Finset.range n,
          (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
            (fun _ => g (unifPart T n k)) s) ∂timeMeasure := by
    intro n
    rw [integral_finsetSum _ (fun k _ => (integrable_const _).indicator measurableSet_Ioc)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : k + 1 ≤ n := Finset.mem_range.mp hk
    rw [setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr (Set.Ioc_subset_Ioc zero_le (unifPart_le_T hk1)),
      setIntegral_const, smul_eq_mul, measureReal_def, timeMeasure_Ioc,
      ENNReal.toReal_ofReal
        (sub_nonneg.mpr (by exact_mod_cast unifPart_mono T n (Nat.le_succ k)))]
    ring
  simp only [hsum]
  -- a.e. convergence of the step functions to `g` on `(0,T]` (cell collapse + continuity)
  have hae : ∀ᵐ s ∂(timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)),
      Tendsto (fun n => ∑ k ∈ Finset.range n,
          (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
            (fun _ => g (unifPart T n k)) s) atTop (𝓝 (g s)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hg.continuousAt ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((T : ℝ) / δ)
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 0 < n := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hn)
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    obtain ⟨k, _, hval, hclose⟩ := cell_collapse T n hn1 s hs (fun j => g (unifPart T n j))
    rw [hval]
    refine hδc ?_
    rw [NNReal.dist_eq]
    have hn_gt : (T : ℝ) / δ < n := lt_of_lt_of_le hN (by exact_mod_cast hnN)
    calc |(unifPart T n k : ℝ) - (s : ℝ)| ≤ (T : ℝ) / n := hclose
      _ < δ := by
          rw [div_lt_iff₀ (by exact_mod_cast hn1 : (0 : ℝ) < (n : ℝ)), mul_comm]
          exact (div_lt_iff₀ hδ).mp hn_gt
  -- uniform bound `|step_n| ≤ C`
  have hbnd : ∀ n, ∀ᵐ s ∂(timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)),
      ‖∑ k ∈ Finset.range n,
          (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
            (fun _ => g (unifPart T n k)) s‖ ≤ C := by
    intro n
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · simp [hn0, hC0]
    · obtain ⟨k, _, hval, _⟩ := cell_collapse T n hn s hs (fun j => g (unifPart T n j))
      rw [Real.norm_eq_abs, hval]
      exact hbdd _
  -- dominated convergence on the finite time measure
  have hmeas : ∀ n, AEStronglyMeasurable (fun s => ∑ k ∈ Finset.range n,
      (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
        (fun _ => g (unifPart T n k)) s) (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) T)) := by
    intro n
    have hrw : (fun s => ∑ k ∈ Finset.range n,
          (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
            (fun _ => g (unifPart T n k)) s)
        = ∑ k ∈ Finset.range n,
          (Set.Ioc (unifPart T n k) (unifPart T n (k + 1))).indicator
            (fun _ => g (unifPart T n k)) := by
      funext s; rw [Finset.sum_apply]
    rw [hrw]
    exact Finset.aestronglyMeasurable_sum _ fun k _ =>
      (stronglyMeasurable_const.indicator measurableSet_Ioc).aestronglyMeasurable
  exact tendsto_integral_of_dominated_convergence (fun _ => C) hmeas
    (integrable_const C) hbnd hae

/-- **The `θ²` drift Riemann-convergence.** For a bounded (`|θ| ≤ C`) integrand `θ` whose every
path `s ↦ θ_s ω` is continuous, the uniform-partition drift sums `∑_{k<n} θ(tₖ)²·(t_{k+1} − tₖ)`
converge to the pathwise energy `∫ s in (0,T], θ_s² ∂timeMeasure` — the drift term of the
continuous Doléans exponent, per path. Specialization of `tendsto_riemannSum_setIntegral` to
`g = θ(·,ω)²` (continuous, bounded by `C²`). -/
theorem tendsto_driftSq_riemannSum {Ω : Type*} {θ : ℝ≥0 → Ω → ℝ}
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C)
    (T : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => ∑ k ∈ Finset.range n,
        (θ (unifPart T n k) ω) ^ 2 * ((unifPart T n (k + 1) : ℝ) - (unifPart T n k : ℝ)))
      atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ≥0) T, (θ s ω) ^ 2 ∂timeMeasure)) := by
  refine tendsto_riemannSum_setIntegral (g := fun s => (θ s ω) ^ 2) (C := C ^ 2)
    ((hcont ω).pow 2) (fun s => ?_) T
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (θ s ω)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hbdd s ω) 2

end MathFin
