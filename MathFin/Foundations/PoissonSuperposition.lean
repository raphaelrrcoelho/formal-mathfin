/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Superposition of Poisson streams: the Poisson convolution identity

Mathlib has the Poisson distribution (`poissonMeasure : ℝ≥0 → Measure ℕ`) but
**no convolution identity** for it: there is no lemma computing
`poissonMeasure a ∗ poissonMeasure b`, and consequently no proof that the sum
of two independent Poisson counts is Poisson at the summed rate — the heart of
the superposition theorem for Poisson processes (Saporito, Theorem 3.3.9).

This file proves both, from the point masses up.

The analytic heart is elementary: `poissonMeasure` is a weighted sum of Dirac
masses, so the convolution evaluated at the singleton `{n}` is the Cauchy
product `∑_{j≤n} e^{−a} aʲ/j! · e^{−b} bⁿ⁻ʲ/(n−j)!`, which the binomial
theorem collapses to `e^{−(a+b)} (a+b)ⁿ/n!`. No characteristic functions, no
generating functions: just `add_pow` and `n.choose j · j! · (n−j)! = n!`.

## Main results

* `PoissonSuperposition.poissonMeasure_conv_poissonMeasure` —
  `poissonMeasure a ∗ poissonMeasure b = poissonMeasure (a + b)`.
* `PoissonSuperposition.indepFun_map_add_poissonMeasure` — if `X, Y` are
  independent with `Poisson(a)`, `Poisson(b)` laws, then `X + Y` has
  `Poisson(a+b)` law (the superposition theorem at increment level).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat

namespace PoissonSuperposition

/-! ### The real-level Cauchy-product identity -/

/-- **Binomial collapse of the Poisson Cauchy product.** For every `n`,
`∑_{j=0}^{n} e^{−a} aʲ/j! · e^{−b} bⁿ⁻ʲ/(n−j)! = e^{−(a+b)} (a+b)ⁿ/n!`. -/
private lemma sum_pmf_mul_pmf (a b : ℝ≥0) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
        rexp (-(a : ℝ)) * (a : ℝ) ^ j / j ! *
          (rexp (-(b : ℝ)) * (b : ℝ) ^ (n - j) / (n - j)!)
      = rexp (-((a : ℝ) + b)) * ((a : ℝ) + b) ^ n / n ! := by
  rw [add_pow, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hfact : ((n.choose j : ℝ)) * (j ! : ℝ) * ((n - j)! : ℝ) = (n ! : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ)
      (Nat.choose_mul_factorial_mul_factorial hjn)
  have hj0 : (j ! : ℝ) ≠ 0 := by positivity
  have hnj0 : ((n - j)! : ℝ) ≠ 0 := by positivity
  have hn0 : (n ! : ℝ) ≠ 0 := by positivity
  rw [neg_add, Real.exp_add]
  field_simp
  linear_combination -((a : ℝ) ^ j * (b : ℝ) ^ (n - j)) * hfact

/-! ### The measure-level convolution identity -/

/-- Inner Dirac sum: integrating the indicator of `{n}` shifted by `j`
against the Poisson weights picks out exactly the `n − j` term (and nothing
when `j > n`). -/
private lemma tsum_pmf_indicator (b : ℝ≥0) (n j : ℕ) :
    (∑' k, ENNReal.ofReal (rexp (-(b : ℝ)) * (b : ℝ) ^ k / k !) *
        Set.indicator {n} (1 : ℕ → ℝ≥0∞) (j + k))
      = if j ≤ n then
          ENNReal.ofReal (rexp (-(b : ℝ)) * (b : ℝ) ^ (n - j) / (n - j)!)
        else 0 := by
  rcases le_or_gt j n with hjn | hjn
  · rw [if_pos hjn, tsum_eq_single (n - j) ?_]
    · rw [Set.indicator_of_mem (by simp [Nat.add_sub_cancel' hjn]),
        Pi.one_apply, mul_one]
    · intro k hk
      rw [Set.indicator_of_notMem (by simp only [Set.mem_singleton_iff]; omega),
        mul_zero]
  · rw [if_neg (not_le.mpr hjn)]
    convert tsum_zero with k
    rw [Set.indicator_of_notMem (by simp only [Set.mem_singleton_iff]; omega),
      mul_zero]

/-- **Poisson convolution identity.** For all rates `a b : ℝ≥0`,
`poissonMeasure a ∗ poissonMeasure b = poissonMeasure (a + b)`.

Absent from Mathlib; proved by evaluating both sides on singletons and
collapsing the Cauchy product with the binomial theorem. -/
theorem poissonMeasure_conv_poissonMeasure (a b : ℝ≥0) :
    poissonMeasure a ∗ poissonMeasure b = poissonMeasure (a + b) := by
  refine Measure.ext_of_singleton fun n => ?_
  have h_ind : Measurable (Set.indicator {n} (1 : ℕ → ℝ≥0∞)) :=
    measurable_const.indicator (measurableSet_singleton n)
  rw [poissonMeasure_singleton, ← lintegral_indicator_one (measurableSet_singleton n),
    Measure.lintegral_conv h_ind,
    show poissonMeasure a = Measure.sum (fun j =>
      ENNReal.ofReal (rexp (-(a : ℝ)) * (a : ℝ) ^ j / j !) • Measure.dirac j) from rfl,
    show poissonMeasure b = Measure.sum (fun k =>
      ENNReal.ofReal (rexp (-(b : ℝ)) * (b : ℝ) ^ k / k !) • Measure.dirac k) from rfl]
  simp_rw [lintegral_sum_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul, tsum_pmf_indicator]
  have h_supp : ∀ j ∉ Finset.range (n + 1),
      ENNReal.ofReal (rexp (-(a : ℝ)) * (a : ℝ) ^ j / j !) *
        (if j ≤ n then
            ENNReal.ofReal (rexp (-(b : ℝ)) * (b : ℝ) ^ (n - j) / (n - j)!)
          else 0) = 0 := by
    intro j hj
    rw [if_neg (by have := Finset.mem_range.not.mp hj; omega), mul_zero]
  rw [tsum_eq_sum h_supp,
    Finset.sum_congr rfl fun j hj => by
      rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)),
        ← ENNReal.ofReal_mul (by positivity)],
    ← ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity,
    sum_pmf_mul_pmf]
  norm_num [NNReal.coe_add]

/-! ### Superposition at increment level -/

/-- **Superposition theorem (increment form, Saporito Theorem 3.3.9).** If
`X` and `Y` are independent `ℕ`-valued random counts with `Poisson(a)` and
`Poisson(b)` laws, their sum is `Poisson(a + b)`. No measurability hypotheses
are needed: a nonzero pushforward forces a.e.-measurability. -/
theorem indepFun_map_add_poissonMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {a b : ℝ≥0} {X Y : Ω → ℕ} (hXY : IndepFun X Y μ)
    (hX : μ.map X = poissonMeasure a) (hY : μ.map Y = poissonMeasure b) :
    μ.map (fun ω => X ω + Y ω) = poissonMeasure (a + b) := by
  rw [show (fun ω => X ω + Y ω) = X + Y from rfl,
    hXY.map_add_eq_map_conv_map₀', hX, hY, poissonMeasure_conv_poissonMeasure]
  · apply AEMeasurable.of_map_ne_zero
    simp [hX, NeZero.ne]
  · apply AEMeasurable.of_map_ne_zero
    simp [hY, NeZero.ne]
  · rw [hX]; infer_instance
  · rw [hY]; infer_instance

end PoissonSuperposition

end MathFin
