/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Coherent risk axioms derived from concave utility (first principles)

The pre-existing `RiskMeasures.CoherentAxioms` proves the four coherent
risk axioms (translation invariance, monotonicity, positive homogeneity,
subadditivity) directly from the gaussian closed forms of VaR and CVaR.
It treats the axioms as algebraic properties of the gaussian formula.

This file gives a *first-principles* derivation: starting from a concave
(risk-averse) utility function, the induced acceptance set is convex and
monotone, which is exactly the *Artzner-Delbaen-Eber-Heath (1999)*
acceptance-set characterisation of coherent risk measures.

## Setup

* `Ω = ι` finite, with probability vector `p : ι → ℝ`, `p i ≥ 0`,
  `∑ p i = 1` (we don't formally require the unit-sum here, it's not
  needed for the implications below).
* `u : ℝ → ℝ` — utility function.
* `W : ℝ` — baseline wealth.
* `X : ι → ℝ` — a position, valued in each state.
* `acceptableUnderUtility s p u W X := E[u(W + X)] ≥ u(W)`.

## The two key utility ⟹ coherent-axiom implications

* `acceptableUnderUtility_convex` (concavity ⟹ subadditivity of risk):
  if `u` is concave and `X, Y` are both acceptable, then any convex
  combination `αX + (1−α)Y` is acceptable. This is the *risk-aversion ⟹
  diversification ⟹ subadditivity* chain.

* `acceptableUnderUtility_monotone_translation` (monotonicity ⟹
  translation property): if `u` is monotone increasing and `X` is
  acceptable, then `X + c` is acceptable for any `c ≥ 0`. This is the
  "more cash is acceptable" axiom that gives translation invariance to
  the induced risk measure `ρ(X) = inf{m : X + m ∈ A}`.

## What is *not* in this file

The full Artzner-Delbaen-Eber-Heath theorem also identifies acceptance-set
properties with the standard risk-measure form
`ρ(X) = inf{m ∈ ℝ : X + m ∈ A}`. That sup-inf construction is mechanical
once the acceptance set has the right properties; this file establishes
*why* the acceptance set has them, from the utility primitive.

## Why this is "first principles"

The pre-existing axioms are *verified* in the gaussian closed form. This
file derives the *content* of those axioms from a more basic primitive:
the concavity of utility (risk aversion). That's the textbook derivation
in von Neumann-Morgenstern / expected-utility theory.
-/

@[expose] public section

namespace MathFin

/-- A position `X : ι → ℝ` is **acceptable under utility `u` and baseline
`W`** if expected utility with the position dominates the baseline:
`E[u(W + X)] ≥ u(W)`. -/
def acceptableUnderUtility {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (u : ℝ → ℝ) (W : ℝ) (X : ι → ℝ) : Prop :=
  u W ≤ ∑ i ∈ s, p i * u (W + X i)

/-- **Convexity of the acceptance set from concavity of utility**.

If `u` is concave (i.e., midpoint-concave w.r.t. arbitrary convex
combinations) and `X, Y` are both acceptable, then any convex combination
`αX + (1−α)Y` is acceptable.

Proof: pointwise concavity gives `u(W + αX + (1−α)Y) ≥ α u(W+X) + (1−α) u(W+Y)`.
Summing with `p i ≥ 0` gives `E[u(W + αX + (1−α)Y)] ≥ α E[u(W+X)] + (1−α) E[u(W+Y)]`.
Since both `E[u(W+X)] ≥ u(W)` and `E[u(W+Y)] ≥ u(W)`, the convex combination
is `≥ u(W)`.

This is the formal expression: **risk aversion ⟹ subadditivity** of the
induced risk measure. -/
theorem acceptableUnderUtility_convex
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) (u : ℝ → ℝ) (W : ℝ)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (h_concave : ∀ x y : ℝ, ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      α * u x + (1 - α) * u y ≤ u (α * x + (1 - α) * y))
    {X Y : ι → ℝ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hX : acceptableUnderUtility s p u W X)
    (hY : acceptableUnderUtility s p u W Y) :
    acceptableUnderUtility s p u W (fun i ↦ α * X i + (1 - α) * Y i) := by
  unfold acceptableUnderUtility at *
  have h_ptwise : ∀ i ∈ s,
      α * u (W + X i) + (1 - α) * u (W + Y i) ≤
      u (W + (α * X i + (1 - α) * Y i)) := by
    intro i _
    have h := h_concave (W + X i) (W + Y i) α hα hα1
    convert h using 2
    ring
  have h_p_mult : ∀ i ∈ s,
      p i * (α * u (W + X i) + (1 - α) * u (W + Y i)) ≤
      p i * u (W + (α * X i + (1 - α) * Y i)) := by
    intro i hi
    exact mul_le_mul_of_nonneg_left (h_ptwise i hi) (hp_nonneg i hi)
  have h_sum := Finset.sum_le_sum h_p_mult
  have h_LHS :
      ∑ i ∈ s, p i * (α * u (W + X i) + (1 - α) * u (W + Y i)) =
      α * (∑ i ∈ s, p i * u (W + X i)) +
        (1 - α) * (∑ i ∈ s, p i * u (W + Y i)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ ↦ by ring)
  rw [h_LHS] at h_sum
  have h_target : α * u W + (1 - α) * u W = u W := by ring
  have h_bound : α * u W + (1 - α) * u W ≤
                 α * (∑ i ∈ s, p i * u (W + X i)) +
                   (1 - α) * (∑ i ∈ s, p i * u (W + Y i)) := by
    have h1 : α * u W ≤ α * (∑ i ∈ s, p i * u (W + X i)) :=
      mul_le_mul_of_nonneg_left hX hα
    have h2 : (1 - α) * u W ≤ (1 - α) * (∑ i ∈ s, p i * u (W + Y i)) :=
      mul_le_mul_of_nonneg_left hY (by linarith)
    linarith
  linarith

/-- **Translation property of the acceptance set from monotonicity of utility**.

If `u` is monotone increasing and `X` is acceptable, then `X + c` is
acceptable for any `c ≥ 0`.

Proof: pointwise monotonicity gives `u(W + X i + c) ≥ u(W + X i)`. Summing
with `p i ≥ 0` and using `E[u(W + X)] ≥ u(W)` gives `E[u(W + X + c)] ≥ u(W)`.

This is the formal expression: **wealth monotonicity ⟹ translation
property** of the induced risk measure `ρ(X) = inf{m : X + m ∈ A}`. -/
theorem acceptableUnderUtility_monotone_translation
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) (u : ℝ → ℝ) (W : ℝ)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (h_mono : Monotone u)
    {X : ι → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hX : acceptableUnderUtility s p u W X) :
    acceptableUnderUtility s p u W (fun i ↦ X i + c) := by
  unfold acceptableUnderUtility at *
  have h_ptwise : ∀ i ∈ s, u (W + X i) ≤ u (W + (X i + c)) := by
    intro i _
    apply h_mono
    linarith
  have h_p_mult : ∀ i ∈ s, p i * u (W + X i) ≤ p i * u (W + (X i + c)) := by
    intro i hi
    exact mul_le_mul_of_nonneg_left (h_ptwise i hi) (hp_nonneg i hi)
  have h_sum := Finset.sum_le_sum h_p_mult
  linarith

/-- **Constant 0 is acceptable**: doing nothing doesn't reduce expected
utility below baseline. -/
theorem acceptableUnderUtility_zero
    {ι : Type*} (s : Finset ι) (p : ι → ℝ) (u : ℝ → ℝ) (W : ℝ)
    (h_p_sum : ∑ i ∈ s, p i = 1) :
    acceptableUnderUtility s p u W (fun _ ↦ 0) := by
  unfold acceptableUnderUtility
  simp only [add_zero]
  rw [← Finset.sum_mul, h_p_sum, one_mul]

end MathFin
