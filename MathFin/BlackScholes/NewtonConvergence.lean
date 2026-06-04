/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import MathFin.BlackScholes.ImpliedVolatility

/-!
# Newton–Raphson: local quadratic convergence

`ImpliedVolatility.lean` records the Newton step `σ ↦ σ − f(σ)/f'(σ)` and its
fixed-point-at-root identity. This file proves the genuine numerical-analysis
content: **local quadratic convergence**.

The hypotheses are the classical ones, phrased through the repo's
`HasDerivAt` idiom (no `ContDiff`/`iteratedDeriv` machinery): on a closed
interval `I = [r − δ, r + δ]` around a root `r`,

* `f` has pointwise derivative `f'` on `I`,
* `f'` is `L`-Lipschitz on `I` (the honest substitute for a second-derivative
  bound — `C²` implies it, but Lipschitz is exactly what the proof consumes),
* `|f'| ≥ m > 0` on `I` (the root is simple).

**One step is quadratic** (`newtonStep_quadratic_error`):

  `|x⁺ − r| ≤ (L/m)·(x − r)²`,   `x⁺ := newtonStep f f' x`.

The proof shows *why* Newton is quadratic: the next error is the Taylor
remainder of `f` at `x`, evaluated at the root, divided by `f' x`. The
remainder is controlled by one mean-value bound applied to the
**linearization-subtracted** auxiliary `g(w) = f(w) − f'(x)·w` on the segment
`[r, x]` — `g` has derivative `f'(w) − f'(x)`, which the Lipschitz hypothesis
bounds by `L·|x − r|`; no second derivative is ever mentioned.

**Iterating converges** (`newtonSeq_tendsto_root`): inside the basin
`|x₀ − r| ≤ δ` with `L·δ ≤ m/2`, the quadratic bound gives the invariant
`|xₙ₊₁ − r| ≤ ½|xₙ − r|`, hence `|xₙ − r| ≤ (½)ⁿ·|x₀ − r| → 0`
(`newtonSeq_error_le_geometric`), and `xₙ → r`.

In the implied-volatility application, `f(σ) = bsV(σ) − C_obs` has
`f' = vega > 0` (`bsV_vega_pos`), so `m` is a positive vega lower bound on the
bracketing interval and the simple-root hypothesis is automatic.

## Results

* `newtonSeq`: the Newton iterates.
* `newtonStep_quadratic_error`: one-step quadratic error bound `(L/m)·e²`.
* `newtonSeq_error_le_geometric`: geometric error decay in the basin.
* `newtonSeq_tendsto_root`: convergence `xₙ → r`.
-/

namespace MathFin

open Filter Topology

/-- The **Newton–Raphson iterates**: `x₀`, then `x_{n+1} = newtonStep f f' xₙ`. -/
noncomputable def newtonSeq (f f' : ℝ → ℝ) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => newtonStep f f' (newtonSeq f f' x₀ n)

variable {f f' : ℝ → ℝ} {r δ m L x₀ : ℝ}

/-- **One Newton step is quadratic**: if `r` is a root, `f'` is the pointwise
derivative of `f` on `I = [r − δ, r + δ]`, `f'` is `L`-Lipschitz on `I`, and
`|f'| ≥ m > 0` on `I`, then for `x ∈ I`

  `|newtonStep f f' x − r| ≤ (L/m) · (x − r)²`.

The next error is the Taylor remainder over `f' x`: the mean-value bound for
the linearization-subtracted auxiliary `w ↦ f w − f' x · w` on the segment
`[r, x]` controls the remainder by `L·|x − r|²`, and `|f' x| ≥ m` divides it
out. -/
theorem newtonStep_quadratic_error
    (hroot : f r = 0) (hm0 : 0 < m) (hL : 0 ≤ L)
    (hd : ∀ y ∈ Set.Icc (r - δ) (r + δ), HasDerivAt f (f' y) y)
    (hlip : ∀ y ∈ Set.Icc (r - δ) (r + δ), ∀ w ∈ Set.Icc (r - δ) (r + δ),
      |f' y - f' w| ≤ L * |y - w|)
    (hm : ∀ y ∈ Set.Icc (r - δ) (r + δ), m ≤ |f' y|)
    {x : ℝ} (hx : x ∈ Set.Icc (r - δ) (r + δ)) :
    |newtonStep f f' x - r| ≤ L / m * (x - r) ^ 2 := by
  have hδ : 0 ≤ δ := by
    have h1 := hx.1; have h2 := hx.2; linarith
  have hr : r ∈ Set.Icc (r - δ) (r + δ) := ⟨by linarith, by linarith⟩
  have hf'x_pos : 0 < |f' x| := lt_of_lt_of_le hm0 (hm x hx)
  have hf'x_ne : f' x ≠ 0 := abs_pos.1 hf'x_pos
  -- mean-value bound for the linearization-subtracted auxiliary on the segment
  have hsub : Set.uIcc r x ⊆ Set.Icc (r - δ) (r + δ) := Set.uIcc_subset_Icc hr hx
  have hg : ∀ y ∈ Set.uIcc r x,
      HasDerivWithinAt (fun w => f w - f' x * w) (f' y - f' x) (Set.uIcc r x) y :=
    fun y hy => ((hd y (hsub hy)).sub
      (by simpa using (hasDerivAt_id y).const_mul (f' x))).hasDerivWithinAt
  have hbound : ∀ y ∈ Set.uIcc r x, ‖f' y - f' x‖ ≤ L * |x - r| := by
    intro y hy
    rw [Real.norm_eq_abs]
    have hseg : |y - x| ≤ |x - r| := by
      rcases Set.mem_uIcc.1 hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonpos (by linarith : y - x ≤ 0),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ x - r)]
        linarith
      · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y - x),
          abs_of_nonpos (by linarith : x - r ≤ 0)]
        linarith
    calc |f' y - f' x| ≤ L * |y - x| := hlip y (hsub hy) x hx
      _ ≤ L * |x - r| := mul_le_mul_of_nonneg_left hseg hL
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound
    (convex_uIcc r x) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  -- the Taylor remainder at the root, in the shape the Newton step produces
  have h_num : |f' x * (x - r) - f x| ≤ L * (x - r) ^ 2 := by
    have h_eq : f' x * (x - r) - f x = -(f x - f' x * x - (f r - f' x * r)) := by
      rw [hroot]; ring
    calc |f' x * (x - r) - f x|
        = |f x - f' x * x - (f r - f' x * r)| := by rw [h_eq, abs_neg]
      _ ≤ L * |x - r| * |x - r| := hmvt
      _ = L * (x - r) ^ 2 := by rw [mul_assoc, abs_mul_abs_self, ← pow_two]
  -- error–times–derivative identity: (x⁺ − r)·f' x = f' x·(x − r) − f x
  have h_prod : (newtonStep f f' x - r) * f' x = f' x * (x - r) - f x := by
    unfold newtonStep
    field_simp
    ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
  calc |newtonStep f f' x - r| * m
      ≤ |newtonStep f f' x - r| * |f' x| :=
        mul_le_mul_of_nonneg_left (hm x hx) (abs_nonneg _)
    _ = |(newtonStep f f' x - r) * f' x| := (abs_mul _ _).symm
    _ = |f' x * (x - r) - f x| := by rw [h_prod]
    _ ≤ L * (x - r) ^ 2 := h_num

/-- **Geometric error decay in the Newton basin**: if additionally
`|x₀ − r| ≤ δ` and `L·δ ≤ m/2`, then every iterate stays in the interval and

  `|xₙ − r| ≤ (½)ⁿ · |x₀ − r|`.

The quadratic bound `(L/m)·e²` turns into the halving `e/2` as soon as
`e ≤ δ ≤ m/(2L)`, and halving preserves the basin — the induction invariant. -/
theorem newtonSeq_error_le_geometric
    (hroot : f r = 0) (hm0 : 0 < m) (hL : 0 ≤ L)
    (hd : ∀ y ∈ Set.Icc (r - δ) (r + δ), HasDerivAt f (f' y) y)
    (hlip : ∀ y ∈ Set.Icc (r - δ) (r + δ), ∀ w ∈ Set.Icc (r - δ) (r + δ),
      |f' y - f' w| ≤ L * |y - w|)
    (hm : ∀ y ∈ Set.Icc (r - δ) (r + δ), m ≤ |f' y|)
    (hx₀ : |x₀ - r| ≤ δ) (hbasin : L * δ ≤ m / 2) :
    ∀ n, |newtonSeq f f' x₀ n - r| ≤ (1 / 2) ^ n * |x₀ - r| := by
  intro n
  induction n with
  | zero => simp [newtonSeq]
  | succ n ih =>
    have h_en_le_δ : |newtonSeq f f' x₀ n - r| ≤ δ := by
      refine ih.trans (le_trans ?_ hx₀)
      calc (1 / 2 : ℝ) ^ n * |x₀ - r|
          ≤ 1 * |x₀ - r| :=
            mul_le_mul_of_nonneg_right
              (pow_le_one₀ (by norm_num) (by norm_num)) (abs_nonneg _)
        _ = |x₀ - r| := one_mul _
    have h_mem : newtonSeq f f' x₀ n ∈ Set.Icc (r - δ) (r + δ) := by
      have h := abs_le.1 h_en_le_δ
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have h_step := newtonStep_quadratic_error hroot hm0 hL hd hlip hm h_mem
    have h_coeff : L / m * δ ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
      linarith
    have h_half : L / m * (newtonSeq f f' x₀ n - r) ^ 2
        ≤ 1 / 2 * |newtonSeq f f' x₀ n - r| := by
      calc L / m * (newtonSeq f f' x₀ n - r) ^ 2
          = L / m * |newtonSeq f f' x₀ n - r| * |newtonSeq f f' x₀ n - r| := by
            rw [mul_assoc, abs_mul_abs_self, ← pow_two]
        _ ≤ L / m * δ * |newtonSeq f f' x₀ n - r| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h_en_le_δ (div_nonneg hL hm0.le))
              (abs_nonneg _)
        _ ≤ 1 / 2 * |newtonSeq f f' x₀ n - r| :=
            mul_le_mul_of_nonneg_right h_coeff (abs_nonneg _)
    show |newtonStep f f' (newtonSeq f f' x₀ n) - r| ≤ (1 / 2) ^ (n + 1) * |x₀ - r|
    calc |newtonStep f f' (newtonSeq f f' x₀ n) - r|
        ≤ L / m * (newtonSeq f f' x₀ n - r) ^ 2 := h_step
      _ ≤ 1 / 2 * |newtonSeq f f' x₀ n - r| := h_half
      _ ≤ 1 / 2 * ((1 / 2) ^ n * |x₀ - r|) := by linarith [ih]
      _ = (1 / 2) ^ (n + 1) * |x₀ - r| := by ring

/-- **Newton–Raphson converges** in the basin: under the quadratic-error
hypotheses with `|x₀ − r| ≤ δ` and `L·δ ≤ m/2`, the iterates tend to the root.
Squeeze of the geometric decay `(½)ⁿ·|x₀ − r| → 0`. -/
theorem newtonSeq_tendsto_root
    (hroot : f r = 0) (hm0 : 0 < m) (hL : 0 ≤ L)
    (hd : ∀ y ∈ Set.Icc (r - δ) (r + δ), HasDerivAt f (f' y) y)
    (hlip : ∀ y ∈ Set.Icc (r - δ) (r + δ), ∀ w ∈ Set.Icc (r - δ) (r + δ),
      |f' y - f' w| ≤ L * |y - w|)
    (hm : ∀ y ∈ Set.Icc (r - δ) (r + δ), m ≤ |f' y|)
    (hx₀ : |x₀ - r| ≤ δ) (hbasin : L * δ ≤ m / 2) :
    Tendsto (newtonSeq f f' x₀) atTop (𝓝 r) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have h_geo : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * |x₀ - r|) atTop (𝓝 0) := by
    have h_pow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using h_pow.mul_const |x₀ - r|
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h_geo
  rw [Real.dist_eq]
  exact newtonSeq_error_le_geometric hroot hm0 hL hd hlip hm hx₀ hbasin n

end MathFin
