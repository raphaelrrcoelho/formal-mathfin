/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaTD
public import MathFin.Foundations.BrownianExpMoment

/-! # Localized (exponential-growth) time-dependent Itô formula

`ito_formula_td_L2_bddDeriv` proves `df = f_x dB + (f_t + ½f_xx) dt` (in integrated `L²`
form) for `f` whose six partials `f_t, f_x, f_xx, f_tt, f_tx, f_xxx` are *globally
bounded*. GBM's value function `f(t,x) = S₀ exp((r−σ²/2)t + σx)` has derivatives `∝ exp(σx)`
— unbounded — so the bounded-derivative formula does not reach it.

This file lifts the formula to `f` of **at-most-exponential growth**
(`|f_• t x| ≤ C exp(λ|x|)` for the six partials): the same conclusion, dropping the six
global bounds. The strategy is an L²-cutoff localization that **reuses** the bounded engine:

* **Cutoff.** A smooth bounded truncation `φₙ` (= `id` on `[−n,n]`, `|φₙ| ≤ min(|·|, 2n)`,
  bounded derivatives) gives `fₙ(t,x) = f(t, φₙ(x))` with *globally bounded* partials per `n`,
  so `ito_formula_td_L2_bddDeriv` applies to each `fₙ`.
* **Pass to the limit.** The boundary term and the drift term converge in `L²(μ)` by
  dominated convergence (the exponential-growth dominators are integrable because Brownian
  marginals have all exponential moments — `BrownianExpMoment`). Hence `aₙ := itoIntegralCLM_T
  gfxₙ` converges, so it is Cauchy; the Itô **isometry** transfers Cauchy-ness back to the
  integrands `gfxₙ ∈ Lp 2 trim`, which converge by completeness to the witness `gfx`; CLM
  **continuity** then identifies the limit and the a.e. identity passes through.

The bounded case is the `ito_formula_td_L2_bddDeriv` special case (`λ` irrelevant when the
partials are bounded). The headline `ito_formula_td_localized` is a drop-in for it.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM QuadraticVariationL2
open scoped NNReal Topology ENNReal

/-- A smooth, bounded, "identity near `0`" modification of `id : ℝ → ℝ`: `C³` with globally
bounded derivatives, `φ x = x` on `[−1, 1]`, `φ'(0) = 1`, `|φ| ≤ min(|·|, M₀)`. Rescaling
`x ↦ ((n:ℝ)+1) · φ(x/((n:ℝ)+1))` yields the cutoff `φₙ` (`= id` on `[−(n+1), n+1]`,
`|φₙ| ≤ |·|`, `|φₙ| ≤ M₀(n+1)`, derivatives bounded by `M₁, M₂/(n+1), M₃/(n+1)²`). The
canonical instance is the antiderivative of a `ContDiffBump`; smoothness and compact support
of the bump give every derivative and bound through Mathlib, with no explicit calculus. The
fields are exactly what the cutoff Itô formula consumes. -/
structure SmoothTrunc where
  φ : ℝ → ℝ
  φ' : ℝ → ℝ
  φ'' : ℝ → ℝ
  φ''' : ℝ → ℝ
  M₀ : ℝ
  M₁ : ℝ
  M₂ : ℝ
  M₃ : ℝ
  hasDeriv₁ : ∀ x, HasDerivAt φ (φ' x) x
  hasDeriv₂ : ∀ x, HasDerivAt φ' (φ'' x) x
  hasDeriv₃ : ∀ x, HasDerivAt φ'' (φ''' x) x
  cont₁ : Continuous φ'
  cont₂ : Continuous φ''
  id_near : ∀ x : ℝ, |x| ≤ 1 → φ x = x
  at_zero₁ : φ' 0 = 1
  le_abs : ∀ x, |φ x| ≤ |x|
  bdd : ∀ x, |φ x| ≤ M₀
  bdd₁ : ∀ x, |φ' x| ≤ M₁
  bdd₂ : ∀ x, |φ'' x| ≤ M₂
  bdd₃ : ∀ x, |φ''' x| ≤ M₃

/-- A `SmoothTrunc` exists: the antiderivative `φ x = ∫₀ˣ ρ` of a `ContDiffBump` `ρ`
(`= 1` on `[−1,1]`, supported in `[−2,2]`, `0 ≤ ρ ≤ 1`). Mathlib supplies everything:
`ρ.contDiff`/`ContDiff.deriv'` give the iterated derivatives `φ' = ρ`, `φ'' = ρ'`,
`φ''' = ρ''`; `HasCompactSupport.exists_bound_of_continuous` bounds them; the FTC
(`intervalIntegral.integral_hasDerivAt_right`) and `norm_integral_le_of_norm_le_const`
give `φ' = ρ` and `|φ x| ≤ |x|`; `ρ.one_of_mem_closedBall` gives `φ = id` near `0`. No
explicit derivative formula is ever written. -/
theorem smoothTrunc_exists : Nonempty SmoothTrunc := by
  classical
  let ρ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  set r : ℝ → ℝ := (ρ : ℝ → ℝ) with hr
  -- smoothness ⇒ the iterated derivatives exist, are continuous, and (via compact support)
  -- are bounded — all from Mathlib, no explicit formulas
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) r := ρ.contDiff
  have hsmooth1 : ContDiff ℝ (⊤ : ℕ∞) (deriv r) := hsmooth.deriv'
  have hdiff0 : Differentiable ℝ r := hsmooth.differentiable (by norm_num)
  have hdiff1 : Differentiable ℝ (deriv r) := hsmooth1.differentiable (by norm_num)
  have hc1 : Continuous (deriv r) := hsmooth.continuous_deriv (by norm_num)
  have hc2 : Continuous (deriv (deriv r)) := hsmooth1.continuous_deriv (by norm_num)
  have hcs1 : HasCompactSupport (deriv r) := ρ.hasCompactSupport.deriv
  have hcs2 : HasCompactSupport (deriv (deriv r)) := hcs1.deriv
  obtain ⟨M₂, hM₂⟩ := hcs1.exists_bound_of_continuous hc1
  obtain ⟨M₃, hM₃⟩ := hcs2.exists_bound_of_continuous hc2
  have hr_nonneg : ∀ x, 0 ≤ r x := fun x => ρ.nonneg
  have hr_le1 : ∀ x, r x ≤ 1 := fun x => ρ.le_one
  have hr_int : Integrable r := ρ.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport
  -- the antiderivative
  set φ : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, r t with hφ
  -- FTC: φ' = r
  have hd1 : ∀ x, HasDerivAt φ (r x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (ρ.continuous.intervalIntegrable 0 x)
      (ρ.continuous.stronglyMeasurableAtFilter volume (nhds x)) ρ.continuous.continuousAt
  -- φ'' = deriv r, φ''' = deriv (deriv r)
  have hd2 : ∀ x, HasDerivAt r (deriv r x) x := fun x => (hdiff0 x).hasDerivAt
  have hd3 : ∀ x, HasDerivAt (deriv r) (deriv (deriv r) x) x := fun x => (hdiff1 x).hasDerivAt
  -- ρ = 1 on the closed unit ball
  have hr_one : ∀ t : ℝ, |t| ≤ 1 → r t = 1 := fun t ht =>
    ρ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact ht)
  -- bounds on φ'
  have hb1 : ∀ x, |r x| ≤ 1 := fun x => by rw [abs_of_nonneg (hr_nonneg x)]; exact hr_le1 x
  -- |φ x| ≤ |x|  (norm of an integral of a `≤ 1` integrand)
  have hla : ∀ x, |φ x| ≤ |x| := fun x => by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := x)
      (C := 1) (f := r) fun t _ => by rw [Real.norm_eq_abs]; exact (abs_of_nonneg (hr_nonneg t)).le.trans (hr_le1 t)
    rw [Real.norm_eq_abs, sub_zero, one_mul] at h
    exact h
  -- φ = id near 0
  have hidn : ∀ x : ℝ, |x| ≤ 1 → φ x = x := fun x hx => by
    have hcongr : ∀ t ∈ Set.uIcc (0 : ℝ) x, r t = (fun _ => (1 : ℝ)) t := fun t ht => by
      refine hr_one t ?_
      have hxle : x ≤ 1 := (abs_le.mp hx).2
      have hxge : -1 ≤ x := (abs_le.mp hx).1
      rw [abs_le]
      exact ⟨le_trans (le_inf (by norm_num) hxge) ht.1,
        le_trans ht.2 (sup_le (by norm_num) hxle)⟩
    show (∫ t in (0 : ℝ)..x, r t) = x
    rw [intervalIntegral.integral_congr hcongr]
    simp
  -- |φ x| ≤ M₀ := ∫ |r|  (eventually constant ⇒ bounded; bound by the full integral)
  set M₀ : ℝ := ∫ t, r t with hM₀
  have hr_nonneg_ae : (0 : ℝ → ℝ) ≤ᵐ[volume] r := ae_of_all _ hr_nonneg
  have hbdd : ∀ x, |φ x| ≤ M₀ := fun x => by
    show |∫ t in (0 : ℝ)..x, r t| ≤ ∫ t, r t
    rcases le_total 0 x with hx | hx
    · rw [intervalIntegral.integral_of_le hx,
        abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc fun t _ => hr_nonneg t)]
      exact setIntegral_le_integral hr_int hr_nonneg_ae
    · rw [intervalIntegral.integral_of_ge hx, abs_neg,
        abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc fun t _ => hr_nonneg t)]
      exact setIntegral_le_integral hr_int hr_nonneg_ae
  exact ⟨{
    φ := φ, φ' := r, φ'' := deriv r, φ''' := deriv (deriv r),
    M₀ := M₀, M₁ := 1, M₂ := M₂, M₃ := M₃,
    hasDeriv₁ := hd1, hasDeriv₂ := hd2, hasDeriv₃ := hd3,
    cont₁ := ρ.continuous, cont₂ := hc1,
    id_near := hidn, at_zero₁ := hr_one 0 (by norm_num),
    le_abs := hla, bdd := hbdd, bdd₁ := hb1, bdd₂ := hM₂, bdd₃ := hM₃ }⟩

namespace SmoothTrunc

/-- The rescaled cutoff `φₙ(x) = (n+1)·φ(x/(n+1))`. It equals `id` on `[−(n+1), n+1]`
(so `φₙ → id` pointwise), with `|φₙ| ≤ min(|·|, M₀(n+1))` and `n`-uniform derivative
bounds — exactly the truncation the localized Itô formula applies `ito_formula_td_L2_bddDeriv`
to. -/
noncomputable def cut (S : SmoothTrunc) (n : ℕ) (x : ℝ) : ℝ :=
  ((n : ℝ) + 1) * S.φ (x / ((n : ℝ) + 1))

/-- For `n + 1 ≥ |x|`, the cutoff is exactly the identity at `x` (since `φ = id` near `0`). -/
lemma cut_eventually_id (S : SmoothTrunc) (x : ℝ) : ∀ᶠ n : ℕ in atTop, S.cut n x = x := by
  filter_upwards [eventually_ge_atTop ⌈|x|⌉₊] with n hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : |x / ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_div, abs_of_pos hn1, div_le_one hn1]
    calc |x| ≤ (⌈|x|⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (n : ℝ) := by exact_mod_cast hn
      _ ≤ (n : ℝ) + 1 := by linarith
  rw [cut, S.id_near _ hle]; field_simp

/-- `φₙ(x) → x` as `n → ∞`. -/
lemma cut_tendsto (S : SmoothTrunc) (x : ℝ) : Tendsto (fun n => S.cut n x) atTop (𝓝 x) :=
  tendsto_const_nhds.congr' ((S.cut_eventually_id x).mono fun _ h => h.symm)

/-- `|φₙ| ≤ |·|` — the `n`-uniform dominator the limit passes use. -/
lemma cut_le_abs (S : SmoothTrunc) (n : ℕ) (x : ℝ) : |S.cut n x| ≤ |x| := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [cut, abs_mul, abs_of_pos hn1]
  calc ((n : ℝ) + 1) * |S.φ (x / ((n : ℝ) + 1))|
      ≤ ((n : ℝ) + 1) * |x / ((n : ℝ) + 1)| := mul_le_mul_of_nonneg_left (S.le_abs _) hn1.le
    _ = |x| := by rw [abs_div, abs_of_pos hn1]; field_simp

/-- `|φₙ| ≤ M₀(n+1)` — so `φₙ` is bounded for each fixed `n` (makes `fₙ`'s derivatives
bounded under exponential growth). -/
lemma cut_bdd (S : SmoothTrunc) (n : ℕ) (x : ℝ) : |S.cut n x| ≤ S.M₀ * ((n : ℝ) + 1) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [cut, abs_mul, abs_of_pos hn1, mul_comm]
  exact mul_le_mul_of_nonneg_right (S.bdd _) hn1.le

/-- `φₙ'(x) = φ'(x/(n+1))`. -/
noncomputable def cutD1 (S : SmoothTrunc) (n : ℕ) (x : ℝ) : ℝ := S.φ' (x / ((n : ℝ) + 1))
/-- `φₙ''(x) = φ''(x/(n+1)) / (n+1)`. -/
noncomputable def cutD2 (S : SmoothTrunc) (n : ℕ) (x : ℝ) : ℝ :=
  S.φ'' (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1)
/-- `φₙ'''(x) = φ'''(x/(n+1)) / (n+1)²`. -/
noncomputable def cutD3 (S : SmoothTrunc) (n : ℕ) (x : ℝ) : ℝ :=
  S.φ''' (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2

/-- The inner rescaling `x ↦ x/(n+1)` has derivative `1/(n+1)`. -/
private lemma hasDerivAt_div_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => y / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) x := by
  simpa using (hasDerivAt_id x).div_const ((n : ℝ) + 1)

lemma cut_hasDerivAt (S : SmoothTrunc) (n : ℕ) (x : ℝ) :
    HasDerivAt (S.cut n) (S.cutD1 n x) x := by
  have heq : S.cutD1 n x = ((n : ℝ) + 1) * (S.φ' (x / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1))) := by
    rw [cutD1]; field_simp
  rw [heq]
  exact ((S.hasDeriv₁ (x / ((n : ℝ) + 1))).comp x (hasDerivAt_div_succ n x)).const_mul ((n : ℝ) + 1)

lemma cutD1_hasDerivAt (S : SmoothTrunc) (n : ℕ) (x : ℝ) :
    HasDerivAt (S.cutD1 n) (S.cutD2 n x) x := by
  have heq : S.cutD2 n x = S.φ'' (x / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) := by
    rw [cutD2]; field_simp
  rw [heq]
  exact (S.hasDeriv₂ (x / ((n : ℝ) + 1))).comp x (hasDerivAt_div_succ n x)

lemma cutD2_hasDerivAt (S : SmoothTrunc) (n : ℕ) (x : ℝ) :
    HasDerivAt (S.cutD2 n) (S.cutD3 n x) x := by
  have heq : S.cutD3 n x = S.φ''' (x / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
    rw [cutD3]; field_simp
  rw [heq]
  exact ((S.hasDeriv₃ (x / ((n : ℝ) + 1))).comp x (hasDerivAt_div_succ n x)).div_const ((n : ℝ) + 1)

lemma cutD1_bdd (S : SmoothTrunc) (n : ℕ) (x : ℝ) : |S.cutD1 n x| ≤ S.M₁ := S.bdd₁ _

lemma cutD2_bdd (S : SmoothTrunc) (n : ℕ) (x : ℝ) : |S.cutD2 n x| ≤ S.M₂ := by
  have hM : 0 ≤ S.M₂ := le_trans (abs_nonneg _) (S.bdd₂ 0)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [cutD2, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1), div_le_iff₀ (by positivity)]
  calc |S.φ'' (x / ((n : ℝ) + 1))| ≤ S.M₂ := S.bdd₂ _
    _ ≤ S.M₂ * ((n : ℝ) + 1) := le_mul_of_one_le_right hM (by linarith)

lemma cutD3_bdd (S : SmoothTrunc) (n : ℕ) (x : ℝ) : |S.cutD3 n x| ≤ S.M₃ := by
  have hM : 0 ≤ S.M₃ := le_trans (abs_nonneg _) (S.bdd₃ 0)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [cutD3, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2),
    div_le_iff₀ (by positivity)]
  calc |S.φ''' (x / ((n : ℝ) + 1))| ≤ S.M₃ := S.bdd₃ _
    _ ≤ S.M₃ * ((n : ℝ) + 1) ^ 2 := le_mul_of_one_le_right hM (by nlinarith [hn])

lemma continuous_cutD1 (S : SmoothTrunc) (n : ℕ) : Continuous (S.cutD1 n) :=
  S.cont₁.comp (continuous_id.div_const _)

lemma continuous_cutD2 (S : SmoothTrunc) (n : ℕ) : Continuous (S.cutD2 n) :=
  (S.cont₂.comp (continuous_id.div_const _)).div_const _

lemma continuous_φ (S : SmoothTrunc) : Continuous S.φ :=
  Differentiable.continuous fun x => (S.hasDeriv₁ x).differentiableAt

lemma continuous_cut (S : SmoothTrunc) (n : ℕ) : Continuous (S.cut n) :=
  continuous_const.mul (S.continuous_φ.comp (continuous_id.div_const _))

end SmoothTrunc

/-- The cutoff function `fₙ(t, x) = f(t, φₙ(x))`. -/
noncomputable def fCut (f : ℝ → ℝ → ℝ) (S : SmoothTrunc) (n : ℕ) (t x : ℝ) : ℝ :=
  f t (S.cut n x)

/-- **A section of `f` with exponential-growth derivative grows at most exponentially.** From
`|f_x t x| ≤ C·exp(λ|x|)` and the segment mean value inequality, `|f t y| ≤ |f t 0| +
C·exp((λ+1)|y|)` (absorbing the `|y|` factor into the exponent via `|y| ≤ exp|y|`). This turns
the *derivative* growth hypothesis into the `f`-value bound the dominated-convergence
dominators need. -/
private lemma abs_le_of_expGrowth_deriv {f f_x : ℝ → ℝ → ℝ}
    (hf_x : ∀ t x, HasDerivAt (fun u => f t u) (f_x t x) x)
    {C lam : ℝ} (hlam : 0 ≤ lam) (hg_x : ∀ t x, |f_x t x| ≤ C * Real.exp (lam * |x|)) (t y : ℝ) :
    |f t y| ≤ |f t 0| + C * Real.exp ((lam + 1) * |y|) := by
  have hC0 : 0 ≤ C := by
    have h := hg_x 0 0; simp only [abs_zero, mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hseg : |f t y - f t 0| ≤ C * Real.exp (lam * |y|) * |y| := by
    have hbound : ∀ x ∈ Set.Icc (-|y|) |y|, ‖f_x t x‖ ≤ C * Real.exp (lam * |y|) := by
      intro x hx
      rw [Real.norm_eq_abs]
      refine (hg_x t x).trans (mul_le_mul_of_nonneg_left ?_ hC0)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by rw [abs_le]; exact ⟨hx.1, hx.2⟩) hlam)
    have hd : ∀ x ∈ Set.Icc (-|y|) |y|,
        HasDerivWithinAt (fun u => f t u) (f_x t x) (Set.Icc (-|y|) |y|) x :=
      fun x _ => (hf_x t x).hasDerivWithinAt
    have h := (convex_Icc (-|y|) |y|).norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound
      (⟨neg_nonpos.mpr (abs_nonneg y), abs_nonneg y⟩ : (0 : ℝ) ∈ Set.Icc (-|y|) |y|)
      (⟨neg_abs_le y, le_abs_self y⟩ : y ∈ Set.Icc (-|y|) |y|)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at h
  have hy : |y| ≤ Real.exp |y| := by linarith [Real.add_one_le_exp |y|]
  have habs : |f t y| ≤ |f t 0| + |f t y - f t 0| := by
    linarith [abs_sub_abs_le_abs_sub (f t y) (f t 0)]
  have hexp : C * Real.exp (lam * |y|) * |y| ≤ C * Real.exp ((lam + 1) * |y|) := by
    rw [show (lam + 1) * |y| = lam * |y| + |y| by ring, Real.exp_add]
    calc C * Real.exp (lam * |y|) * |y|
        ≤ C * Real.exp (lam * |y|) * Real.exp |y| :=
          mul_le_mul_of_nonneg_left hy (mul_nonneg hC0 (Real.exp_nonneg _))
      _ = C * (Real.exp (lam * |y|) * Real.exp |y|) := by ring
  linarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- **The bounded-derivative Itô formula applied to the cutoff `fₙ = f(t, φₙ(x))`.** For `f`
of exponential growth, each `fₙ` has globally bounded partials (the truncation `φₙ` confines
the argument to `[−M₀(n+1), M₀(n+1)]`, where the growth bound is a constant, times the
`n`-uniform bounds on `φₙ`'s derivatives), so `ito_formula_td_L2_bddDeriv` applies and yields
a trim-`L²` integrand `gfxₙ` realizing the chain-rule integrand. The drift integrand is the
genuine `(fₙ)_t + ½(fₙ)_xx` written through the chain rule. -/
theorem cutoff_bddDeriv (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω) (T : ℝ≥0) (S : SmoothTrunc) (n : ℕ)
    {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s => f s x) (f_t t x) t)
    (hf_tt : ∀ t x, HasDerivAt (fun s => f_t s x) (f_tt t x) t)
    (hf_tx : ∀ t x, HasDerivAt (fun u => f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u => f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u => f_x t u) (f_xx t x) x)
    (hf_xxx : ∀ t x, HasDerivAt (fun u => f_xx t u) (f_xxx t x) x)
    (hf_x_cont : Continuous fun p : ℝ × ℝ => f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ => f_xx p.1 p.2)
    {C lam : ℝ} (hlam : 0 ≤ lam)
    (hg_t : ∀ t x, |f_t t x| ≤ C * Real.exp (lam * |x|))
    (hg_x : ∀ t x, |f_x t x| ≤ C * Real.exp (lam * |x|))
    (hg_xx : ∀ t x, |f_xx t x| ≤ C * Real.exp (lam * |x|))
    (hg_tt : ∀ t x, |f_tt t x| ≤ C * Real.exp (lam * |x|))
    (hg_tx : ∀ t x, |f_tx t x| ≤ C * Real.exp (lam * |x|))
    (hg_xxx : ∀ t x, |f_xxx t x| ≤ C * Real.exp (lam * |x|)) :
    ∃ gfx : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω => fCut f S n T (B T ω) - fCut f S n 0 (B 0 ω)) =ᵐ[μ]
        (fun ω => (itoIntegralCLM_T hB T hBmeas gfx) ω
          + ∫ s in Set.Ioc 0 T,
              (f_t s (S.cut n (B s ω))
                + (1 / 2) * (f_xx s (S.cut n (B s ω)) * S.cutD1 n (B s ω) ^ 2
                    + f_x s (S.cut n (B s ω)) * S.cutD2 n (B s ω)))
              ∂ItoIntegralL2.timeMeasure) := by
  classical
  have hC0 : 0 ≤ C := by
    have h := hg_t 0 0
    simp only [abs_zero, mul_zero, Real.exp_zero, mul_one] at h
    exact le_trans (abs_nonneg _) h
  set En : ℝ := C * Real.exp (lam * (S.M₀ * ((n : ℝ) + 1))) with hEn
  have hEn0 : 0 ≤ En := mul_nonneg hC0 (Real.exp_nonneg _)
  -- the growth bound becomes a constant once the argument is confined by the truncation
  have hcb : ∀ (g : ℝ → ℝ → ℝ), (∀ t x, |g t x| ≤ C * Real.exp (lam * |x|)) →
      ∀ t x, |g t (S.cut n x)| ≤ En := by
    intro g hg t x
    refine (hg t (S.cut n x)).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (S.cut_bdd n x) hlam)
  have hcont_cut2 : Continuous fun p : ℝ × ℝ => f_x p.1 (S.cut n p.2) :=
    hf_x_cont.comp (continuous_fst.prodMk ((S.continuous_cut n).comp continuous_snd))
  have hcont_cutxx : Continuous fun p : ℝ × ℝ => f_xx p.1 (S.cut n p.2) :=
    hf_xx_cont.comp (continuous_fst.prodMk ((S.continuous_cut n).comp continuous_snd))
  refine ito_formula_td_L2_bddDeriv hB hBmeas hBcont T (f := fCut f S n)
    (f_t := fun t x => f_t t (S.cut n x))
    (f_x := fun t x => f_x t (S.cut n x) * S.cutD1 n x)
    (f_xx := fun t x => f_xx t (S.cut n x) * S.cutD1 n x ^ 2 + f_x t (S.cut n x) * S.cutD2 n x)
    (f_tt := fun t x => f_tt t (S.cut n x))
    (f_tx := fun t x => f_tx t (S.cut n x) * S.cutD1 n x)
    (f_xxx := fun t x => f_xxx t (S.cut n x) * S.cutD1 n x ^ 3
        + 3 * f_xx t (S.cut n x) * S.cutD1 n x * S.cutD2 n x + f_x t (S.cut n x) * S.cutD3 n x)
    (Ct := En) (C1 := En * S.M₁) (C2 := En * S.M₁ ^ 2 + En * S.M₂) (Ctt := En)
    (Ctx := En * S.M₁) (Cxxx := En * S.M₁ ^ 3 + 3 * (En * S.M₁ * S.M₂) + En * S.M₃)
    ?ht ?htt ?htx ?hx ?hxx ?hxxx ?hxc ?hxxc ?bt ?bx ?bxx ?btt ?btx ?bxxx
  case ht => exact fun t x => hf_t t (S.cut n x)
  case htt => exact fun t x => hf_tt t (S.cut n x)
  case htx => exact fun t x => (hf_tx t (S.cut n x)).comp x (S.cut_hasDerivAt n x)
  case hx => exact fun t x => (hf_x t (S.cut n x)).comp x (S.cut_hasDerivAt n x)
  case hxx =>
    intro t x
    rw [show f_xx t (S.cut n x) * S.cutD1 n x ^ 2 + f_x t (S.cut n x) * S.cutD2 n x
        = f_xx t (S.cut n x) * S.cutD1 n x * S.cutD1 n x + f_x t (S.cut n x) * S.cutD2 n x by ring]
    exact ((hf_xx t (S.cut n x)).comp x (S.cut_hasDerivAt n x)).mul (S.cutD1_hasDerivAt n x)
  case hxxx =>
    intro t x
    have hsq : HasDerivAt (fun u => S.cutD1 n u ^ 2) (2 * S.cutD1 n x * S.cutD2 n x) x := by
      have h := (S.cutD1_hasDerivAt n x).mul (S.cutD1_hasDerivAt n x)
      rw [show (fun u => S.cutD1 n u ^ 2) = (fun u => S.cutD1 n u * S.cutD1 n u) from
            funext fun u => sq (S.cutD1 n u),
          show 2 * S.cutD1 n x * S.cutD2 n x
            = S.cutD2 n x * S.cutD1 n x + S.cutD1 n x * S.cutD2 n x from by ring]
      exact h
    rw [show f_xxx t (S.cut n x) * S.cutD1 n x ^ 3
            + 3 * f_xx t (S.cut n x) * S.cutD1 n x * S.cutD2 n x + f_x t (S.cut n x) * S.cutD3 n x
          = f_xxx t (S.cut n x) * S.cutD1 n x * S.cutD1 n x ^ 2
              + f_xx t (S.cut n x) * (2 * S.cutD1 n x * S.cutD2 n x)
            + (f_xx t (S.cut n x) * S.cutD1 n x * S.cutD2 n x + f_x t (S.cut n x) * S.cutD3 n x)
          by ring]
    exact (((hf_xxx t (S.cut n x)).comp x (S.cut_hasDerivAt n x)).mul hsq).add
      (((hf_xx t (S.cut n x)).comp x (S.cut_hasDerivAt n x)).mul (S.cutD2_hasDerivAt n x))
  case hxc => exact hcont_cut2.mul ((S.continuous_cutD1 n).comp continuous_snd)
  case hxxc =>
    exact (hcont_cutxx.mul (((S.continuous_cutD1 n).comp continuous_snd).pow 2)).add
      (hcont_cut2.mul ((S.continuous_cutD2 n).comp continuous_snd))
  case bt => exact fun t x => hcb f_t hg_t t x
  case btt => exact fun t x => hcb f_tt hg_tt t x
  case btx =>
    intro t x
    rw [abs_mul]
    exact mul_le_mul (hcb f_tx hg_tx t x) (S.cutD1_bdd n x) (abs_nonneg _) hEn0
  case bx =>
    intro t x
    rw [abs_mul]
    exact mul_le_mul (hcb f_x hg_x t x) (S.cutD1_bdd n x) (abs_nonneg _) hEn0
  case bxx =>
    intro t x
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_pow]
      exact mul_le_mul (hcb f_xx hg_xx t x) (pow_le_pow_left₀ (abs_nonneg _) (S.cutD1_bdd n x) 2)
        (by positivity) hEn0
    · rw [abs_mul]; exact mul_le_mul (hcb f_x hg_x t x) (S.cutD2_bdd n x) (abs_nonneg _) hEn0
  case bxxx =>
    intro t x
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul, abs_pow]
      exact mul_le_mul (hcb f_xxx hg_xxx t x) (pow_le_pow_left₀ (abs_nonneg _) (S.cutD1_bdd n x) 3)
        (by positivity) hEn0
    · have hM1 : 0 ≤ S.M₁ := le_trans (abs_nonneg _) (S.cutD1_bdd n x)
      have hb : |f_xx t (S.cut n x) * S.cutD1 n x * S.cutD2 n x| ≤ En * S.M₁ * S.M₂ := by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul (hcb f_xx hg_xx t x) (S.cutD1_bdd n x) (abs_nonneg _) hEn0)
          (S.cutD2_bdd n x) (abs_nonneg _) (mul_nonneg hEn0 hM1)
      rw [show (3 : ℝ) * f_xx t (S.cut n x) * S.cutD1 n x * S.cutD2 n x
            = 3 * (f_xx t (S.cut n x) * S.cutD1 n x * S.cutD2 n x) by ring, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      exact mul_le_mul_of_nonneg_left hb (by norm_num)
    · rw [abs_mul]; exact mul_le_mul (hcb f_x hg_x t x) (S.cutD3_bdd n x) (abs_nonneg _) hEn0

/-- **The path integral of an exponential-growth integrand lies in `L²(μ)`.** For a weight
`w : ℝ≥0 → ℝ → ℝ`, measurable in space, with `|w s x| ≤ K·exp(c|x|)`, the pathwise integral
`ω ↦ ∫₀ᵀ w_s(B_s ω) ds` is square-integrable. This is the exponential-growth generalization
of `memLp_pathIntegral_process` (which needs a *uniform* bound), and the reusable base stone
the localized formula's drift dominator stands on. The proof is Fatou over the left-endpoint
Riemann sums: each path `s ↦ w_s(B_s ω)` is continuous, hence locally bounded on `[0,T]`, so
its Riemann sums converge to the integral (`tendsto_riemann_continuous` — applied per path,
the integrand having *no uniform bound*); the limit is therefore measurable, and a discrete
Cauchy–Schwarz `(∑ w·Δ)² ≤ (∑Δ)(∑ w²·Δ)` plus the Brownian marginal moment
`∫ exp(2c|B_{tₖ}|) ≤ 2·exp(2c²·tₖ)` bound `∫ (Riemannₙ)² ≤ 2K²T²·exp(2c²T)` uniformly in `n`;
`lintegral_liminf_le` lifts that to `∫ (path integral)²`. -/
theorem pathIntegral_expGrowth_memLp (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    {w : ℝ≥0 → ℝ → ℝ} (hw_meas : ∀ s, Measurable (w s)) {K : ℝ} (hK : 0 ≤ K) {c : ℝ}
    (hw_bdd : ∀ s x, |w s x| ≤ K * Real.exp (c * |x|))
    (hw_cont : ∀ ω, Continuous fun s : ℝ≥0 => w s (B s ω)) :
    MemLp (fun ω => ∫ s in Set.Ioc 0 T, w s (B s ω) ∂ItoIntegralL2.timeMeasure) 2 μ := by
  classical
  set P : Ω → ℝ := fun ω => ∫ s in Set.Ioc 0 T, w s (B s ω) ∂ItoIntegralL2.timeMeasure with hP
  set Rsum : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n,
    w (unifPart T n k) (B (unifPart T n k) ω)
      * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) with hRsum
  have hg_meas : ∀ s, Measurable (fun ω => w s (B s ω)) := fun s => (hw_meas s).comp (hBmeas s)
  have hR_meas : ∀ n, Measurable (Rsum n) := fun n =>
    Finset.measurable_sum _ fun k _ => (hg_meas _).mul_const _
  -- per-path Riemann convergence: each path is continuous, hence bounded on the compact `[0,T]`
  have hpath : ∀ ω, Tendsto (fun n => Rsum n ω) atTop (𝓝 (P ω)) := by
    intro ω
    obtain ⟨Cω, hCω⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      (hw_cont ω).continuousOn
    exact tendsto_riemann_continuous (h := fun s => w s (B s ω)) (hw_cont ω) T
      (fun s hs => by rw [← Real.norm_eq_abs]; exact hCω s ⟨zero_le, hs⟩)
  have hP_meas : Measurable P := measurable_of_tendsto_metrizable hR_meas (tendsto_pi_nhds.mpr hpath)
  -- pointwise growth domination and the per-marginal `L²` bound
  have hdom : ∀ (s : ℝ≥0) (ω : Ω),
      (w s (B s ω)) ^ 2 ≤ K ^ 2 * Real.exp (2 * c * |B s ω|) := by
    intro s ω
    calc (w s (B s ω)) ^ 2 = |w s (B s ω)| ^ 2 := (sq_abs _).symm
      _ ≤ (K * Real.exp (c * |B s ω|)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (hw_bdd s (B s ω)) 2
      _ = K ^ 2 * Real.exp (2 * c * |B s ω|) := by
          have hexp2 : Real.exp (c * |B s ω|) ^ 2 = Real.exp (2 * c * |B s ω|) := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
          rw [mul_pow, hexp2]
  have hwsq_int : ∀ s : ℝ≥0, Integrable (fun ω => (w s (B s ω)) ^ 2) μ := fun s =>
    ((integrable_exp_abs_eval hB s (2 * c)).const_mul (K ^ 2)).mono'
      ((hg_meas s).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hdom s ω)
  set A : ℝ := 2 * K ^ 2 * Real.exp (2 * c ^ 2 * (T : ℝ)) with hA
  have hpoint : ∀ s : ℝ≥0, s ≤ T → ∫ ω, (w s (B s ω)) ^ 2 ∂μ ≤ A := by
    intro s hsT
    calc ∫ ω, (w s (B s ω)) ^ 2 ∂μ
        ≤ ∫ ω, K ^ 2 * Real.exp (2 * c * |B s ω|) ∂μ :=
          integral_mono (hwsq_int s) ((integrable_exp_abs_eval hB s (2 * c)).const_mul _)
            (hdom s)
      _ = K ^ 2 * ∫ ω, Real.exp (2 * c * |B s ω|) ∂μ := integral_const_mul _ _
      _ ≤ K ^ 2 * (2 * Real.exp ((2 * c) ^ 2 * (s : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (integral_exp_abs_eval_le hB s (2 * c)) (sq_nonneg K)
      _ ≤ A := by
          rw [hA]
          have hexp : Real.exp ((2 * c) ^ 2 * (s : ℝ) / 2) ≤ Real.exp (2 * c ^ 2 * (T : ℝ)) := by
            apply Real.exp_le_exp.mpr
            rw [show (2 * c) ^ 2 * (s : ℝ) / 2 = 2 * c ^ 2 * (s : ℝ) by ring]
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsT) (by positivity)
          nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hexp), Real.exp_nonneg (2 * c ^ 2 * (T : ℝ))]
  -- the uniform `L²` bound on the Riemann sums via discrete Cauchy–Schwarz
  set Bnd : ℝ := (T : ℝ) * ((T : ℝ) * A) with hBnd
  have hgap_nonneg : ∀ n k, (0 : ℝ) ≤ (unifPart T n (k + 1) : ℝ) - unifPart T n k := by
    intro n k
    have : unifPart T n k ≤ unifPart T n (k + 1) := by
      simp only [unifPart]; gcongr <;> simp
    exact sub_nonneg.mpr (by exact_mod_cast this)
  have hle_T : ∀ n k, k ≤ n → unifPart T n k ≤ T := by
    intro n k hk
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0; simp only [Nat.le_zero.mp hk]; simp [unifPart]
    · have hkn : (k : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hk
      have hnpos : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
      simp only [unifPart]
      calc (k : ℝ≥0) / (n : ℝ≥0) * T ≤ 1 * T :=
            mul_le_mul_of_nonneg_right ((div_le_one hnpos).mpr hkn) zero_le
        _ = T := one_mul _
  have hsumgap : ∀ n, 0 < n →
      ∑ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) := by
    intro n hn
    rw [Finset.sum_range_sub (fun k => (unifPart T n k : ℝ))]
    have h1 : unifPart T n n = T := by
      have hne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [unifPart, div_self hne, one_mul]
    have h0 : unifPart T n 0 = 0 := by simp [unifPart]
    rw [h1, h0]; simp
  have hCS : ∀ n, ∀ ω, (Rsum n ω) ^ 2 ≤ (T : ℝ) *
      ∑ k ∈ Finset.range n, (w (unifPart T n k) (B (unifPart T n k) ω)) ^ 2
        * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0; simp [hRsum]
    · have e1 : (∑ k ∈ Finset.range n, Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
            * (w (unifPart T n k) (B (unifPart T n k) ω)
                * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)))
          = Rsum n ω := by
        rw [hRsum]; refine Finset.sum_congr rfl fun k _ => ?_
        rw [show Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
              * (w (unifPart T n k) (B (unifPart T n k) ω)
                  * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k))
            = w (unifPart T n k) (B (unifPart T n k) ω)
              * (Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
                  * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) by ring,
          Real.mul_self_sqrt (hgap_nonneg n k)]
      have e2 : (∑ k ∈ Finset.range n,
            (Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) = (T : ℝ) := by
        rw [← hsumgap n hn]; refine Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hgap_nonneg n k)
      have e3 : (∑ k ∈ Finset.range n, (w (unifPart T n k) (B (unifPart T n k) ω)
            * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2)
          = ∑ k ∈ Finset.range n, (w (unifPart T n k) (B (unifPart T n k) ω)) ^ 2
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_pow, Real.sq_sqrt (hgap_nonneg n k)]
      calc (Rsum n ω) ^ 2
          = (∑ k ∈ Finset.range n, Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
              * (w (unifPart T n k) (B (unifPart T n k) ω)
                  * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k))) ^ 2 := by rw [e1]
        _ ≤ (∑ k ∈ Finset.range n,
              (Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2)
            * (∑ k ∈ Finset.range n, (w (unifPart T n k) (B (unifPart T n k) ω)
                * Real.sqrt ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) ^ 2) :=
            Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = (T : ℝ) * ∑ k ∈ Finset.range n, (w (unifPart T n k) (B (unifPart T n k) ω)) ^ 2
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by rw [e2, e3]
  -- the `L²` membership of each Riemann sum (finite sum of `L²` functions)
  have hwk_memLp : ∀ s : ℝ≥0, MemLp (fun ω => w s (B s ω)) 2 μ := fun s =>
    (memLp_two_iff_integrable_sq (hg_meas s).aestronglyMeasurable).mpr (hwsq_int s)
  have hRsum_memLp : ∀ n, MemLp (Rsum n) 2 μ := fun n => by
    rw [hRsum]
    refine memLp_finsetSum _ fun k _ => ?_
    have := (hwk_memLp (unifPart T n k)).const_mul ((unifPart T n (k + 1) : ℝ) - unifPart T n k)
    simpa [mul_comm] using this
  have hRsq_int : ∀ n, Integrable (fun ω => (Rsum n ω) ^ 2) μ := fun n => by
    have hsq : (fun ω => (Rsum n ω) ^ 2) = fun ω => Rsum n ω * Rsum n ω := by funext ω; ring
    rw [hsq]; exact (hRsum_memLp n).integrable_mul (hRsum_memLp n)
  -- integrate the Cauchy–Schwarz bound to a uniform `∫ (Rsumₙ)² ≤ Bnd`
  have hRbound : ∀ n, ∫ ω, (Rsum n ω) ^ 2 ∂μ ≤ Bnd := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0
      simp only [hRsum, Finset.range_zero, Finset.sum_empty]
      rw [show (fun _ : Ω => (0 : ℝ) ^ 2) = fun _ : Ω => (0 : ℝ) by funext ω; ring, integral_zero]
      rw [hBnd, hA]; positivity
    · have hint_rhs : Integrable (fun ω => (T : ℝ) *
          ∑ k ∈ Finset.range n, (w (unifPart T n k) (B (unifPart T n k) ω)) ^ 2
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k)) μ :=
        (integrable_finsetSum _ fun k _ =>
          (hwsq_int (unifPart T n k)).mul_const _).const_mul _
      calc ∫ ω, (Rsum n ω) ^ 2 ∂μ
          ≤ ∫ ω, (T : ℝ) * ∑ k ∈ Finset.range n,
              (w (unifPart T n k) (B (unifPart T n k) ω)) ^ 2
                * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ∂μ :=
            integral_mono (hRsq_int n) hint_rhs (hCS n)
        _ = (T : ℝ) * ∑ k ∈ Finset.range n,
              (∫ ω, (w (unifPart T n k) (B (unifPart T n k) ω)) ^ 2 ∂μ)
                * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
            rw [integral_const_mul, integral_finsetSum _ fun k _ =>
              (hwsq_int (unifPart T n k)).mul_const _]
            refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
            rw [integral_mul_const]
        _ ≤ (T : ℝ) * ∑ k ∈ Finset.range n, A
              * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (NNReal.coe_nonneg T)
            exact mul_le_mul_of_nonneg_right
              (hpoint _ (hle_T n k (Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Finset.mem_range.mp hk)))))
              (hgap_nonneg n k)
        _ = Bnd := by
            rw [← Finset.mul_sum, hsumgap n hn, hBnd]; ring
  -- Fatou: lift the uniform bound to the limit `P`
  refine (memLp_two_iff_integrable_sq hP_meas.aestronglyMeasurable).mpr ?_
  refine ⟨(hP_meas.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hconv : ∀ ω, Tendsto (fun n => ‖(Rsum n ω) ^ 2‖ₑ) atTop (𝓝 (‖(P ω) ^ 2‖ₑ)) := fun ω =>
    (continuous_enorm.tendsto _).comp ((hpath ω).pow 2)
  calc ∫⁻ ω, ‖(P ω) ^ 2‖ₑ ∂μ
      = ∫⁻ ω, liminf (fun n => ‖(Rsum n ω) ^ 2‖ₑ) atTop ∂μ :=
        lintegral_congr fun ω => (hconv ω).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ ω, ‖(Rsum n ω) ^ 2‖ₑ ∂μ) atTop :=
        lintegral_liminf_le fun n => ((hR_meas n).pow_const 2).enorm
    _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal Bnd) atTop := by
        refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
        have hee : (fun ω => ‖(Rsum n ω) ^ 2‖ₑ) = fun ω => ENNReal.ofReal ((Rsum n ω) ^ 2) :=
          funext fun ω => Real.enorm_eq_ofReal (sq_nonneg _)
        rw [hee, ← ofReal_integral_eq_lintegral_ofReal (hRsq_int n) (ae_of_all _ fun ω => sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hRbound n)
    _ = ENNReal.ofReal Bnd := liminf_const _
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- **Boundary `L²` convergence.** The cutoff boundary `fₙ(T,B_T) − fₙ(0,B_0)` converges to
the genuine `f(T,B_T) − f(0,B_0)` in `L²(μ)`. Each path eventually satisfies `φₙ = id` at the
sampled point (`cut_eventually_id`), so the difference is pointwise eventually `0`; the
`f`-value bound `abs_le_of_expGrowth_deriv` together with the Brownian marginal exponential
moments (`memLp_exp_abs_eval`) furnishes a fixed `L²` dominator, and dominated convergence
gives the `L²` limit. -/
theorem boundary_tendsto_L2 (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (S : SmoothTrunc)
    {f f_x : ℝ → ℝ → ℝ} (hf_x : ∀ t x, HasDerivAt (fun u => f t u) (f_x t x) x)
    {C lam : ℝ} (hlam : 0 ≤ lam) (hg_x : ∀ t x, |f_x t x| ≤ C * Real.exp (lam * |x|)) :
    Tendsto (fun n => ∫ ω,
        ((fCut f S n T (B T ω) - fCut f S n 0 (B 0 ω)) - (f T (B T ω) - f 0 (B 0 ω))) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  classical
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (by simpa using hg_x 0 0)
  have hcont_f : ∀ t : ℝ, Continuous (fun x => f t x) := fun t =>
    Differentiable.continuous fun x => (hf_x t x).differentiableAt
  set bn : ℕ → Ω → ℝ := fun n ω =>
    (fCut f S n T (B T ω) - fCut f S n 0 (B 0 ω)) - (f T (B T ω) - f 0 (B 0 ω)) with hbn
  set H : Ω → ℝ := fun ω => 2 * (|f (T : ℝ) 0| + C * Real.exp ((lam + 1) * |B T ω|))
    + 2 * (|f (0 : ℝ) 0| + C * Real.exp ((lam + 1) * |B 0 ω|)) with hH
  -- the `f`-value bound, specialised to a cutoff argument
  have hfc : ∀ (n : ℕ) (t z : ℝ), |f t (S.cut n z)| ≤ |f t 0| + C * Real.exp ((lam + 1) * |z|) :=
    fun n t z => (abs_le_of_expGrowth_deriv hf_x hlam hg_x t (S.cut n z)).trans (by
      have hmono : Real.exp ((lam + 1) * |S.cut n z|) ≤ Real.exp ((lam + 1) * |z|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (S.cut_le_abs n z) (by linarith))
      linarith [mul_le_mul_of_nonneg_left hmono hC0])
  -- `H ∈ L²(μ)` and the dominator `H²` is integrable
  have hHmemLp : MemLp H 2 μ := by
    refine MemLp.add ?_ ?_
    · exact (((memLp_const (|f (T : ℝ) 0|)).add
        ((memLp_exp_abs_eval hB T (lam + 1)).const_mul C)).const_mul 2)
    · exact (((memLp_const (|f (0 : ℝ) 0|)).add
        ((memLp_exp_abs_eval hB 0 (lam + 1)).const_mul C)).const_mul 2)
  have hGint : Integrable (fun ω => (H ω) ^ 2) μ := by
    have hsq : (fun ω => (H ω) ^ 2) = fun ω => H ω * H ω := by funext ω; ring
    rw [hsq]; exact hHmemLp.integrable_mul hHmemLp
  -- the uniform pointwise bound `|bn n ω| ≤ H ω`
  have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    rw [sub_eq_add_neg]; exact (abs_add_le a (-b)).trans (by rw [abs_neg])
  have hbnd : ∀ n ω, |bn n ω| ≤ H ω := by
    intro n ω
    have e1 := hfc n (T : ℝ) (B T ω)
    have e2 := hfc n (0 : ℝ) (B 0 ω)
    have e3 := abs_le_of_expGrowth_deriv hf_x hlam hg_x (T : ℝ) (B T ω)
    have e4 := abs_le_of_expGrowth_deriv hf_x hlam hg_x (0 : ℝ) (B 0 ω)
    simp only [hbn, hH, fCut]
    calc |(f (T : ℝ) (S.cut n (B T ω)) - f (0 : ℝ) (S.cut n (B 0 ω)))
            - (f (T : ℝ) (B T ω) - f (0 : ℝ) (B 0 ω))|
        ≤ |f (T : ℝ) (S.cut n (B T ω)) - f (0 : ℝ) (S.cut n (B 0 ω))|
            + |f (T : ℝ) (B T ω) - f (0 : ℝ) (B 0 ω)| := htri _ _
      _ ≤ (|f (T : ℝ) (S.cut n (B T ω))| + |f (0 : ℝ) (S.cut n (B 0 ω))|)
            + (|f (T : ℝ) (B T ω)| + |f (0 : ℝ) (B 0 ω)|) := add_le_add (htri _ _) (htri _ _)
      _ ≤ 2 * (|f (T : ℝ) 0| + C * Real.exp ((lam + 1) * |B T ω|))
            + 2 * (|f (0 : ℝ) 0| + C * Real.exp ((lam + 1) * |B 0 ω|)) := by linarith
  -- measurability of each squared difference
  have hbn_meas : ∀ n, Measurable (bn n) := fun n => by
    have m1 : Measurable (fun ω => f (T : ℝ) (S.cut n (B T ω))) :=
      ((hcont_f (T : ℝ)).comp (S.continuous_cut n)).measurable.comp (hBmeas T)
    have m2 : Measurable (fun ω => f (0 : ℝ) (S.cut n (B 0 ω))) :=
      ((hcont_f (0 : ℝ)).comp (S.continuous_cut n)).measurable.comp (hBmeas 0)
    have m3 : Measurable (fun ω => f (T : ℝ) (B T ω)) := (hcont_f (T : ℝ)).measurable.comp (hBmeas T)
    have m4 : Measurable (fun ω => f (0 : ℝ) (B 0 ω)) := (hcont_f (0 : ℝ)).measurable.comp (hBmeas 0)
    simpa only [hbn, fCut] using (m1.sub m2).sub (m3.sub m4)
  -- pointwise: eventually `bn n ω = 0`, hence `(bn n ω)² → 0`
  have hlim : ∀ ω, Tendsto (fun n => (bn n ω) ^ 2) atTop (𝓝 0) := fun ω =>
    (tendsto_congr' (by
      filter_upwards [S.cut_eventually_id (B T ω), S.cut_eventually_id (B 0 ω)] with n hT h0
      simp only [hbn, fCut, hT, h0]; ring)).mpr tendsto_const_nhds
  have key := tendsto_integral_of_dominated_convergence
    (F := fun n ω => (bn n ω) ^ 2) (f := fun _ : Ω => (0 : ℝ)) (bound := fun ω => (H ω) ^ 2)
    (fun n => ((hbn_meas n).pow_const 2).aestronglyMeasurable) hGint
    (fun n => ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (bn n ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbnd n ω) 2)
    (ae_of_all _ fun ω => hlim ω)
  simpa using key

/-- **Drift `L²` convergence.** The cutoff drift integrand converges to the genuine drift
`f_t(s,B_s) + ½f_xx(s,B_s)` in `L²(μ)`. For each path, the inner `ds`-integrand converges
pointwise (`φₙ → id`, `φₙ' → 1`, `φₙ'' /(n+1) → 0`) and is uniformly bounded on the compact
`[0,T]`, so bounded convergence gives the inner integral's limit; the outer difference is then
dominated by the exponential-growth path integral `H = ∫₀ᵀ Kdom·exp(λ|B_s|) ds ∈ L²(μ)`
(`pathIntegral_expGrowth_memLp`), and dominated convergence closes the `L²` limit. -/
theorem drift_tendsto_L2 (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω) (T : ℝ≥0) (S : SmoothTrunc)
    {f_t f_x f_xx : ℝ → ℝ → ℝ}
    (hf_t_cont : Continuous fun p : ℝ × ℝ => f_t p.1 p.2)
    (hf_x_cont : Continuous fun p : ℝ × ℝ => f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ => f_xx p.1 p.2)
    {C lam : ℝ} (hlam : 0 ≤ lam)
    (hg_t : ∀ t x, |f_t t x| ≤ C * Real.exp (lam * |x|))
    (hg_x : ∀ t x, |f_x t x| ≤ C * Real.exp (lam * |x|))
    (hg_xx : ∀ t x, |f_xx t x| ≤ C * Real.exp (lam * |x|)) :
    Tendsto (fun n => ∫ ω,
        ((∫ s in Set.Ioc 0 T, (f_t s (S.cut n (B s ω))
              + (1 / 2) * (f_xx s (S.cut n (B s ω)) * S.cutD1 n (B s ω) ^ 2
                  + f_x s (S.cut n (B s ω)) * S.cutD2 n (B s ω))) ∂ItoIntegralL2.timeMeasure)
          - (∫ s in Set.Ioc 0 T, (f_t s (B s ω) + (1 / 2) * f_xx s (B s ω))
              ∂ItoIntegralL2.timeMeasure)) ^ 2 ∂μ) atTop (𝓝 0) := by
  classical
  haveI hνT : IsFiniteMeasure (ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 T)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        ItoIntegralL2.timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (by simpa using hg_t 0 0)
  have hM2 : 0 ≤ S.M₂ := le_trans (abs_nonneg _) (S.bdd₂ 0)
  set K1 : ℝ := C * (1 + (1 / 2) * S.M₁ ^ 2 + (1 / 2) * S.M₂) with hK1
  set Kdom : ℝ := K1 + C * (1 + 1 / 2) with hKdom
  have hK1_0 : 0 ≤ K1 := by rw [hK1]; positivity
  have hKdom0 : 0 ≤ Kdom := by rw [hKdom]; positivity
  -- inner integrands and their per-path data
  set Jn : ℕ → Ω → ℝ≥0 → ℝ := fun n ω s => f_t s (S.cut n (B s ω))
      + (1 / 2) * (f_xx s (S.cut n (B s ω)) * S.cutD1 n (B s ω) ^ 2
          + f_x s (S.cut n (B s ω)) * S.cutD2 n (B s ω)) with hJn
  set Jl : Ω → ℝ≥0 → ℝ := fun ω s => f_t s (B s ω) + (1 / 2) * f_xx s (B s ω) with hJl
  set driftCut : ℕ → Ω → ℝ := fun n ω =>
    ∫ s in Set.Ioc 0 T, Jn n ω s ∂ItoIntegralL2.timeMeasure with hdriftCut
  set drift : Ω → ℝ := fun ω => ∫ s in Set.Ioc 0 T, Jl ω s ∂ItoIntegralL2.timeMeasure with hdrift
  show Tendsto (fun n => ∫ ω, (driftCut n ω - drift ω) ^ 2 ∂μ) atTop (𝓝 0)
  -- the growth bound on the cutoff inner integrand, uniform in `n`
  have hJn_bound : ∀ n ω s, |Jn n ω s| ≤ K1 * Real.exp (lam * |B s ω|) := by
    intro n ω s
    set Ec : ℝ := Real.exp (lam * |S.cut n (B s ω)|) with hEc
    have hEc0 : 0 ≤ Ec := Real.exp_nonneg _
    have hCEc0 : 0 ≤ C * Ec := mul_nonneg hC0 hEc0
    have hcut : Ec ≤ Real.exp (lam * |B s ω|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (S.cut_le_abs n (B s ω)) hlam)
    have ht : |f_t (s : ℝ) (S.cut n (B s ω))| ≤ C * Ec := hg_t s (S.cut n (B s ω))
    have hxx : |f_xx (s : ℝ) (S.cut n (B s ω))| ≤ C * Ec := hg_xx s (S.cut n (B s ω))
    have hx : |f_x (s : ℝ) (S.cut n (B s ω))| ≤ C * Ec := hg_x s (S.cut n (B s ω))
    have hd1 : S.cutD1 n (B s ω) ^ 2 ≤ S.M₁ ^ 2 := by
      rw [← sq_abs (S.cutD1 n (B s ω))]; exact pow_le_pow_left₀ (abs_nonneg _) (S.cutD1_bdd n _) 2
    have hd2 : |S.cutD2 n (B s ω)| ≤ S.M₂ := S.cutD2_bdd n _
    calc |Jn n ω s|
        ≤ C * Ec + (1 / 2) * (C * Ec * S.M₁ ^ 2 + C * Ec * S.M₂) := by
          simp only [hJn]
          refine (abs_add_le _ _).trans (add_le_add ht ?_)
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ ?_))
            (by norm_num)
          · rw [abs_mul, abs_of_nonneg (sq_nonneg (S.cutD1 n (B s ω)))]
            exact mul_le_mul hxx hd1 (sq_nonneg _) hCEc0
          · rw [abs_mul]; exact mul_le_mul hx hd2 (abs_nonneg _) hCEc0
      _ = K1 * Ec := by rw [hK1]; ring
      _ ≤ K1 * Real.exp (lam * |B s ω|) := mul_le_mul_of_nonneg_left hcut hK1_0
  -- the inner integrand is continuous in `s` (joint continuity of the partials)
  have hJn_cont : ∀ n ω, Continuous (Jn n ω) := by
    intro n ω
    have hpair : Continuous fun s : ℝ≥0 => ((s : ℝ), S.cut n (B s ω)) :=
      NNReal.continuous_coe.prodMk ((S.continuous_cut n).comp (hBcont ω))
    rw [hJn]
    refine (hf_t_cont.comp hpair).add (continuous_const.mul ((((hf_xx_cont.comp hpair).mul
      (((S.continuous_cutD1 n).comp (hBcont ω)).pow 2))).add
      ((hf_x_cont.comp hpair).mul ((S.continuous_cutD2 n).comp (hBcont ω)))))
  have hJl_cont : ∀ ω, Continuous (Jl ω) := by
    intro ω
    have hpair : Continuous fun s : ℝ≥0 => ((s : ℝ), B s ω) :=
      NNReal.continuous_coe.prodMk (hBcont ω)
    rw [hJl]
    exact (hf_t_cont.comp hpair).add (continuous_const.mul (hf_xx_cont.comp hpair))
  -- per-path inner convergence `driftCut n ω → drift ω` (bounded convergence on `[0,T]`)
  have hinner : ∀ ω, Tendsto (fun n => driftCut n ω) atTop (𝓝 (drift ω)) := by
    intro ω
    obtain ⟨Mω, hMω⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      (hBcont ω).continuousOn
    have hconst : Integrable (fun _ : ℝ≥0 => K1 * Real.exp (lam * Mω))
        (ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 T)) := integrable_const _
    -- pointwise convergence of the inner integrand
    have hz0 : ∀ z : ℝ, Tendsto (fun n : ℕ => z / ((n : ℝ) + 1)) atTop (𝓝 0) := fun z => by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul z
      simpa [div_eq_mul_inv] using this
    have hcutD1 : ∀ z : ℝ, Tendsto (fun n => S.cutD1 n z) atTop (𝓝 1) := fun z => by
      have h : Tendsto (fun n : ℕ => S.φ' (z / ((n : ℝ) + 1))) atTop (𝓝 (S.φ' 0)) :=
        (S.cont₁.continuousAt).tendsto.comp (hz0 z)
      rw [S.at_zero₁] at h
      exact h
    have hcutD2 : ∀ z : ℝ, Tendsto (fun n => S.cutD2 n z) atTop (𝓝 0) := fun z => by
      have hφ : Tendsto (fun n : ℕ => S.φ'' (z / ((n : ℝ) + 1))) atTop (𝓝 (S.φ'' 0)) :=
        (S.cont₂.continuousAt).tendsto.comp (hz0 z)
      have hrec : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hmul := hφ.mul hrec
      rw [mul_zero] at hmul
      exact Tendsto.congr (fun n => by simp only [SmoothTrunc.cutD2]; ring) hmul
    have hptw : ∀ s : ℝ≥0, Tendsto (fun n => Jn n ω s) atTop (𝓝 (Jl ω s)) := by
      intro s
      have hft : Tendsto (fun n => f_t (s : ℝ) (S.cut n (B s ω))) atTop (𝓝 (f_t s (B s ω))) :=
        ((hf_t_cont.comp (continuous_const.prodMk continuous_id)).continuousAt
          (x := B s ω)).tendsto.comp (S.cut_tendsto (B s ω))
      have hfxx : Tendsto (fun n => f_xx (s : ℝ) (S.cut n (B s ω))) atTop (𝓝 (f_xx s (B s ω))) :=
        ((hf_xx_cont.comp (continuous_const.prodMk continuous_id)).continuousAt
          (x := B s ω)).tendsto.comp (S.cut_tendsto (B s ω))
      have hfx : Tendsto (fun n => f_x (s : ℝ) (S.cut n (B s ω))) atTop (𝓝 (f_x s (B s ω))) :=
        ((hf_x_cont.comp (continuous_const.prodMk continuous_id)).continuousAt
          (x := B s ω)).tendsto.comp (S.cut_tendsto (B s ω))
      have hsq : Tendsto (fun n => S.cutD1 n (B s ω) ^ 2) atTop (𝓝 1) := by
        have := (hcutD1 (B s ω)).pow 2; simpa using this
      rw [hJn, hJl]
      have := hft.add (((hfxx.mul hsq).add (hfx.mul (hcutD2 (B s ω)))).const_mul (1 / 2))
      simpa using this
    have hmeas : ∀ n, AEStronglyMeasurable (Jn n ω)
        (ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 T)) :=
      fun n => (hJn_cont n ω).aestronglyMeasurable
    have hbound : ∀ n, ∀ᵐ s ∂(ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 T)),
        ‖Jn n ω s‖ ≤ K1 * Real.exp (lam * Mω) := by
      intro n
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs => ?_)
      rw [Real.norm_eq_abs]
      refine (hJn_bound n ω s).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK1_0
      refine mul_le_mul_of_nonneg_left ?_ hlam
      have := hMω s ⟨zero_le, hs.2⟩
      rwa [Real.norm_eq_abs] at this
    exact tendsto_integral_of_dominated_convergence _ hmeas hconst hbound
      (ae_of_all _ fun s => hptw s)
  -- the outer `L²` dominator `H = ∫₀ᵀ Kdom·exp(λ|B_s|) ds ∈ L²(μ)`
  set H : Ω → ℝ := fun ω =>
    ∫ s in Set.Ioc 0 T, Kdom * Real.exp (lam * |B s ω|) ∂ItoIntegralL2.timeMeasure with hHdef
  have hHmemLp : MemLp H 2 μ :=
    pathIntegral_expGrowth_memLp hB hBmeas T
      (w := fun _ x => Kdom * Real.exp (lam * |x|))
      (fun s => (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_abs))).measurable)
      hKdom0 (fun s x => by rw [abs_of_nonneg (mul_nonneg hKdom0 (Real.exp_nonneg _))])
      (fun ω => continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul ((continuous_abs).comp (hBcont ω)))))
  -- `|driftCut n ω − drift ω| ≤ H ω`
  have hHbound : ∀ n ω, |driftCut n ω - drift ω| ≤ H ω := by
    intro n ω
    obtain ⟨Mω, hMω⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      (hBcont ω).continuousOn
    have habs_Bω : ∀ s ∈ Set.Ioc (0 : ℝ≥0) T, |B s ω| ≤ Mω := fun s hs => by
      have := hMω s ⟨zero_le, hs.2⟩; rwa [Real.norm_eq_abs] at this
    have hintJn : IntegrableOn (Jn n ω) (Set.Ioc 0 T) ItoIntegralL2.timeMeasure := by
      refine Integrable.mono' (integrable_const (K1 * Real.exp (lam * Mω)))
        (hJn_cont n ω).aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).mpr
          (ae_of_all _ fun s hs => ?_))
      rw [Real.norm_eq_abs]
      exact (hJn_bound n ω s).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (habs_Bω s hs) hlam)) hK1_0)
    have hintJl : IntegrableOn (Jl ω) (Set.Ioc 0 T) ItoIntegralL2.timeMeasure := by
      refine Integrable.mono' (integrable_const (C * (1 + 1 / 2) * Real.exp (lam * Mω)))
        (hJl_cont ω).aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioc).mpr
          (ae_of_all _ fun s hs => ?_))
      rw [Real.norm_eq_abs, hJl]
      have hb : |f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω)|
          ≤ C * Real.exp (lam * |B s ω|) + (1 / 2) * (C * Real.exp (lam * |B s ω|)) := by
        refine (abs_add_le _ _).trans (add_le_add (hg_t _ _) ?_)
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
        exact mul_le_mul_of_nonneg_left (hg_xx _ _) (by norm_num)
      refine hb.trans ?_
      have hmono : Real.exp (lam * |B s ω|) ≤ Real.exp (lam * Mω) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (habs_Bω s hs) hlam)
      nlinarith [hmono, hC0, Real.exp_nonneg (lam * |B s ω|), Real.exp_nonneg (lam * Mω)]
    have hintH : IntegrableOn (fun s => Kdom * Real.exp (lam * |B s ω|))
        (Set.Ioc 0 T) ItoIntegralL2.timeMeasure := by
      refine Integrable.mono' (integrable_const (Kdom * Real.exp (lam * Mω)))
        (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
          ((continuous_abs).comp (hBcont ω))))).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hKdom0 (Real.exp_nonneg _))]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (habs_Bω s hs) hlam)) hKdom0
    calc |driftCut n ω - drift ω|
        = |∫ s in Set.Ioc 0 T, (Jn n ω s - Jl ω s) ∂ItoIntegralL2.timeMeasure| := by
          rw [hdriftCut, hdrift, integral_sub hintJn hintJl]
      _ ≤ ∫ s in Set.Ioc 0 T, |Jn n ω s - Jl ω s| ∂ItoIntegralL2.timeMeasure :=
          abs_integral_le_integral_abs
      _ ≤ ∫ s in Set.Ioc 0 T, Kdom * Real.exp (lam * |B s ω|) ∂ItoIntegralL2.timeMeasure := by
          refine integral_mono_of_nonneg (ae_of_all _ fun s => abs_nonneg _)
            hintH ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs => ?_))
          calc |Jn n ω s - Jl ω s| ≤ |Jn n ω s| + |Jl ω s| := by
                rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
            _ ≤ K1 * Real.exp (lam * |B s ω|)
                + C * (1 + 1 / 2) * Real.exp (lam * |B s ω|) := by
                refine add_le_add (hJn_bound n ω s) ?_
                rw [hJl]
                refine (abs_add_le _ _).trans ?_
                rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
                nlinarith [hg_t (s:ℝ) (B s ω), hg_xx (s:ℝ) (B s ω),
                  Real.exp_nonneg (lam * |B s ω|), hC0]
            _ = Kdom * Real.exp (lam * |B s ω|) := by rw [hKdom]; ring
      _ = H ω := by rw [hHdef]
  -- measurability of the path integrals (via the exposed `measurable_pathIntegral`)
  have hJn_meas : ∀ n s, Measurable (fun ω => Jn n ω s) := by
    intro n s
    have hcomp : ∀ g : ℝ → ℝ → ℝ, Continuous (fun p : ℝ × ℝ => g p.1 p.2) →
        Measurable (fun ω => g (s : ℝ) (S.cut n (B s ω))) := fun g hg =>
      (((hg.comp (continuous_const.prodMk continuous_id)).comp
        (S.continuous_cut n)).measurable).comp (hBmeas s)
    have hd1 : Measurable (fun ω => S.cutD1 n (B s ω)) :=
      (S.continuous_cutD1 n).measurable.comp (hBmeas s)
    have hd2 : Measurable (fun ω => S.cutD2 n (B s ω)) :=
      (S.continuous_cutD2 n).measurable.comp (hBmeas s)
    rw [hJn]
    exact (hcomp f_t hf_t_cont).add
      (((((hcomp f_xx hf_xx_cont).mul (hd1.pow_const 2)).add
        ((hcomp f_x hf_x_cont).mul hd2))).const_mul (1 / 2))
  have hJl_meas : ∀ s, Measurable (fun ω => Jl ω s) := by
    intro s
    have hcomp : ∀ g : ℝ → ℝ → ℝ, Continuous (fun p : ℝ × ℝ => g p.1 p.2) →
        Measurable (fun ω => g (s : ℝ) (B s ω)) := fun g hg =>
      ((hg.comp (continuous_const.prodMk continuous_id)).measurable).comp (hBmeas s)
    rw [hJl]
    exact (hcomp f_t hf_t_cont).add ((hcomp f_xx hf_xx_cont).const_mul (1 / 2))
  have hdriftCut_meas : ∀ n, Measurable (driftCut n) := fun n => by
    rw [hdriftCut]
    exact measurable_pathIntegral (w := fun s ω => Jn n ω s) (fun s => hJn_meas n s)
      (fun ω => hJn_cont n ω) T
  have hdrift_meas : Measurable drift := by
    rw [hdrift]
    exact measurable_pathIntegral (w := fun s ω => Jl ω s) (fun s => hJl_meas s)
      (fun ω => hJl_cont ω) T
  -- outer dominated convergence
  have hGint : Integrable (fun ω => (H ω) ^ 2) μ := by
    have hsq : (fun ω => (H ω) ^ 2) = fun ω => H ω * H ω := by funext ω; ring
    rw [hsq]; exact hHmemLp.integrable_mul hHmemLp
  have key := tendsto_integral_of_dominated_convergence
    (F := fun n ω => (driftCut n ω - drift ω) ^ 2) (f := fun _ : Ω => (0 : ℝ))
    (bound := fun ω => (H ω) ^ 2)
    (fun n => (((hdriftCut_meas n).sub hdrift_meas).pow_const 2).aestronglyMeasurable) hGint
    (fun n => ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (driftCut n ω - drift ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hHbound n ω) 2)
    (ae_of_all _ fun ω => by
      have h := ((hinner ω).sub_const (drift ω)).pow 2; simpa using h)
  simpa using key

/-- **The localized (exponential-growth) time-dependent Itô formula.** For `f` whose six
partials are of at-most-exponential growth (`|f_• t x| ≤ C·exp(λ|x|)`) — so it reaches GBM's
`exp(σx)` value function, which `ito_formula_td_L2_bddDeriv` cannot — the same conclusion
holds: `f(T,B_T) − f(0,B_0) =ᵐ ∫ f_x dB + ∫₀ᵀ (f_t + ½f_xx) ds`, with the stochastic integral
realized by `itoIntegralCLM_T`. The proof cuts `f` by the smooth truncation `φₙ`, applies the
bounded engine to each `fₙ` (`cutoff_bddDeriv`), and passes `n → ∞`: the boundary and drift
terms converge in `L²(μ)` (`boundary_tendsto_L2`, `drift_tendsto_L2`), so `aₙ = itoIntegralCLM_T
gfxₙ` is Cauchy; the Itô **isometry** transfers Cauchy-ness to `(gfxₙ)`, completeness gives the
witness `gfxInf`, and CLM **continuity** identifies its image with the limit. The bounded case is
the special case `λ = 0`; this is a drop-in for `ito_formula_td_L2_bddDeriv` (it additionally
asks `f_t` to be jointly continuous, which exponential growth — unlike a global bound — does not
supply). -/
theorem ito_formula_td_localized
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω)
    (T : ℝ≥0) {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s => f s x) (f_t t x) t)
    (hf_tt : ∀ t x, HasDerivAt (fun s => f_t s x) (f_tt t x) t)
    (hf_tx : ∀ t x, HasDerivAt (fun u => f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u => f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u => f_x t u) (f_xx t x) x)
    (hf_xxx : ∀ t x, HasDerivAt (fun u => f_xx t u) (f_xxx t x) x)
    (hf_t_cont : Continuous fun p : ℝ × ℝ => f_t p.1 p.2)
    (hf_x_cont : Continuous fun p : ℝ × ℝ => f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ => f_xx p.1 p.2)
    {C lam : ℝ} (hlam : 0 ≤ lam)
    (hg_t : ∀ t x, |f_t t x| ≤ C * Real.exp (lam * |x|))
    (hg_x : ∀ t x, |f_x t x| ≤ C * Real.exp (lam * |x|))
    (hg_xx : ∀ t x, |f_xx t x| ≤ C * Real.exp (lam * |x|))
    (hg_tt : ∀ t x, |f_tt t x| ≤ C * Real.exp (lam * |x|))
    (hg_tx : ∀ t x, |f_tx t x| ≤ C * Real.exp (lam * |x|))
    (hg_xxx : ∀ t x, |f_xxx t x| ≤ C * Real.exp (lam * |x|)) :
    ∃ gfx : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω => f T (B T ω) - f 0 (B 0 ω)) =ᵐ[μ]
        (fun ω => (itoIntegralCLM_T hB T hBmeas gfx) ω
          + ∫ s in Set.Ioc 0 T,
              (f_t s (B s ω) + (1 / 2) * f_xx s (B s ω)) ∂ItoIntegralL2.timeMeasure) := by
  classical
  have hcont_f : ∀ t : ℝ, Continuous (fun x => f t x) := fun t =>
    Differentiable.continuous fun x => (hf_x t x).differentiableAt
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (by simpa using hg_x 0 0)
  obtain ⟨S⟩ := smoothTrunc_exists
  choose gfx hid using fun n => cutoff_bddDeriv hB hBmeas hBcont T S n hf_t hf_tt hf_tx hf_x hf_xx
    hf_xxx hf_x_cont hf_xx_cont hlam hg_t hg_x hg_xx hg_tt hg_tx hg_xxx
  -- `L²` membership of the boundary terms, via the `f`-value growth bound
  have hfeval : ∀ (t : ℝ) (r : ℝ≥0) (g : Ω → ℝ), Measurable g → (∀ ω, |g ω| ≤ |B r ω|) →
      MemLp (fun ω => f t (g ω)) 2 μ := by
    intro t r g hg_meas hg_le
    refine MemLp.mono ((memLp_const (|f t 0|)).add
      ((memLp_exp_abs_eval hB r (lam + 1)).const_mul C))
      ((hcont_f t).measurable.comp hg_meas).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_le_of_expGrowth_deriv hf_x hlam hg_x t (g ω)).trans ?_
    have hmono : Real.exp ((lam + 1) * |g ω|) ≤ Real.exp ((lam + 1) * |B r ω|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hg_le ω) (by linarith))
    calc |f t 0| + C * Real.exp ((lam + 1) * |g ω|)
        ≤ |f t 0| + C * Real.exp ((lam + 1) * |B r ω|) := by
          linarith [mul_le_mul_of_nonneg_left hmono hC0]
      _ ≤ ‖|f t 0| + C * Real.exp ((lam + 1) * |B r ω|)‖ := le_abs_self _
  have hbdy_memLp : MemLp (fun ω => f T (B T ω) - f 0 (B 0 ω)) 2 μ :=
    (hfeval (T : ℝ) T (fun ω => B T ω) (hBmeas T) (fun _ => le_refl _)).sub
      (hfeval (0 : ℝ) 0 (fun ω => B 0 ω) (hBmeas 0) (fun _ => le_refl _))
  have hbdyCut_memLp : ∀ n, MemLp (fun ω => fCut f S n T (B T ω) - fCut f S n 0 (B 0 ω)) 2 μ :=
    fun n => (hfeval (T : ℝ) T (fun ω => S.cut n (B T ω))
        ((S.continuous_cut n).measurable.comp (hBmeas T)) (fun ω => S.cut_le_abs n (B T ω))).sub
      (hfeval (0 : ℝ) 0 (fun ω => S.cut n (B 0 ω))
        ((S.continuous_cut n).measurable.comp (hBmeas 0)) (fun ω => S.cut_le_abs n (B 0 ω)))
  -- `L²` membership of the drift terms, via the exp-growth path integral
  have hM2 : 0 ≤ S.M₂ := le_trans (abs_nonneg _) (S.bdd₂ 0)
  have hdrift_memLp :
      MemLp (fun ω => ∫ s in Set.Ioc 0 T, (f_t s (B s ω) + (1 / 2) * f_xx s (B s ω))
        ∂ItoIntegralL2.timeMeasure) 2 μ :=
    pathIntegral_expGrowth_memLp hB hBmeas T (w := fun s x => f_t (s : ℝ) x + (1 / 2) * f_xx (s : ℝ) x)
      (fun s => ((hf_t_cont.comp (continuous_const.prodMk continuous_id)).measurable).add
        (((hf_xx_cont.comp (continuous_const.prodMk continuous_id)).measurable).const_mul (1 / 2)))
      (by positivity : (0 : ℝ) ≤ C * (1 + 1 / 2))
      (fun s x => by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        calc |f_t (s : ℝ) x| + 1 / 2 * |f_xx (s : ℝ) x|
            ≤ C * Real.exp (lam * |x|) + 1 / 2 * (C * Real.exp (lam * |x|)) :=
              add_le_add (hg_t s x) (mul_le_mul_of_nonneg_left (hg_xx s x) (by norm_num))
          _ = C * (1 + 1 / 2) * Real.exp (lam * |x|) := by ring)
      (fun ω => ((hf_t_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))).add
        (continuous_const.mul (hf_xx_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))))))
  have hdriftCut_memLp : ∀ n, MemLp (fun ω => ∫ s in Set.Ioc 0 T,
      (f_t s (S.cut n (B s ω)) + (1 / 2) * (f_xx s (S.cut n (B s ω)) * S.cutD1 n (B s ω) ^ 2
          + f_x s (S.cut n (B s ω)) * S.cutD2 n (B s ω))) ∂ItoIntegralL2.timeMeasure) 2 μ := by
    intro n
    refine pathIntegral_expGrowth_memLp hB hBmeas T (c := lam)
      (w := fun s x => f_t (s : ℝ) (S.cut n x) + (1 / 2) * (f_xx (s : ℝ) (S.cut n x)
        * S.cutD1 n x ^ 2 + f_x (s : ℝ) (S.cut n x) * S.cutD2 n x))
      (fun s => (((hf_t_cont.comp (continuous_const.prodMk continuous_id)).comp
          (S.continuous_cut n)).measurable.comp measurable_id).add
        ((((((hf_xx_cont.comp (continuous_const.prodMk continuous_id)).comp
              (S.continuous_cut n)).measurable.comp measurable_id).mul
            ((S.continuous_cutD1 n).measurable.pow_const 2)).add
          ((((hf_x_cont.comp (continuous_const.prodMk continuous_id)).comp
              (S.continuous_cut n)).measurable.comp measurable_id).mul
            (S.continuous_cutD2 n).measurable)).const_mul (1 / 2)))
      (by positivity : (0 : ℝ) ≤ C * (1 + (1 / 2) * S.M₁ ^ 2 + (1 / 2) * S.M₂)) ?_ ?_
    · intro s x
      set Ec : ℝ := Real.exp (lam * |S.cut n x|) with hEc
      have hCEc0 : 0 ≤ C * Ec := mul_nonneg hC0 (Real.exp_nonneg _)
      have hcut : Ec ≤ Real.exp (lam * |x|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (S.cut_le_abs n x) hlam)
      have hd1 : S.cutD1 n x ^ 2 ≤ S.M₁ ^ 2 := by
        rw [← sq_abs (S.cutD1 n x)]; exact pow_le_pow_left₀ (abs_nonneg _) (S.cutD1_bdd n _) 2
      calc |f_t (s : ℝ) (S.cut n x) + (1 / 2) * (f_xx (s : ℝ) (S.cut n x) * S.cutD1 n x ^ 2
              + f_x (s : ℝ) (S.cut n x) * S.cutD2 n x)|
          ≤ C * Ec + (1 / 2) * (C * Ec * S.M₁ ^ 2 + C * Ec * S.M₂) := by
            refine (abs_add_le _ _).trans (add_le_add (hg_t s _) ?_)
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ ?_))
              (by norm_num)
            · rw [abs_mul, abs_of_nonneg (sq_nonneg (S.cutD1 n x))]
              exact mul_le_mul (hg_xx s _) hd1 (sq_nonneg _) hCEc0
            · rw [abs_mul]; exact mul_le_mul (hg_x s _) (S.cutD2_bdd n _) (abs_nonneg _) hCEc0
        _ = C * (1 + (1 / 2) * S.M₁ ^ 2 + (1 / 2) * S.M₂) * Ec := by ring
        _ ≤ C * (1 + (1 / 2) * S.M₁ ^ 2 + (1 / 2) * S.M₂) * Real.exp (lam * |x|) :=
            mul_le_mul_of_nonneg_left hcut (by positivity)
    · intro ω
      have hpair : Continuous fun s : ℝ≥0 => ((s : ℝ), S.cut n (B s ω)) :=
        NNReal.continuous_coe.prodMk ((S.continuous_cut n).comp (hBcont ω))
      exact (hf_t_cont.comp hpair).add (continuous_const.mul (((hf_xx_cont.comp hpair).mul
        (((S.continuous_cutD1 n).comp (hBcont ω)).pow 2)).add
        ((hf_x_cont.comp hpair).mul ((S.continuous_cutD2 n).comp (hBcont ω)))))
  -- lift the two `L²` convergences to `Lp`-norm convergence
  have hbdyCut_tendsto : Tendsto (fun n => (hbdyCut_memLp n).toLp _) atTop
      (𝓝 (hbdy_memLp.toLp _)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (ItoIntegralRiemannBridge.tendsto_norm_toLp_sub' hbdyCut_memLp hbdy_memLp
      (boundary_tendsto_L2 hB hBmeas T S hf_x hlam hg_x))
  have hdriftCut_tendsto : Tendsto (fun n => (hdriftCut_memLp n).toLp _) atTop
      (𝓝 (hdrift_memLp.toLp _)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (ItoIntegralRiemannBridge.tendsto_norm_toLp_sub' hdriftCut_memLp hdrift_memLp
      (drift_tendsto_L2 hB hBmeas hBcont T S hf_t_cont hf_x_cont hf_xx_cont hlam hg_t hg_x hg_xx))
  -- `aₙ = itoIntegralCLM_T gfxₙ = bdyCutₙ − driftCutₙ` in `Lp`, hence converges, hence Cauchy
  have ha_eq : ∀ n, itoIntegralCLM_T hB T hBmeas (gfx n)
      = (hbdyCut_memLp n).toLp _ - (hdriftCut_memLp n).toLp _ := by
    intro n
    refine Lp.ext ?_
    filter_upwards [hid n, (hbdyCut_memLp n).coeFn_toLp, (hdriftCut_memLp n).coeFn_toLp,
      Lp.coeFn_sub ((hbdyCut_memLp n).toLp _) ((hdriftCut_memLp n).toLp _)] with ω h1 h2 h3 h4
    rw [h4, Pi.sub_apply, h2, h3]; linarith [h1]
  have ha_tendsto : Tendsto (fun n => itoIntegralCLM_T hB T hBmeas (gfx n)) atTop
      (𝓝 (hbdy_memLp.toLp _ - hdrift_memLp.toLp _)) := by
    refine (tendsto_congr ha_eq).mpr (hbdyCut_tendsto.sub hdriftCut_tendsto)
  have hgfx_cauchy : CauchySeq gfx := by
    have ha_cauchy := ha_tendsto.cauchySeq
    rw [Metric.cauchySeq_iff] at ha_cauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := ha_cauchy ε hε
    refine ⟨N, fun m hm k hk => ?_⟩
    have hdist : dist (gfx m) (gfx k)
        = dist (itoIntegralCLM_T hB T hBmeas (gfx m)) (itoIntegralCLM_T hB T hBmeas (gfx k)) := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, itoIntegralCLM_T_norm]
    rw [hdist]; exact hN m hm k hk
  obtain ⟨gfxInf, hgfxInf⟩ := cauchySeq_tendsto_of_complete hgfx_cauchy
  refine ⟨gfxInf, ?_⟩
  -- CLM continuity ⇒ `itoIntegralCLM_T gfxInf = bdy − drift`
  have hJ : itoIntegralCLM_T hB T hBmeas gfxInf = hbdy_memLp.toLp _ - hdrift_memLp.toLp _ :=
    tendsto_nhds_unique
      (((itoIntegralCLM_T hB T hBmeas).continuous.tendsto gfxInf).comp hgfxInf) ha_tendsto
  -- unfold to the a.e. identity
  have hbdy_eq : hbdy_memLp.toLp _
      = itoIntegralCLM_T hB T hBmeas gfxInf + hdrift_memLp.toLp _ := eq_add_of_sub_eq hJ.symm
  have key : (fun ω => f T (B T ω) - f 0 (B 0 ω)) =ᵐ[μ] ⇑(hbdy_memLp.toLp _) :=
    hbdy_memLp.coeFn_toLp.symm
  rw [hbdy_eq] at key
  filter_upwards [key, Lp.coeFn_add (itoIntegralCLM_T hB T hBmeas gfxInf) (hdrift_memLp.toLp _),
    hdrift_memLp.coeFn_toLp] with ω hk hadd hdc
  rw [hk, hadd, Pi.add_apply, hdc]

end MathFin
