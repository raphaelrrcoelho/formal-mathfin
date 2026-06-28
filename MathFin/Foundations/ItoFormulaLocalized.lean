/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaTD
-- NOTE: `public import MathFin.Foundations.BrownianExpMoment` is added at Task 4
-- (the first consumer of the exponential moments); deferred so Tasks 2-3 check
-- against the already-built oleans without a daemon restart.

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

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM
open scoped NNReal Topology

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
    _ ≤ S.M₂ * ((n : ℝ) + 1) := by nlinarith [hM, hn]

lemma cutD3_bdd (S : SmoothTrunc) (n : ℕ) (x : ℝ) : |S.cutD3 n x| ≤ S.M₃ := by
  have hM : 0 ≤ S.M₃ := le_trans (abs_nonneg _) (S.bdd₃ 0)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [cutD3, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2),
    div_le_iff₀ (by positivity)]
  calc |S.φ''' (x / ((n : ℝ) + 1))| ≤ S.M₃ := S.bdd₃ _
    _ ≤ S.M₃ * ((n : ℝ) + 1) ^ 2 := by
        nlinarith [mul_nonneg hM (mul_nonneg hn hn), mul_nonneg hM hn]

lemma continuous_cutD1 (S : SmoothTrunc) (n : ℕ) : Continuous (S.cutD1 n) :=
  S.cont₁.comp (continuous_id.div_const _)

lemma continuous_cutD2 (S : SmoothTrunc) (n : ℕ) : Continuous (S.cutD2 n) :=
  (S.cont₂.comp (continuous_id.div_const _)).div_const _

end SmoothTrunc

end MathFin
