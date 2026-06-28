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

lemma continuous_φ (S : SmoothTrunc) : Continuous S.φ :=
  Differentiable.continuous fun x => (S.hasDeriv₁ x).differentiableAt

lemma continuous_cut (S : SmoothTrunc) (n : ℕ) : Continuous (S.cut n) :=
  continuous_const.mul (S.continuous_φ.comp (continuous_id.div_const _))

end SmoothTrunc

/-- The cutoff function `fₙ(t, x) = f(t, φₙ(x))`. -/
noncomputable def fCut (f : ℝ → ℝ → ℝ) (S : SmoothTrunc) (n : ℕ) (t x : ℝ) : ℝ :=
  f t (S.cut n x)

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

end MathFin
