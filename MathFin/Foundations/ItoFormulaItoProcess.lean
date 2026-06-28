/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaLocalized

/-! # Itô formula against a (constant-coefficient) Itô process

For an Itô process with constant coefficients

  `X_t = X₀ + b·t + σ·B_t`     (drift `b`, diffusion `σ`, `B` a pre-Brownian motion)

and a `C³` function `f` of at-most-exponential growth, the Itô formula reads

  `f(X_T) − f(X₀) =ᵐ ∫₀ᵀ f'(X_s)·σ dB_s + ∫₀ᵀ (f'(X_s)·b + ½ f''(X_s)·σ²) ds`,

where the stochastic term is the genuine continuous Itô integral `itoIntegralCLM_T`. Grouping
`∫ f'(X)·b ds + ∫ f'(X)·σ dB = ∫ f'(X) dX` exhibits the classical shape
`f(X_T) − f(X₀) = ∫ f'(X) dX + ½∫ f''(X)·σ² ds`.

This generalizes `ito_formula_gbm` (the `f = S₀·exp` / `b = m−σ²/2` case) from the exponential
value function to an arbitrary `C³` exponential-growth `f`. The route is identical: the inner
exponent `b·t` is `t`-unbounded, so the localized formula is applied to the **time-localized**
inner map `(t, x) ↦ X₀ + b·φₙ(t) + σx` (`φₙ = SmoothTrunc.cut n`, `n = ⌈T⌉₊`), the identity on
`[0, T]` yet globally bounded, so the exponential-in-`x` growth bounds hold uniformly in time; on
`[0, T]` the cutoff drops out (`φₙ = id`, `φₙ' = 1`). Constant coefficients keep the diffusion
integrand `f'(X_s)·σ` a function of `B_s`, which the tower handles directly; general adapted
coefficients (the full semimartingale Itô formula, needing the Itô integral against random
integrands) remain the open frontier.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- **Itô formula for a constant-coefficient Itô process `X_t = X₀ + b·t + σ B_t`.** For a `C³`
function `f` whose derivatives are of at-most-exponential growth (`|f^{(k)} x| ≤ C·exp(λ|x|)`,
`k = 1,2,3`),

  `f(X_T) − f(X₀) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ (f'(X_s)·b + ½·f''(X_s)·σ²) ds`,

with the trim-`L²` integrand `gfx` realizing the diffusion `s ↦ σ·f'(X_s)` and the genuine
continuous Itô integral `itoIntegralCLM_T` carrying it. Together with the drift's `f'(X_s)·b`
term this is `f(X_T) − f(X₀) = ∫₀ᵀ f'(X_s) dX_s + ½∫₀ᵀ f''(X_s)·σ² ds`. The instantiation of
`ito_formula_td_localized` at the time-localized inner map `(t, x) ↦ X₀ + b·φₙ(t) + σx`. -/
theorem ito_formula_itoProcess (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω) (T : ℝ≥0) (X₀ b σ : ℝ)
    {f f' f'' f''' : ℝ → ℝ}
    (hf' : ∀ x, HasDerivAt f (f' x) x) (hf'' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''' : ∀ x, HasDerivAt f'' (f''' x) x)
    {C lam : ℝ} (hlam : 0 ≤ lam)
    (hg' : ∀ x, |f' x| ≤ C * Real.exp (lam * |x|))
    (hg'' : ∀ x, |f'' x| ≤ C * Real.exp (lam * |x|))
    (hg''' : ∀ x, |f''' x| ≤ C * Real.exp (lam * |x|)) :
    ∃ gfx : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω => f (X₀ + b * (T : ℝ) + σ * B T ω) - f (X₀ + b * (0 : ℝ) + σ * B 0 ω)) =ᵐ[μ]
        (fun ω => (itoIntegralCLM_T hB T hBmeas gfx) ω
          + ∫ s in Set.Ioc 0 T,
              (f' (X₀ + b * (s : ℝ) + σ * B s ω) * b
                + (1 / 2) * (f'' (X₀ + b * (s : ℝ) + σ * B s ω) * σ ^ 2))
              ∂ItoIntegralL2.timeMeasure) := by
  obtain ⟨S⟩ := smoothTrunc_exists
  set n : ℕ := ⌈(T : ℝ)⌉₊ with hn
  have hM1 : (0 : ℝ) ≤ S.M₁ := le_trans (abs_nonneg _) (S.bdd₁ 0)
  have hM2 : (0 : ℝ) ≤ S.M₂ := le_trans (abs_nonneg _) (S.bdd₂ 0)
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (by simpa using hg' 0)
  have hTn : (T : ℝ) ≤ (n : ℝ) := by rw [hn]; exact Nat.le_ceil _
  -- the exp-growth constants: `lam' = lam·|σ|`, `K` dominates every `f^{(k)}(X₀+b·φₙ+σx)`,
  -- `C_global = Csum·K` the single bound for all six localized-formula partials
  set lam' : ℝ := lam * |σ| with hlam'
  set K : ℝ := C * Real.exp (lam * (|X₀| + |b| * S.M₀ * ((n : ℝ) + 1))) with hK
  set Csum : ℝ := |b| * S.M₁ + |σ| + σ ^ 2 + (|b| * S.M₂ + b ^ 2 * S.M₁ ^ 2)
      + |b| * |σ| * S.M₁ + |σ| ^ 3 with hCsum
  set Cg : ℝ := Csum * K with hCg
  have hK0 : (0 : ℝ) ≤ K := mul_nonneg hC0 (Real.exp_nonneg _)
  have t1 : (0 : ℝ) ≤ |b| * S.M₁ := mul_nonneg (abs_nonneg _) hM1
  have t2 : (0 : ℝ) ≤ |σ| := abs_nonneg _
  have t3 : (0 : ℝ) ≤ σ ^ 2 := sq_nonneg _
  have t4 : (0 : ℝ) ≤ |b| * S.M₂ + b ^ 2 * S.M₁ ^ 2 :=
    add_nonneg (mul_nonneg (abs_nonneg _) hM2) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have t5 : (0 : ℝ) ≤ |b| * |σ| * S.M₁ := mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hM1
  have t6 : (0 : ℝ) ≤ |σ| ^ 3 := by positivity
  have hCsum_nonneg : (0 : ℝ) ≤ Csum := by rw [hCsum]; linarith [t1, t2, t3, t4, t5, t6]
  have hlam'0 : (0 : ℝ) ≤ lam' := by rw [hlam']; exact mul_nonneg hlam (abs_nonneg _)
  -- `f^{(k)}` evaluated at the localized argument is dominated by `K·exp(lam'|x|)`, uniformly in `t`
  have hfbd : ∀ h : ℝ → ℝ, (∀ x, |h x| ≤ C * Real.exp (lam * |x|)) →
      ∀ t x : ℝ, |h (X₀ + b * S.cut n t + σ * x)| ≤ K * Real.exp (lam' * |x|) := by
    intro h hh t x
    refine (hh _).trans ?_
    have hRHS : K * Real.exp (lam' * |x|)
        = C * Real.exp (lam * (|X₀| + |b| * S.M₀ * ((n : ℝ) + 1)) + lam * |σ| * |x|) := by
      rw [hK, hlam', Real.exp_add]; ring
    rw [hRHS]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
    have harg : |X₀ + b * S.cut n t + σ * x|
        ≤ |X₀| + |b| * S.M₀ * ((n : ℝ) + 1) + |σ| * |x| := by
      calc |X₀ + b * S.cut n t + σ * x| ≤ |X₀ + b * S.cut n t| + |σ * x| := abs_add_le _ _
        _ ≤ |X₀| + |b * S.cut n t| + |σ * x| := by
            have := abs_add_le X₀ (b * S.cut n t); linarith
        _ = |X₀| + |b| * |S.cut n t| + |σ| * |x| := by rw [abs_mul, abs_mul]
        _ ≤ |X₀| + |b| * (S.M₀ * ((n : ℝ) + 1)) + |σ| * |x| := by
            linarith [mul_le_mul_of_nonneg_left (S.cut_bdd n t) (abs_nonneg b)]
        _ = |X₀| + |b| * S.M₀ * ((n : ℝ) + 1) + |σ| * |x| := by ring
    calc lam * |X₀ + b * S.cut n t + σ * x|
        ≤ lam * (|X₀| + |b| * S.M₀ * ((n : ℝ) + 1) + |σ| * |x|) :=
          mul_le_mul_of_nonneg_left harg hlam
      _ = lam * (|X₀| + |b| * S.M₀ * ((n : ℝ) + 1)) + lam * |σ| * |x| := by ring
  -- the slot helper: a `Csum`-bounded coefficient times `f^{(k)}(arg)` is dominated by `Cg`
  have hbound : ∀ (cf h : ℝ → ℝ), (∀ t, |cf t| ≤ Csum) →
      (∀ x, |h x| ≤ C * Real.exp (lam * |x|)) →
      ∀ t x : ℝ, |cf t * h (X₀ + b * S.cut n t + σ * x)| ≤ Cg * Real.exp (lam' * |x|) := by
    intro cf h hcf hh t x
    rw [abs_mul, hCg]
    calc |cf t| * |h (X₀ + b * S.cut n t + σ * x)|
        ≤ Csum * (K * Real.exp (lam' * |x|)) :=
          mul_le_mul (hcf t) (hfbd h hh t x) (abs_nonneg _) hCsum_nonneg
      _ = Csum * K * Real.exp (lam' * |x|) := by ring
  -- the five single-term coefficient bounds `|cf t| ≤ Csum`
  have hcoef_t : ∀ t : ℝ, |b * S.cutD1 n t| ≤ Csum := fun t => by
    rw [abs_mul, hCsum]
    have h := mul_le_mul_of_nonneg_left (S.cutD1_bdd n t) (abs_nonneg b)
    linarith [h, t2, t3, t4, t5, t6]
  have hcoef_x : ∀ _t : ℝ, |σ| ≤ Csum := fun _ => by rw [hCsum]; linarith [t1, t3, t4, t5, t6]
  have hcoef_xx : ∀ _t : ℝ, |σ ^ 2| ≤ Csum := fun _ => by
    rw [abs_of_nonneg (sq_nonneg σ), hCsum]; linarith [t1, t2, t4, t5, t6]
  have hcoef_tx : ∀ t : ℝ, |b * σ * S.cutD1 n t| ≤ Csum := fun t => by
    rw [abs_mul, abs_mul, hCsum]
    have h := mul_le_mul_of_nonneg_left (S.cutD1_bdd n t) (mul_nonneg (abs_nonneg b) (abs_nonneg σ))
    linarith [h, t1, t2, t3, t4, t6]
  have hcoef_xxx : ∀ _t : ℝ, |σ ^ 3| ≤ Csum := fun _ => by
    rw [abs_pow, hCsum]; linarith [t1, t2, t3, t4, t5]
  -- continuity of `f'`, `f''` (from one-higher differentiability) and the inner argument
  have hf'c : Continuous f' := Differentiable.continuous (fun x => (hf'' x).differentiableAt)
  have hf''c : Continuous f'' := Differentiable.continuous (fun x => (hf''' x).differentiableAt)
  have hargc : Continuous fun p : ℝ × ℝ => X₀ + b * S.cut n p.1 + σ * p.2 :=
    (continuous_const.add (continuous_const.mul ((S.continuous_cut n).comp continuous_fst))).add
      (continuous_const.mul continuous_snd)
  -- the clean `x`-exponent derivative (constant inner offset `c`, slope `σ`)
  have hInx : ∀ c y : ℝ, HasDerivAt (fun u => c + σ * u) σ y :=
    fun c y => by simpa using ((hasDerivAt_id y).const_mul σ).const_add c
  obtain ⟨gfx, hgfx⟩ := ito_formula_td_localized hB hBmeas hBcont T
    (f := fun t x => f (X₀ + b * S.cut n t + σ * x))
    (f_t := fun t x => b * S.cutD1 n t * f' (X₀ + b * S.cut n t + σ * x))
    (f_x := fun t x => σ * f' (X₀ + b * S.cut n t + σ * x))
    (f_xx := fun t x => σ ^ 2 * f'' (X₀ + b * S.cut n t + σ * x))
    (f_tt := fun t x => b * S.cutD2 n t * f' (X₀ + b * S.cut n t + σ * x)
      + b ^ 2 * S.cutD1 n t ^ 2 * f'' (X₀ + b * S.cut n t + σ * x))
    (f_tx := fun t x => b * σ * S.cutD1 n t * f'' (X₀ + b * S.cut n t + σ * x))
    (f_xxx := fun t x => σ ^ 3 * f''' (X₀ + b * S.cut n t + σ * x))
    (fun t x => by
      rw [show b * S.cutD1 n t * f' (X₀ + b * S.cut n t + σ * x)
            = f' (X₀ + b * S.cut n t + σ * x) * (b * S.cutD1 n t) by ring]
      exact (hf' (X₀ + b * S.cut n t + σ * x)).comp t
        (((S.cut_hasDerivAt n t).const_mul b).const_add X₀ |>.add_const (σ * x)))
    (fun t x => by
      rw [show b * S.cutD2 n t * f' (X₀ + b * S.cut n t + σ * x)
              + b ^ 2 * S.cutD1 n t ^ 2 * f'' (X₀ + b * S.cut n t + σ * x)
            = b * S.cutD2 n t * f' (X₀ + b * S.cut n t + σ * x)
              + b * S.cutD1 n t * (f'' (X₀ + b * S.cut n t + σ * x) * (b * S.cutD1 n t)) by ring]
      exact ((S.cutD1_hasDerivAt n t).const_mul b).mul
        ((hf'' (X₀ + b * S.cut n t + σ * x)).comp t
          (((S.cut_hasDerivAt n t).const_mul b).const_add X₀ |>.add_const (σ * x))))
    (fun t x => by
      rw [show b * σ * S.cutD1 n t * f'' (X₀ + b * S.cut n t + σ * x)
            = b * S.cutD1 n t * (f'' (X₀ + b * S.cut n t + σ * x) * σ) by ring]
      exact (((hf'' (X₀ + b * S.cut n t + σ * x)).comp x
        (hInx (X₀ + b * S.cut n t) x)).const_mul (b * S.cutD1 n t)))
    (fun t x => by
      rw [show σ * f' (X₀ + b * S.cut n t + σ * x)
            = f' (X₀ + b * S.cut n t + σ * x) * σ by ring]
      exact (hf' (X₀ + b * S.cut n t + σ * x)).comp x (hInx (X₀ + b * S.cut n t) x))
    (fun t x => by
      rw [show σ ^ 2 * f'' (X₀ + b * S.cut n t + σ * x)
            = σ * (f'' (X₀ + b * S.cut n t + σ * x) * σ) by ring]
      exact ((hf'' (X₀ + b * S.cut n t + σ * x)).comp x
        (hInx (X₀ + b * S.cut n t) x)).const_mul σ)
    (fun t x => by
      rw [show σ ^ 3 * f''' (X₀ + b * S.cut n t + σ * x)
            = σ ^ 2 * (f''' (X₀ + b * S.cut n t + σ * x) * σ) by ring]
      exact ((hf''' (X₀ + b * S.cut n t + σ * x)).comp x
        (hInx (X₀ + b * S.cut n t) x)).const_mul (σ ^ 2))
    ((continuous_const.mul ((S.continuous_cutD1 n).comp continuous_fst)).mul (hf'c.comp hargc))
    (continuous_const.mul (hf'c.comp hargc))
    (continuous_const.mul (hf''c.comp hargc))
    (lam := lam') (C := Cg) hlam'0
    (fun t x => hbound (fun t => b * S.cutD1 n t) f' hcoef_t hg' t x)
    (fun t x => hbound (fun _ => σ) f' hcoef_x hg' t x)
    (fun t x => hbound (fun _ => σ ^ 2) f'' hcoef_xx hg'' t x)
    (fun t x => by
      refine (abs_add_le _ _).trans ?_
      rw [hCg]
      have hKe : (0 : ℝ) ≤ K * Real.exp (lam' * |x|) := mul_nonneg hK0 (Real.exp_nonneg _)
      have e1 : |b * S.cutD2 n t * f' (X₀ + b * S.cut n t + σ * x)|
          ≤ |b| * S.M₂ * (K * Real.exp (lam' * |x|)) := by
        rw [abs_mul]
        refine mul_le_mul ?_ (hfbd f' hg' t x) (abs_nonneg _) (mul_nonneg (abs_nonneg _) hM2)
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (S.cutD2_bdd n t) (abs_nonneg b)
      have e2 : |b ^ 2 * S.cutD1 n t ^ 2 * f'' (X₀ + b * S.cut n t + σ * x)|
          ≤ b ^ 2 * S.M₁ ^ 2 * (K * Real.exp (lam' * |x|)) := by
        rw [abs_mul]
        refine mul_le_mul ?_ (hfbd f'' hg'' t x) (abs_nonneg _)
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        rw [abs_mul, abs_of_nonneg (sq_nonneg b), abs_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (S.cutD1_bdd n t) 2) (sq_nonneg b)
      have hsum_le : |b| * S.M₂ + b ^ 2 * S.M₁ ^ 2 ≤ Csum := by
        rw [hCsum]; linarith [t1, t2, t3, t5, t6]
      calc |b * S.cutD2 n t * f' (X₀ + b * S.cut n t + σ * x)|
            + |b ^ 2 * S.cutD1 n t ^ 2 * f'' (X₀ + b * S.cut n t + σ * x)|
          ≤ |b| * S.M₂ * (K * Real.exp (lam' * |x|))
            + b ^ 2 * S.M₁ ^ 2 * (K * Real.exp (lam' * |x|)) := add_le_add e1 e2
        _ = (|b| * S.M₂ + b ^ 2 * S.M₁ ^ 2) * (K * Real.exp (lam' * |x|)) := by ring
        _ ≤ Csum * (K * Real.exp (lam' * |x|)) := mul_le_mul_of_nonneg_right hsum_le hKe
        _ = Csum * K * Real.exp (lam' * |x|) := by ring)
    (fun t x => hbound (fun t => b * σ * S.cutD1 n t) f'' hcoef_tx hg'' t x)
    (fun t x => hbound (fun _ => σ ^ 3) f''' hcoef_xxx hg''' t x)
  -- reduce off `[0, T]`: the cutoff is the identity, with unit slope
  refine ⟨gfx, ?_⟩
  filter_upwards [hgfx] with ω hω
  rw [S.cut_eq_id_of_abs_le (x := (T : ℝ)) (by rw [abs_of_nonneg (NNReal.coe_nonneg T)]; linarith),
      S.cut_eq_id_of_abs_le (x := (0 : ℝ)) (by rw [abs_zero]; positivity)] at hω
  rw [hω, add_right_inj]
  refine integral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs => ?_))
  have hsn : (s : ℝ) ≤ (n : ℝ) := le_trans (by exact_mod_cast hs.2) hTn
  dsimp only
  rw [S.cut_eq_id_of_abs_le (x := (s : ℝ)) (by rw [abs_of_nonneg (NNReal.coe_nonneg s)]; linarith),
      S.cutD1_eq_one_of_abs_lt (x := (s : ℝ)) (by rw [abs_of_nonneg (NNReal.coe_nonneg s)]; linarith)]
  ring

end MathFin
