/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaItoProcess

/-! # Itô formula for the exponential of Brownian motion — the GBM building block

The localized Itô formula `ito_formula_td_localized` applied to the (time-independent,
exponential-growth) value function `f(t, x) = exp(σx)` gives the Itô decomposition of
`exp(σ B_t)` — the diffusion core of geometric Brownian motion
`S_t = S₀ exp((r − σ²/2)t + σ B_t)`:

  `exp(σ B_T) − exp(σ B_0) =ᵐ ∫₀ᵀ σ·exp(σ B_s) dB_s + ∫₀ᵀ ½σ²·exp(σ B_s) ds`,

with the stochastic integral the genuine continuous Itô integral `itoIntegralCLM_T`. This is
the **first pricing-ward consumer of the analytic Itô tower** (which until now had none): the
diffusion `exp(σ B)` is decomposed by the real Itô integral, not an algebraic drift or a heat
kernel. It is the rung from which the discounted-GBM martingale — whose `−σ²/2` Itô correction
makes the drift vanish — is to be re-grounded on the Itô integral.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM
open scoped NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- **Itô formula for `exp(σ·B)`.** For a pre-Brownian motion `B` with continuous paths,
`exp(σ B_T) − exp(σ B_0) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ ½σ²·exp(σ B_s) ds`, where the
trim-`L²` integrand `gfx` realizes `s ↦ σ·exp(σ B_s)`. The instantiation of
`ito_formula_td_localized` at the time-independent exponential-growth value function
`f(t, x) = exp(σx)` (whose partials `f_x = σ exp(σx)`, `f_xx = σ² exp(σx)` are unbounded —
out of reach of the bounded-derivative formula — but of exponential growth). -/
theorem ito_formula_expBrownian (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω) (T : ℝ≥0) (σ : ℝ) :
    ∃ gfx : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω => Real.exp (σ * B T ω) - Real.exp (σ * B 0 ω)) =ᵐ[μ]
        (fun ω => (itoIntegralCLM_T hB T hBmeas gfx) ω
          + ∫ s in Set.Ioc 0 T, (1 / 2) * (σ ^ 2 * Real.exp (σ * B s ω))
              ∂ItoIntegralL2.timeMeasure) := by
  -- the exponential-growth bound constant `C = |σ|³ + σ² + |σ|` dominates every partial
  set C : ℝ := |σ| ^ 3 + σ ^ 2 + |σ| with hC
  have hexpσ : ∀ x : ℝ, Real.exp (σ * x) ≤ Real.exp (|σ| * |x|) := fun x =>
    Real.exp_le_exp.mpr (le_trans (le_abs_self _) (by rw [abs_mul]))
  -- the six exp-growth bounds, with a single `C`, `lam = |σ|`
  have hbd : ∀ (k : ℝ), |k| ≤ C → ∀ x : ℝ,
      |k * Real.exp (σ * x)| ≤ C * Real.exp (|σ| * |x|) := by
    intro k hk x
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hk (hexpσ x) (Real.exp_nonneg _) (le_trans (abs_nonneg _) hk)
  have hkx : |σ| ≤ C := by rw [hC]; nlinarith [abs_nonneg σ, sq_nonneg σ, sq_abs σ]
  have hkxx : |σ ^ 2| ≤ C := by
    rw [hC, abs_pow, sq_abs]; nlinarith [abs_nonneg σ, pow_nonneg (abs_nonneg σ) 3, sq_nonneg σ]
  have hkxxx : |σ ^ 3| ≤ C := by
    rw [hC, abs_pow]; nlinarith [abs_nonneg σ, sq_nonneg σ, sq_abs σ, pow_nonneg (abs_nonneg σ) 3]
  have hlin : ∀ x : ℝ, HasDerivAt (fun u => σ * u) σ x :=
    fun x => by simpa using (hasDerivAt_id x).const_mul σ
  obtain ⟨gfx, hgfx⟩ := ito_formula_td_localized hB hBmeas hBcont T
    (f := fun _ x => Real.exp (σ * x)) (f_t := fun _ _ => 0)
    (f_x := fun _ x => σ * Real.exp (σ * x)) (f_xx := fun _ x => σ ^ 2 * Real.exp (σ * x))
    (f_tt := fun _ _ => 0) (f_tx := fun _ _ => 0)
    (f_xxx := fun _ x => σ ^ 3 * Real.exp (σ * x))
    (fun t x => hasDerivAt_const t _) (fun t x => hasDerivAt_const t _)
    (fun t x => hasDerivAt_const x _)
    (fun t x => by
      rw [show σ * Real.exp (σ * x) = Real.exp (σ * x) * σ by ring]
      exact (hlin x).exp)
    (fun t x => by
      rw [show σ ^ 2 * Real.exp (σ * x) = σ * (Real.exp (σ * x) * σ) by ring]
      exact ((hlin x).exp).const_mul σ)
    (fun t x => by
      rw [show σ ^ 3 * Real.exp (σ * x) = σ ^ 2 * (Real.exp (σ * x) * σ) by ring]
      exact ((hlin x).exp).const_mul (σ ^ 2))
    continuous_const
    ((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).const_mul σ)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).const_mul (σ ^ 2))
    (lam := |σ|) (C := C) (abs_nonneg σ)
    (fun t x => by simpa using mul_nonneg (le_trans (abs_nonneg _) hkx) (Real.exp_nonneg _))
    (fun t x => hbd σ hkx x) (fun t x => hbd (σ ^ 2) hkxx x)
    (fun t x => by simpa using mul_nonneg (le_trans (abs_nonneg _) hkx) (Real.exp_nonneg _))
    (fun t x => by simpa using mul_nonneg (le_trans (abs_nonneg _) hkx) (Real.exp_nonneg _))
    (fun t x => hbd (σ ^ 3) hkxxx x)
  refine ⟨gfx, ?_⟩
  filter_upwards [hgfx] with ω hω
  rw [hω, add_right_inj]
  exact integral_congr_ae (ae_of_all _ fun s => zero_add _)

/-- **Itô formula for geometric Brownian motion.** For the GBM value function
`Ŝ(t) = S₀ exp((m − σ²/2)t + σ B_t)`,

  `Ŝ(T) − Ŝ(0) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ m·Ŝ(s) ds`,

with the genuine continuous Itô integral `itoIntegralCLM_T` carrying the `σ Ŝ` diffusion. The
**`f = S₀·exp` special case of `ito_formula_itoProcess`** — the Itô process `X_t = (m−σ²/2)t + σ B_t`
(`X₀ = 0`, drift `b = m−σ²/2`): there `f' = f'' = S₀·exp`, so the general drift
`f'(X)·b + ½f''(X)·σ² = S₀ exp(X)·(m−σ²/2) + ½σ²·S₀ exp(X) = m·Ŝ` (the time-localization `−σ²/2`
plus the Itô second-order `½σ²`). **Setting `m = 0` makes the drift vanish**
(`discountedGBM_eq_itoIntegral`) — the Itô-integral reading of the discounted-GBM martingale,
grounding it on the continuous Itô integral rather than the explicit Wald exponential. -/
theorem ito_formula_gbm (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω) (T : ℝ≥0) (S₀ m σ : ℝ) :
    ∃ gfx : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω => S₀ * Real.exp ((m - σ ^ 2 / 2) * (T : ℝ) + σ * B T ω)
              - S₀ * Real.exp ((m - σ ^ 2 / 2) * (0 : ℝ) + σ * B 0 ω)) =ᵐ[μ]
        (fun ω => (itoIntegralCLM_T hB T hBmeas gfx) ω
          + ∫ s in Set.Ioc 0 T, m * (S₀ * Real.exp ((m - σ ^ 2 / 2) * (s : ℝ) + σ * B s ω))
              ∂ItoIntegralL2.timeMeasure) := by
  -- `f = S₀·exp` has every exponential moment bound with `C = |S₀|`, `lam = 1`
  have hexp : ∀ y : ℝ, |S₀ * Real.exp y| ≤ |S₀| * Real.exp (1 * |y|) := fun y => by
    rw [abs_mul, abs_of_pos (Real.exp_pos _), one_mul]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (le_abs_self _)) (abs_nonneg _)
  obtain ⟨gfx, hgfx⟩ := ito_formula_itoProcess hB hBmeas hBcont T 0 (m - σ ^ 2 / 2) σ
    (f := fun y => S₀ * Real.exp y) (f' := fun y => S₀ * Real.exp y)
    (f'' := fun y => S₀ * Real.exp y) (f''' := fun y => S₀ * Real.exp y)
    (fun y => (Real.hasDerivAt_exp y).const_mul S₀)
    (fun y => (Real.hasDerivAt_exp y).const_mul S₀)
    (fun y => (Real.hasDerivAt_exp y).const_mul S₀)
    (lam := 1) (C := |S₀|) zero_le_one hexp hexp hexp
  -- on `[0, T]` the inner offset `X₀ = 0` drops out and the drift `b·f' + ½σ²f''` collapses to `m·Ŝ`
  refine ⟨gfx, ?_⟩
  filter_upwards [hgfx] with ω hω
  simp only [zero_add] at hω
  rw [hω, add_right_inj]
  exact integral_congr_ae (ae_of_all _ fun s => by ring)

/-- **The discounted GBM increment is a pure Itô integral (zero drift).** Specializing
`ito_formula_gbm` at the risk-neutral drift `m = 0`: the discounted geometric Brownian motion
`Ŝ(t) = S₀ exp(−(σ²/2)·t + σ B_t)` satisfies

  `Ŝ(T) − Ŝ(0) =ᵐ itoIntegralCLM_T gfx`,

the drift vanishing because the localization drift `−σ²/2` exactly cancels the Itô second-order
correction `½σ²`. This is the **Itô-integral content of the discounted-GBM martingale**
(`discountedGBM_isMartingale`, there obtained via the Wald exponential): the discounted price
moves only through its `σ Ŝ` diffusion against `dB`, with no drift — so the increment is a pure
Itô integral, and the martingale property is the martingale property of that integral. -/
theorem discountedGBM_eq_itoIntegral (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω) (T : ℝ≥0) (S₀ σ : ℝ) :
    ∃ gfx : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω => S₀ * Real.exp (-(σ ^ 2 / 2) * (T : ℝ) + σ * B T ω)
              - S₀ * Real.exp (σ * B 0 ω)) =ᵐ[μ]
        (fun ω => (itoIntegralCLM_T hB T hBmeas gfx) ω) := by
  obtain ⟨gfx, hgfx⟩ := ito_formula_gbm hB hBmeas hBcont T S₀ 0 σ
  refine ⟨gfx, ?_⟩
  filter_upwards [hgfx] with ω hω
  rw [show -(σ ^ 2 / 2) * (T : ℝ) = (0 - σ ^ 2 / 2) * (T : ℝ) by ring,
      show σ * B 0 ω = (0 - σ ^ 2 / 2) * (0 : ℝ) + σ * B 0 ω by ring, hω]
  simp

end MathFin
