/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholes.Call
import HybridVerify.BlackScholes.Forward

/-!
# Power options under the BS lognormal hypothesis

A power option pays a function of `S_T^n` for some `n : ℕ`. The key
risk-neutral moment is

  `E_Q[S_T^n] = S_0^n · exp(n·r·T + n(n-1)/2 · σ² T)`,

with the canonical specializations `n = 1` (forward price) and `n = 2`
(`secondMoment_terminal` in `LognormalMoments.lean`). Discounting gives the
**power-forward price**

  `e^{-rT} · E_Q[S_T^n] = S_0^n · exp((n-1)·r·T + n(n-1)/2 · σ² T)`,

which generalizes both the spot-forward parity (`n = 1`, price = `S_0`) and the
discounted second moment.

Derivation pattern (identical to `secondMoment_terminal`): rewrite
`(S_T)^n = S_0^n · exp(n·(r − σ²/2)·T + n·σ·√T·Z)`, apply the gaussian MGF
`E[exp(c·Z)] = exp(c²/2)` at `c = n·σ·√T`.

Results:

* `nthMoment_terminal`: the `n`-th moment of `S_T` under `BSCallHyp`.
* `powerForward_price`: discounted power-forward price.
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **`n`-th moment of the terminal asset price** under `BSCallHyp`:
`E_Q[S_T^n] = S_0^n · exp(n·r·T + n(n-1)/2 · σ² T)`. -/
theorem nthMoment_terminal
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ} (n : ℕ)
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, (bsTerminal S_0 r σ T (Z ω))^n ∂Q =
      S_0^n *
        Real.exp ((n : ℝ) * r * T + (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T) := by
  obtain ⟨_hS_0, _hK, _hσ, hT, hZ⟩ := h
  set N : ℝ := (n : ℝ) with N_def
  set μ_log : ℝ := N * (r - σ^2 / 2) * T with μ_log_def
  set ν_log : ℝ := N * σ * Real.sqrt T with ν_log_def
  have hν_log_sq : ν_log^2 = N^2 * σ^2 * T := by
    rw [ν_log_def]; ring_nf; rw [Real.sq_sqrt hT.le]
  have h_algebra : μ_log + ν_log^2 / 2 = N * r * T + N * (N - 1) / 2 * σ^2 * T := by
    rw [hν_log_sq]; ring
  have h_term_meas : Measurable fun z : ℝ => (bsTerminal S_0 r σ T z)^n := by
    unfold bsTerminal; fun_prop
  rw [show (fun ω => (bsTerminal S_0 r σ T (Z ω))^n)
        = (fun z => (bsTerminal S_0 r σ T z)^n) ∘ Z from rfl,
      hZ.integral_comp h_term_meas.aestronglyMeasurable,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  have h_factor : ∀ z : ℝ,
      gaussianPDFReal 0 1 z • (bsTerminal S_0 r σ T z)^n
        = S_0^n * Real.exp μ_log *
            (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z) := by
    intro z
    unfold bsTerminal
    have h_pow :
        (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))^n
          = S_0^n * (Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))^n :=
      mul_pow _ _ _
    have h_exp_pow :
        (Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))^n
          = Real.exp (μ_log + ν_log * z) := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [μ_log_def, ν_log_def, N_def]; ring
    rw [h_pow, h_exp_pow, smul_eq_mul, Real.exp_add]
    ring
  rw [show (fun z => gaussianPDFReal 0 1 z • (bsTerminal S_0 r σ T z)^n)
        = (fun z => S_0^n * Real.exp μ_log *
            (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z)) from funext h_factor]
  rw [integral_const_mul, integral_exp_mul_gaussianPDFReal_univ]
  rw [show S_0^n * Real.exp μ_log * Real.exp (ν_log^2 / 2)
        = S_0^n * (Real.exp μ_log * Real.exp (ν_log^2 / 2)) from by ring,
      ← Real.exp_add, h_algebra]

/-- **Power-forward price**: discounted `n`-th moment of `S_T` equals
`S_0^n · exp((n-1)·r·T + n(n-1)/2 · σ² T)`. Specializes to:
* `n = 0`: `e^{-rT}`,
* `n = 1`: `S_0` (martingale property of discounted spot),
* `n = 2`: `S_0² · exp(r·T + σ² T)`. -/
theorem powerForward_price
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ} (n : ℕ)
    (h : BSCallHyp Q S_0 K r σ T Z) :
    Real.exp (-(r * T)) *
      (∫ ω, (bsTerminal S_0 r σ T (Z ω))^n ∂Q) =
      S_0^n *
        Real.exp ((((n : ℝ) - 1) * r * T) +
                  (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T) := by
  rw [nthMoment_terminal n h]
  rw [show Real.exp (-(r * T)) *
        (S_0^n *
          Real.exp ((n : ℝ) * r * T +
                    (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T))
        = S_0^n *
            (Real.exp (-(r * T)) *
              Real.exp ((n : ℝ) * r * T +
                        (n : ℝ) * ((n : ℝ) - 1) / 2 * σ^2 * T)) from by ring,
      ← Real.exp_add]
  congr 2
  ring

end HybridVerify
