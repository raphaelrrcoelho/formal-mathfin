/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholes.Call
import HybridVerify.BlackScholes.Forward

/-!
# Second moment and variance of the terminal asset price

Under `BSCallHyp` (risk-neutral lognormal model), the second moment and the
variance of the terminal asset price are

  `E_Q[S_T²] = S_0² · exp(2 r T + σ² T)`,
  `Var_Q[S_T] = S_0² · exp(2 r T) · (exp(σ² T) − 1)`.

Derivation: `(bsTerminal z)² = S_0² · exp(2(r − σ²/2)T + 2 σ √T · z)`, so the
risk-neutral expectation reduces to the gaussian MGF at `2σ√T`. Combined with
`expected_terminal_eq_forward` (which gives `E[S_T] = S_0 e^{rT}`), the variance
identity is immediate.

These complete the algebraic description of the lognormal distribution under
the BS model — no Itô calculus required.

Results:

* `secondMoment_terminal`: `E_Q[S_T²] = S_0² · exp(2 r T + σ² T)`.
* `variance_terminal`: `E_Q[S_T²] − (E_Q[S_T])² = S_0² · exp(2 r T) ·
  (exp(σ² T) − 1)`.
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Second moment of the terminal asset price**: under `BSCallHyp`,
`E_Q[S_T²] = S_0² · exp(2 r T + σ² T)`. -/
theorem secondMoment_terminal
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, (bsTerminal S_0 r σ T (Z ω))^2 ∂Q =
      S_0^2 * Real.exp (2 * r * T + σ^2 * T) := by
  obtain ⟨hS_0, _hK, _hσ, hT, hZ⟩ := h
  set μ_log : ℝ := 2 * (r - σ^2 / 2) * T with μ_log_def
  set ν_log : ℝ := 2 * σ * Real.sqrt T with ν_log_def
  have hsqrT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hν_log_sq : ν_log^2 = 4 * σ^2 * T := by
    rw [ν_log_def]; ring_nf; rw [Real.sq_sqrt hT.le]
  have h_algebra : μ_log + ν_log^2 / 2 = 2 * r * T + σ^2 * T := by
    rw [hν_log_sq]; ring
  have h_term_meas : Measurable fun z : ℝ => (bsTerminal S_0 r σ T z)^2 := by
    unfold bsTerminal; fun_prop
  rw [show (fun ω => (bsTerminal S_0 r σ T (Z ω))^2)
        = (fun z => (bsTerminal S_0 r σ T z)^2) ∘ Z from rfl,
      hZ.integral_comp h_term_meas.aestronglyMeasurable,
      integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  -- Rewrite pdf · (bsTerminal z)² = S_0² · exp(μ_log) · (exp(ν_log · z) · pdf)
  have h_factor : ∀ z : ℝ,
      gaussianPDFReal 0 1 z • (bsTerminal S_0 r σ T z)^2
        = S_0^2 * Real.exp μ_log *
            (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z) := by
    intro z
    unfold bsTerminal
    -- (S_0 · exp(a + b z))² = S_0² · exp(2(a + b z)) = S_0² · exp(2a) · exp(2 b z)
    have h_sq :
        (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))^2
          = S_0^2 * (Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))^2 := by
      ring
    have h_exp_sq :
        (Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))^2
          = Real.exp (μ_log + ν_log * z) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      rw [μ_log_def, ν_log_def]; ring
    rw [h_sq, h_exp_sq, smul_eq_mul, Real.exp_add]
    ring
  rw [show (fun z => gaussianPDFReal 0 1 z • (bsTerminal S_0 r σ T z)^2)
        = (fun z => S_0^2 * Real.exp μ_log *
            (Real.exp (ν_log * z) * gaussianPDFReal 0 1 z)) from funext h_factor]
  rw [integral_const_mul, integral_exp_mul_gaussianPDFReal_univ]
  rw [show S_0^2 * Real.exp μ_log * Real.exp (ν_log^2 / 2)
        = S_0^2 * (Real.exp μ_log * Real.exp (ν_log^2 / 2)) from by ring,
      ← Real.exp_add, h_algebra]

/-- **Variance of the terminal asset price**: under `BSCallHyp`,
`Var_Q[S_T] = E_Q[S_T²] − (E_Q[S_T])² = S_0² · exp(2 r T) · (exp(σ² T) − 1)`.

Combines `secondMoment_terminal` with `expected_terminal_eq_forward`. -/
theorem variance_terminal
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, (bsTerminal S_0 r σ T (Z ω))^2 ∂Q -
      (∫ ω, bsTerminal S_0 r σ T (Z ω) ∂Q)^2 =
        S_0^2 * Real.exp (2 * r * T) * (Real.exp (σ^2 * T) - 1) := by
  rw [secondMoment_terminal h, expected_terminal_eq_forward h]
  -- (S_0 · exp(rT))^2 = S_0^2 · exp(rT)^2 = S_0^2 · exp(2rT)
  have h_exp_sq : (Real.exp (r * T))^2 = Real.exp (2 * r * T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1; ring
  have h_sq_exp : (S_0 * Real.exp (r * T))^2 = S_0^2 * Real.exp (2 * r * T) := by
    rw [mul_pow, h_exp_sq]
  rw [h_sq_exp, Real.exp_add]
  ring

end HybridVerify
