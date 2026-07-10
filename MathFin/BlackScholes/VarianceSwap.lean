/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.Call
public import MathFin.BlackScholes.Forward

/-!
# Variance swap fair strike (Demeterfi-Derman-Kamal)

Under the BS lognormal hypothesis, the fair strike of a variance swap with
log-payoff replication

  `(2/T) · E_Q[log(F/S_T) + (S_T - F)/F] = σ²`,

where `F = S_0 · e^{rT}` is the forward price. The two terms are:

* `E_Q[log(F/S_T)] = σ² T / 2`: the log-moment of the discount factor `F/S_T`.
  Comes from `log(F/S_T) = σ² T / 2 − σ √T · Z` (after the `S_0` cancellation)
  and `E_Q[Z] = 0`.
* `E_Q[(S_T - F)/F] = 0`: zero by `expected_terminal_eq_forward` (`E_Q[S_T] = F`).

The result `(2/T)·σ²T/2 = σ²` says: under BS lognormal dynamics, the fair
variance swap rate equals the squared volatility — exactly the relationship
that makes BS implied volatility a "risk-neutral expected variance".

Results:

* `log_forward_div_bsTerminal_eq`: `log(F/S_T) = σ² T / 2 − σ √T · z`.
* `integral_log_forward_div_bsTerminal_eq`:
  `E_Q[log(F/S_T)] = σ² T / 2`.
* `varianceSwap_log_contribution`: the log-payoff piece
  `(2/T) · E_Q[log(F/S_T)] = σ²`.
* `integral_bsTerminal_eq_forward`: `E[S_T] = F` (standard-normal-driver form).
* `integral_excess_return_eq_zero`: `E[(S_T − F)/F] = 0`.
* `varianceSwap_fairStrike`: the full Demeterfi-Derman-Kamal identity
  `(2/T) · E[log(F/S_T) + (S_T − F)/F] = σ²`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Log-moment integrand identity**: after the `S_0` cancellation,
`log((S_0 · e^{rT}) / (S_0 · exp((r − σ²/2)T + σ√T·z))) = σ²T/2 − σ√T·z`. -/
lemma log_forward_div_bsTerminal_eq {S_0 : ℝ} (hS : 0 < S_0) (r σ T z : ℝ) :
    Real.log ((S_0 * Real.exp (r * T)) /
              (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
      = σ^2 * T / 2 - σ * Real.sqrt T * z := by
  have hS_ne : S_0 ≠ 0 := hS.ne'
  rw [mul_div_mul_left _ _ hS_ne]
  rw [← Real.exp_sub, Real.log_exp]
  ring

/-- **Log-moment integral identity**: `∫ z, log(F/S_T(z)) ∂(gaussianReal 0 1)
= σ² T / 2`. -/
lemma integral_log_forward_div_bsTerminal_eq {S_0 : ℝ} (hS : 0 < S_0)
    (r σ T : ℝ) :
    ∫ z, Real.log ((S_0 * Real.exp (r * T)) /
                  (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
      ∂(gaussianReal 0 1) = σ^2 * T / 2 := by
  have h_integrand_eq : ∀ z : ℝ,
      Real.log ((S_0 * Real.exp (r * T)) /
                (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
        = σ^2 * T / 2 - σ * Real.sqrt T * z :=
    fun z ↦ log_forward_div_bsTerminal_eq hS r σ T z
  rw [show (fun z ↦ Real.log ((S_0 * Real.exp (r * T)) /
              (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))))
        = (fun z ↦ σ^2 * T / 2 - σ * Real.sqrt T * z) from funext h_integrand_eq]
  have h_const_integrable :
      Integrable (fun _ : ℝ ↦ σ^2 * T / 2) (gaussianReal 0 1) :=
    integrable_const _
  have h_id_basic : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_cast)
  have h_id_integrable :
      Integrable (fun z : ℝ ↦ σ * Real.sqrt T * z) (gaussianReal 0 1) :=
    h_id_basic.const_mul (σ * Real.sqrt T)
  rw [integral_sub h_const_integrable h_id_integrable]
  rw [integral_const, integral_const_mul, integral_id_gaussianReal]
  simp

/-- **Variance swap fair strike (log-payoff contribution)**: the log-payoff
replication piece scales to give the squared volatility.

`(2/T) · E[log(F/S_T)] = σ²` under the BS lognormal hypothesis (with
`F = S_0 · e^{rT}`). Combined with the zero excess-return moment
`E[(S_T − F)/F] = 0` (from `expected_terminal_eq_forward`), this gives the
full Demeterfi-Derman-Kamal log-replication identity for the variance swap
fair strike. -/
theorem varianceSwap_log_contribution {S_0 : ℝ} (hS : 0 < S_0)
    (r σ T : ℝ) (hT : T ≠ 0) :
    (2 / T) *
      (∫ z, Real.log ((S_0 * Real.exp (r * T)) /
            (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z)))
        ∂(gaussianReal 0 1)) = σ^2 := by
  rw [integral_log_forward_div_bsTerminal_eq hS]
  field_simp

/-- **Terminal price is the forward in expectation** — the standard-normal-driver
form of `Forward.expected_terminal_eq_forward`: `E[S_T] = F = S_0·e^{rT}`. -/
lemma integral_bsTerminal_eq_forward (S_0 r σ T : ℝ) (hT : 0 ≤ T) :
    ∫ z, S_0 * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z) ∂(gaussianReal 0 1)
      = S_0 * Real.exp (r * T) := by
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0),
      show (fun z ↦ gaussianPDFReal 0 1 z •
            (S_0 * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)))
          = (fun z ↦ S_0 * Real.exp ((r - σ ^ 2 / 2) * T) *
              (Real.exp (σ * Real.sqrt T * z) * gaussianPDFReal 0 1 z)) from
        funext fun z ↦ by rw [smul_eq_mul, Real.exp_add]; ring,
      integral_const_mul, integral_exp_mul_gaussianPDFReal_univ,
      show S_0 * Real.exp ((r - σ ^ 2 / 2) * T) * Real.exp ((σ * Real.sqrt T) ^ 2 / 2)
          = S_0 * (Real.exp ((r - σ ^ 2 / 2) * T) * Real.exp ((σ * Real.sqrt T) ^ 2 / 2))
        from by ring,
      ← Real.exp_add,
      show (r - σ ^ 2 / 2) * T + (σ * Real.sqrt T) ^ 2 / 2 = r * T from by
        rw [mul_pow, Real.sq_sqrt hT]; ring]

/-- **Zero excess-return moment**: `E[(S_T − F)/F] = 0`, immediate from
`E[S_T] = F` (`integral_bsTerminal_eq_forward`). -/
lemma integral_excess_return_eq_zero (S_0 r σ T : ℝ) (hT : 0 ≤ T) :
    ∫ z, (S_0 * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)
            - S_0 * Real.exp (r * T)) / (S_0 * Real.exp (r * T)) ∂(gaussianReal 0 1) = 0 := by
  have hint : Integrable
      (fun z ↦ S_0 * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)) (gaussianReal 0 1) := by
    have h1 : Integrable (fun z ↦ Real.exp (σ * Real.sqrt T * z)) (gaussianReal 0 1) :=
      integrable_exp_mul_gaussianReal (σ * Real.sqrt T)
    refine (h1.const_mul (S_0 * Real.exp ((r - σ ^ 2 / 2) * T))).congr
      (Filter.Eventually.of_forall fun z ↦ ?_)
    show S_0 * Real.exp ((r - σ ^ 2 / 2) * T) * Real.exp (σ * Real.sqrt T * z)
        = S_0 * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)
    rw [mul_assoc, ← Real.exp_add]
  rw [integral_div, integral_sub hint (integrable_const _),
      integral_bsTerminal_eq_forward S_0 r σ T hT, integral_const, measureReal_def,
      measure_univ, ENNReal.toReal_one, one_smul, sub_self, zero_div]

/-- **Variance swap fair strike** (Demeterfi-Derman-Kamal, full log-replication
identity): `(2/T) · E[log(F/S_T) + (S_T − F)/F] = σ²`. Assembles the log
contribution with the zero excess-return moment `E[(S_T − F)/F] = 0`. -/
theorem varianceSwap_fairStrike {S_0 : ℝ} (hS : 0 < S_0) (r σ T : ℝ) (hT : 0 < T) :
    (2 / T) *
        ((∫ z, Real.log ((S_0 * Real.exp (r * T)) /
              (S_0 * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)))
            ∂(gaussianReal 0 1))
         + ∫ z, (S_0 * Real.exp ((r - σ ^ 2 / 2) * T + σ * Real.sqrt T * z)
              - S_0 * Real.exp (r * T)) / (S_0 * Real.exp (r * T)) ∂(gaussianReal 0 1))
      = σ ^ 2 := by
  rw [integral_excess_return_eq_zero S_0 r σ T hT.le, add_zero]
  exact varianceSwap_log_contribution hS r σ T hT.ne'

end MathFin
