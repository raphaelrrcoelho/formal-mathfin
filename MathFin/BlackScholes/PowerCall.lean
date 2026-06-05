/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.Call

/-!
# Powered call option closed form (first-principles)

The **powered call** with exponent `a : ℕ` pays `max((S_T)^a − K, 0)` at
maturity. Its risk-neutral discounted price has a closed form in the BS
lognormal model — derived here as a direct consequence of `bs_call_formula`
via the structural identity that **`(S_T)^a` is itself a BS terminal**, with
*effective spot* `S_0^a · exp((a−1)rT + a(a−1)/2 σ²T)` and *effective
volatility* `aσ`. No new integral is computed: the only new content is the
algebraic identity reducing the powered case to the standard case.

## Mathematical content

Starting from `S_T = S_0 · exp((r − σ²/2)T + σ√T·Z)`,

  `(S_T)^a = S_0^a · exp(a(r − σ²/2)T + aσ√T·Z)`.

We want to write the RHS as `Š_0 · exp((r − σ̃²/2)T + σ̃√T·Z)` for some
effective spot `Š_0` and volatility `σ̃`. Setting `σ̃ = aσ` gives `σ̃²T =
a²σ²T`, so

  `Š_0 = S_0^a · exp(a(r − σ²/2)T − (r − a²σ²/2)T)`
       = `S_0^a · exp((a−1)rT + a(a−1)/2 σ²T)`.

This `Š_0` is the **risk-neutral expected** value of `(S_T)^a` divided by
`e^{rT}` (a.k.a. the power-forward; see `PowerOption.powerForward_price`).

## Why this is first-principles

The pre-existing `PowerOption.lean` derives `E[(S_T)^a]` from the affine-
shifted standard-normal MGF (one direct integral). This file goes the next
step: it shows the *struck* payoff `max((S_T)^a − K, 0)` also has a closed
form, reducing it not by a new integral but by recognising that the
powered terminal is a standard BS terminal with adjusted spot and
volatility. The whole derivation goes via `bs_call_formula` with no
additional Gaussian work.

## Results

* `bsPowerTerminal`: `(S_T)^a` as a function of the standard-normal sample.
* `bsPowerEffectiveSpot`: `S_0^a · exp((a−1)rT + a(a−1)/2 σ²T)`.
* `bsPowerTerminal_eq_bsTerminal_effective`: the structural reduction
  identity.
* `bsCallHyp_powered`: lift of `BSCallHyp` to the effective-spot /
  effective-volatility setup.
* `bs_power_call_formula`: the closed-form discounted price.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Powered terminal asset price**: `(S_T)^a` viewed as a function of the
standard-normal sample. -/
noncomputable def bsPowerTerminal (S_0 r σ T : ℝ) (a : ℕ) (z : ℝ) : ℝ :=
  (bsTerminal S_0 r σ T z) ^ a

/-- **Effective spot** for the power-call reduction:
`Š_0 = S_0^a · exp((a−1)rT + a(a−1)/2 σ²T)`. -/
noncomputable def bsPowerEffectiveSpot (S_0 r σ T : ℝ) (a : ℕ) : ℝ :=
  S_0 ^ a *
    Real.exp (((a : ℝ) - 1) * r * T + (a : ℝ) * ((a : ℝ) - 1) / 2 * σ ^ 2 * T)

/-- **Structural reduction identity**: the powered terminal `(S_T)^a` *is* a
standard BS terminal, with effective spot `bsPowerEffectiveSpot` and
effective volatility `aσ`. This is the algebraic core that lets us reduce
power-option pricing to `bs_call_formula`. -/
theorem bsPowerTerminal_eq_bsTerminal_effective
    (S_0 r σ T : ℝ) (a : ℕ) (z : ℝ) :
    bsPowerTerminal S_0 r σ T a z =
      bsTerminal (bsPowerEffectiveSpot S_0 r σ T a) r ((a : ℝ) * σ) T z := by
  unfold bsPowerTerminal bsTerminal bsPowerEffectiveSpot
  rw [mul_pow, ← Real.exp_nat_mul]
  rw [mul_assoc (S_0 ^ a), ← Real.exp_add]
  congr 1
  congr 1
  ring

/-- **`bsCallHyp` lifts to the powered setup**: if the standard BS hypothesis
holds for `(S_0, K, r, σ, T, Z)`, then it also holds for the effective-spot
and effective-volatility tuple `(Š_0, K', r, aσ, T, Z)` for any positive
strike `K'` and any positive exponent `a`. -/
theorem bsCallHyp_powered {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ} {K' : ℝ}
    (a : ℕ) (ha : 0 < a) (hK' : 0 < K')
    (h : BSCallHyp Q S_0 K r σ T Z) :
    BSCallHyp Q (bsPowerEffectiveSpot S_0 r σ T a) K' r ((a : ℝ) * σ) T Z := by
  obtain ⟨hS_0, _hK, hσ, hT, hZ⟩ := h
  refine ⟨?_, hK', ?_, hT, hZ⟩
  · unfold bsPowerEffectiveSpot
    exact mul_pos (pow_pos hS_0 a) (Real.exp_pos _)
  · have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    exact mul_pos ha_pos hσ

/-- **Black-Scholes powered call pricing formula** (first-principles).
For the powered payoff `max((S_T)^a − K, 0)` under `BSCallHyp`, the discounted
risk-neutral expectation equals the standard BS call price evaluated at the
effective spot `Š_0` and effective volatility `aσ`:

  `e^{−rT} · E_Q[max((S_T)^a − K, 0)]
    = Š_0 · Φ(d̃_1) − K · e^{−rT} · Φ(d̃_2)`,

where `(d̃_1, d̃_2)` are `(bsd1, bsd2)` at `(Š_0, K, r, aσ, T)`.

Proof: rewrite the integrand via `bsPowerTerminal_eq_bsTerminal_effective`
and apply `bs_call_formula` to the lifted hypothesis. -/
theorem bs_power_call_formula
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (a : ℕ) (ha : 0 < a) (hK : 0 < K)
    (h : BSCallHyp Q S_0 K r σ T Z) :
    ∫ ω, Real.exp (-r * T) *
        max (bsPowerTerminal S_0 r σ T a (Z ω) - K) 0 ∂Q =
      bsPowerEffectiveSpot S_0 r σ T a *
        Phi (bsd1 (bsPowerEffectiveSpot S_0 r σ T a) K r ((a : ℝ) * σ) T) -
      K * Real.exp (-r * T) *
        Phi (bsd2 (bsPowerEffectiveSpot S_0 r σ T a) K r ((a : ℝ) * σ) T) := by
  have h' :
      BSCallHyp Q (bsPowerEffectiveSpot S_0 r σ T a) K r ((a : ℝ) * σ) T Z :=
    bsCallHyp_powered a ha hK h
  have h_int :
      (fun ω => Real.exp (-r * T) *
          max (bsPowerTerminal S_0 r σ T a (Z ω) - K) 0) =
      (fun ω => Real.exp (-r * T) *
          max (bsTerminal (bsPowerEffectiveSpot S_0 r σ T a) r
                ((a : ℝ) * σ) T (Z ω) - K) 0) := by
    funext ω
    rw [bsPowerTerminal_eq_bsTerminal_effective]
  rw [h_int]
  exact bs_call_formula h'

/-- **Specialisation `a = 1` recovers the standard BS call price** at the
level of effective spot: `Š_0 = S_0` when `a = 1`. -/
lemma bsPowerEffectiveSpot_one (S_0 r σ T : ℝ) :
    bsPowerEffectiveSpot S_0 r σ T 1 = S_0 := by
  unfold bsPowerEffectiveSpot
  have h_arg :
      (((1 : ℕ) : ℝ) - 1) * r * T +
        ((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 1) / 2 * σ ^ 2 * T = 0 := by
    push_cast; ring
  rw [h_arg, Real.exp_zero, pow_one, mul_one]

end MathFin
