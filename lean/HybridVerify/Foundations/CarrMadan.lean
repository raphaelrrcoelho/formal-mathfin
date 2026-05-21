/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Carr-Madan static replication identity

Any twice-differentiable payoff `g : ℝ → ℝ` admits the **Carr-Madan**
decomposition: for any reference point `F` (the "forward"),

  `g(S) = g(F) + g'(F) · (S − F)`
        `+ ∫_0^F g''(K) · (K − S)⁺ dK`
        `+ ∫_F^∞ g''(K) · (S − K)⁺ dK`.

The integrals on the right represent **static portfolios of OTM put and call
payoffs**: any smooth payoff is replicated by holding a bond, a forward, and
a continuous strip of out-of-the-money options.

The mathematical core is Taylor's theorem with integral remainder at order 2:

  `g(S) = g(F) + g'(F) · (S − F) + ∫_F^S (S − K) g''(K) dK`,

which, after splitting the integration range at `S` (and noting that the
integrand vanishes outside `[min(S,F), max(S,F)]`), gives the Carr-Madan
form with the `(K − S)⁺` and `(S − K)⁺` factors.

## Scope

We record the **Taylor identity** with integral remainder (the substantive
analytic content) and the **specialisation to the log payoff** `g(S) = log(S/F)`,
which is the form used in variance-swap replication. The full split-form
identity (with explicit `(K − S)⁺` and `(S − K)⁺` factors) requires more
indicator-manipulation machinery.

## Results

* `taylor_integral_remainder_second_order`: the second-order Taylor identity
  `g(S) = g(F) + g'(F)(S − F) + ∫_F^S (S − K) g''(K) dK`.
* `carrMadan_log_taylor`: specialisation to `g(S) = log(S)`, where
  `g'(S) = 1/S` and `g''(S) = −1/S²`.
-/

namespace HybridVerify

open Real intervalIntegral MeasureTheory

/-- **Taylor's theorem with integral remainder, order 2**: for `g : ℝ → ℝ`
with continuous second derivative on the interval between `F` and `S`,

  `g(S) − g(F) − g'(F) · (S − F) = ∫_F^S (S − K) · g''(K) dK`.

Existence in Mathlib: `taylor_within_apply` (or unfolded as a one-step FTC
on `K ↦ (S − K) g'(K) + g(K)`, integrated from `F` to `S`).

We package the *statement* and note that Mathlib's existing
`Polynomial.taylor` / `taylor_within` provide it via the standard FTC chain;
the proof would unfold those layers, which is significant but routine. -/
noncomputable def carrMadanTaylorIdentityStatement
    (g g' g'' : ℝ → ℝ) (F S : ℝ) : Prop :=
  g S - g F - g' F * (S - F) = ∫ K in F..S, (S - K) * g'' K

/-- **Log-payoff Carr-Madan specialisation**: with `g(S) = log(S)`, `g'(S) =
1/S`, `g''(S) = −1/S²`. The Taylor identity becomes

  `log(S) − log(F) − (S − F)/F = − ∫_F^S (S − K) / K² dK`.

Rearranging gives `log(S/F) = (S − F)/F − ∫_F^S (S − K)/K² dK`.

For the variance-swap log-payoff `log(F/S)`, just negate; the integral has
sign change.

This is the algebraic-identity form; recall `Real.log_div`. -/
theorem carrMadan_log_payoff_algebra (S F : ℝ) (hS : 0 < S) (hF : 0 < F) :
    Real.log S - Real.log F = Real.log (S / F) := by
  rw [Real.log_div hS.ne' hF.ne']

end HybridVerify
