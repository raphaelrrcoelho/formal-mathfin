/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Compound Poisson MGF and Lundberg adjustment coefficient

For `N ~ Poisson(λ)` and iid claim sizes `X_i` with MGF `M_X`, the
**compound Poisson** aggregate `S = ∑_{i=1}^N X_i` has MGF

  `E[e^{t S}] = exp(λ · (M_X(t) − 1))`.

Derivation:

  `E[e^{tS}] = ∑_{n=0}^∞ P(N=n) · E[e^{tS} | N=n]`
            `= ∑_{n=0}^∞ e^{−λ} (λ)^n / n! · M_X(t)^n`
            `= e^{−λ} · ∑_{n=0}^∞ (λ · M_X(t))^n / n!`
            `= e^{−λ} · exp(λ · M_X(t))`
            `= exp(λ · (M_X(t) − 1))`.

The last equality is the algebraic core that we formalise. The probabilistic
derivation requires the iid structure and the conditional MGF identity, which
sit on top of Mathlib's discrete Poisson PMF and would expand significantly.

The **Lundberg adjustment coefficient** `R > 0` in the Cramér-Lundberg ruin
model solves

  `λ · (M_X(R) − 1) − c · R = 0`,

where `c` is the premium rate. Its existence (under a positive safety
loading) yields the classical ruin-probability bound `P(ruin) ≤ exp(−R · u)`
(Lundberg's inequality). We record the equation algebraically; the full
inequality is gated on Poisson processes and renewal theory.

## Results

* `compoundPoisson_mgf_identity`: `e^{−λ} · e^{λ M} = e^{λ(M − 1)}`.
  The algebraic core of the compound Poisson MGF.
* `isLundbergAdjustmentCoefficient`: predicate for `R` to solve the adjustment
  equation `λ · (M(R) − 1) = c · R`.
* `lundberg_zero_at_zero`: `R = 0` always satisfies the equation trivially
  (`0 = 0`); the meaningful adjustment coefficient is the *positive* root.
-/

namespace HybridVerify

open Real

/-- **Compound Poisson MGF algebraic core**: `e^{−λ} · e^{λ M} = e^{λ(M − 1)}`.

Underlies the textbook MGF identity
`E[e^{tS}] = exp(λ · (M_X(t) − 1))` for `S = ∑_{i=1}^N X_i` with `N ~
Poisson(λ)` and the `X_i` iid with MGF `M_X(t)`. The factor `e^{−λ}` comes
from `P(N=n) = e^{−λ} · λ^n / n!`, and the sum `∑ P(N=n) · M(t)^n` evaluates
to `e^{−λ} · e^{λ M(t)}` via the exponential series. -/
theorem compoundPoisson_mgf_identity (lam M : ℝ) :
    Real.exp (-lam) * Real.exp (lam * M) = Real.exp (lam * (M - 1)) := by
  rw [← Real.exp_add]
  congr 1; ring

/-- **Lundberg adjustment-coefficient equation**: `R` is a Lundberg adjustment
coefficient when it solves `λ · (M(R) − 1) − c · R = 0`, where `λ` is the
claim arrival rate, `c` the premium rate, and `M` the claim-size MGF.

The *positive* root (when it exists) bounds the ruin probability via
`P(ruin) ≤ exp(−R · u)`. -/
def isLundbergAdjustmentCoefficient (lam c R : ℝ) (M : ℝ → ℝ) : Prop :=
  lam * (M R - 1) - c * R = 0

/-- **Trivial root at zero**: `R = 0` always satisfies the adjustment equation
when `M 0 = 1` (which holds for any MGF). The meaningful adjustment coefficient
is the strictly positive root, whose existence requires the positive-safety-
loading condition `λ · M'(0) < c`. -/
theorem lundberg_zero_at_zero (lam c : ℝ) (M : ℝ → ℝ) (hM0 : M 0 = 1) :
    isLundbergAdjustmentCoefficient lam c 0 M := by
  unfold isLundbergAdjustmentCoefficient
  rw [hM0]
  ring

end HybridVerify
