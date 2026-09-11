/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Pricing
public import MathFin.BlackScholes.Digital
public import MathFin.BlackScholes.Put

/-!
# Closing the loop: the reified call, put and digital price to their closed forms

`MathFin/BlackScholes/Call.lean`, `Put.lean` and `Digital.lean` each prove a pricing
identity whose left-hand side is a lambda written inline inside the integral — the
payoff and the model are the same syntactic object, and the payoff exists nowhere
else in the library. This file reifies each of those payoffs as a `Contract Unit`
(`europeanCall`, `europeanPut`, `digitalCall`) against `bsAssets`, the single-asset
Black–Scholes model map, and proves each reified contract's `Contract.value` equals
the closed form the library already proves.

`bsAssets` is constant in `t`: every instrument here observes the underlying only at
its maturity `T`, so the model's value at other times is irrelevant to what gets
priced. This is deliberate and correct for these single-maturity instruments, not an
oversight — it does not supply a path, and a genuinely path-dependent instance needs
one and is deferred.

Nothing new is proved about Black–Scholes here. The whole content is the reduction
`value_pay_eq`: unfolding `Contract.pay`'s semantics turns `Contract.value` into
exactly the integral `bs_call_formula`, `bs_put_formula` and
`bs_cash_or_nothing_formula` already compute, so each of `value_europeanCall`,
`value_europeanPut` and `value_digitalCall` closes by `rw [value_pay_eq]` followed by
the existing theorem.

## Main definitions

* `bsAssets` — the single-asset Black–Scholes model as a model map `Unit → ℝ≥0 → Ω → ℝ`,
  constant in `t` and equal to `bsTerminal` at every time.
* `europeanCallPayoff` — the call's payoff data on its own, so `CappedCall.lean` can build
  against exactly this term rather than a second copy of it.
* `europeanCall`, `europeanPut`, `digitalCall` — the three reified `Contract Unit`s.

## Main results

* `value_pay_eq` — a single-cashflow contract's `value` is the integral of its
  discounted payoff; the shared reduction step folding all three theorems below into
  one `rw` plus the existing closed form.
* `value_europeanCall`, `value_europeanPut`, `value_digitalCall` — each reified
  contract's `value` equals `bs_call_formula`, `bs_put_formula` and
  `bs_cash_or_nothing_formula` respectively.

## Source

The layered separation of contract semantics from pricing semantics, and the
framing "the contract is not the model", are due to Paul Bilokon,
*The Contract Is Not the Model: Proof-Carrying Exotic Derivatives and the
Economics of Model Risk* (working paper, 9 August 2026; Mathematical
Finance, Imperial College London), with code at
<https://github.com/thalesians/lean_contracts> (Apache-2.0). That paper in
turn builds on the compositional contract-DSL of
Peyton Jones, Eber and Seward (2000) and the certified-contract work of Bahr,
Berthold and Elsman (2015) and Annenkov (2018).

The source paper's §"Pricing-model validation" lists proving contract cashflows
measurable and integrable, and connecting them to a concrete model, as future
work; this file does that reduction against closed forms the library already
proves.

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The single-asset Black–Scholes market as a model map. Every instrument in
this file observes only at `T`, so the value at other times is irrelevant; a
path-dependent instance needs the full GBM path and is deferred. -/
noncomputable def bsAssets (S_0 r σ T : ℝ) (Z : Ω → ℝ) : Unit → ℝ≥0 → Ω → ℝ :=
  fun _ _ ω ↦ bsTerminal S_0 r σ T (Z ω)

/-- The European call payoff `max (S_T - K) 0`, on its own so a consumer outside this file
(`CappedCall.lean`'s measurability argument) can reference the same term rather than
re-spelling it. -/
noncomputable def europeanCallPayoff (K : ℝ) (T : ℝ≥0) : Payoff Unit :=
  .max (.sub (.obs () T) (.const K)) (.const 0)

/-- The reified European call: pays `max (S_T - K) 0` at maturity `T`. -/
noncomputable def europeanCall (K : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (europeanCallPayoff K T)

/-- The reified European put: pays `max (K - S_T) 0` at maturity `T`. -/
noncomputable def europeanPut (K : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (.max (.sub (.const K) (.obs () T)) (.const 0))

/-- The reified cash-or-nothing digital call: pays `1` at maturity `T` iff `S_T > K`. -/
noncomputable def digitalCall (K : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (.indicatorLt (.const K) (.obs () T))

/-- A single-cashflow contract's `value` is the integral of its discounted payoff.
The shared reduction step: `Contract.value` unfolds to exactly this shape for any
`pay`, so each of `value_europeanCall`, `value_europeanPut` and `value_digitalCall`
below reaches the corresponding `MathFin.BlackScholes` closed form by rewriting
through this lemma once rather than repeating the same eleven-lemma unfold three
times. -/
private theorem value_pay_eq {ι : Type*} (Q : Measure Ω) (D : ℝ≥0 → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a : Payoff ι) :
    (Contract.pay t a).value Q D X = ∫ ω, D t * a.eval (scenarioAt X ω) ∂Q := by
  simp [Contract.value, Contract.pathPV, Contract.cashflows]

/-- The reified European call prices to the Black–Scholes call formula: the value of
`europeanCall K T` under `bsAssets` is exactly `bs_call_formula`'s right-hand side. -/
theorem value_europeanCall {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    (europeanCall K T).value Q (fun _ ↦ Real.exp (-r * T)) (bsAssets S_0 r σ T Z)
      = S_0 * Phi (bsd1 S_0 K r σ T) - K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) := by
  rw [europeanCall, value_pay_eq]
  exact MathFin.bs_call_formula h

/-- The reified cash-or-nothing digital call prices to the Black–Scholes
cash-or-nothing formula: the value of `digitalCall K T` under `bsAssets` is exactly
`bs_cash_or_nothing_formula`'s right-hand side. -/
theorem value_digitalCall {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    (digitalCall K T).value Q (fun _ ↦ Real.exp (-r * T)) (bsAssets S_0 r σ T Z)
      = Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) := by
  rw [digitalCall, value_pay_eq]
  have heq (ω : Ω) : Payoff.eval (scenarioAt (bsAssets S_0 r σ T Z) ω)
      ((Payoff.const K).indicatorLt (Payoff.obs () T))
        = (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ)) (bsTerminal S_0 r σ T (Z ω)) := by
    simp [Payoff.eval, scenarioAt, bsAssets, Set.indicator_apply, Set.mem_Ioi]
    congr 1
  simp only [heq]
  exact MathFin.bs_cash_or_nothing_formula h

/-- The reified European put prices to the Black–Scholes put formula: the value of
`europeanPut K T` under `bsAssets` is exactly `bs_put_formula`'s right-hand side. -/
theorem value_europeanPut {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    (europeanPut K T).value Q (fun _ ↦ Real.exp (-r * T)) (bsAssets S_0 r σ T Z)
      = K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T)) - S_0 * Phi (-(bsd1 S_0 K r σ T)) := by
  rw [europeanPut, value_pay_eq]
  exact MathFin.bs_put_formula h

end MathFin.Contracts
