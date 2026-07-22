/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Knock-in / knock-out barrier parity (in–out parity)

A knock-**in** option pays the vanilla payoff `f` only if the underlying path
hits the barrier during the option's life; the matching knock-**out** pays `f`
only if it does *not*. The barrier-hit event `A` and its complement `Aᶜ`
partition every path, so the two discounted expected payoffs add back to the
vanilla price:

`V_in + V_out = V_vanilla`.

This needs **no** barrier density and no running-max law — it is a pure
linearity-of-expectation identity, in the register of
`BlackScholes/ChooserComposition.lean`'s `chooser_integral_decomp`: a pathwise
payoff decomposition (`barrier_payoff_partition`) lifted through the integral.

We first name the present-value functional the library had only ever written
inline — `discountedValue D Q g = D · E_Q[g]` — so the barrier values are thin,
honest specialisations of it and the parity reads as an identity about *values*.

## Results

* `discountedValue`: `D · E_Q[g]`, the discounted risk-neutral value functional.
* `knockInValue` / `knockOutValue` / `vanillaValue`: the three barrier values.
* `barrier_payoff_partition`: the pathwise split `𝟙_A·f + 𝟙_{Aᶜ}·f = f`.
* `knockIn_add_knockOut_eq_vanilla`: in–out parity `V_in + V_out = V_vanilla`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Discounted risk-neutral value** of a payoff `g` under pricing measure `Q`
and discount factor `D`: `D · E_Q[g]`. The present-value functional the pricing
files had been spelling out inline; named here so in–out parity is an identity
about values rather than raw integrals. -/
noncomputable def discountedValue (D : ℝ) (Q : Measure Ω) (g : Ω → ℝ) : ℝ :=
  D * ∫ ω, g ω ∂Q

/-- **Knock-in value**: the option pays the payoff `f` only on the barrier-hit
event `A`, so its value is the discounted expectation of `𝟙_A · f`. -/
noncomputable def knockInValue (D : ℝ) (Q : Measure Ω) (A : Set Ω) (f : Ω → ℝ) : ℝ :=
  discountedValue D Q (A.indicator f)

/-- **Knock-out value**: the option pays `f` only off the barrier-hit event, i.e.
on the complement `Aᶜ`, so its value is the discounted expectation of
`𝟙_{Aᶜ} · f = (1 − 𝟙_A) · f`. -/
noncomputable def knockOutValue (D : ℝ) (Q : Measure Ω) (A : Set Ω) (f : Ω → ℝ) : ℝ :=
  discountedValue D Q (Aᶜ.indicator f)

/-- **Vanilla value**: the discounted expected payoff `f`, paid on every path. -/
noncomputable def vanillaValue (D : ℝ) (Q : Measure Ω) (f : Ω → ℝ) : ℝ :=
  discountedValue D Q f

/-- **Barrier payoff partition** (pathwise): the knock-in payoff `𝟙_A · f` and the
knock-out payoff `𝟙_{Aᶜ} · f` sum to the vanilla payoff `f` on every path — each
path either hits the barrier (`ω ∈ A`) or does not (`ω ∈ Aᶜ`), and contributes
`f ω` to exactly one leg. -/
theorem barrier_payoff_partition (A : Set Ω) (f : Ω → ℝ) :
    A.indicator f + Aᶜ.indicator f = f :=
  Set.indicator_self_add_compl A f

/-- **In–out barrier parity**: `V_in + V_out = V_vanilla`. The barrier-hit event
`A` and its complement partition the paths (`barrier_payoff_partition`), so the
discounted expected payoffs add to the vanilla price. Pure linearity of the
integral — no barrier density required. -/
theorem knockIn_add_knockOut_eq_vanilla
    (D : ℝ) (Q : Measure Ω) (A : Set Ω) (f : Ω → ℝ)
    (hA : MeasurableSet A) (hf : Integrable f Q) :
    knockInValue D Q A f + knockOutValue D Q A f = vanillaValue D Q f := by
  unfold knockInValue knockOutValue vanillaValue discountedValue
  rw [← mul_add, integral_indicator hA, integral_indicator hA.compl,
    integral_add_compl hA hf]

end MathFin
