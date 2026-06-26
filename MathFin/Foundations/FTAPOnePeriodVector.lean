/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# One-period FTAP on a general probability space (d assets)

The Föllmer–Schied / one-period Dalang–Morton–Willinger Fundamental Theorem of Asset
Pricing for a `ℝᵈ`-valued discounted excess return `Y` and **constant** portfolios
`θ ∈ ℝᵈ` (trivial initial information) on an **arbitrary** probability space `(Ω, P)`:
no arbitrage ⟺ there is an equivalent martingale measure `Q ~ P` with `Y` integrable
and `E_Q[Y] = 0 ∈ ℝᵈ`.

This is the `d`-asset generalisation of the scalar `Foundations/FTAPOnePeriod.lean`.
Because `θ` ranges over the **finite-dimensional** `ℝᵈ`, the equivalent martingale
measure is **explicit** — the backward direction is the Esscher / minimal-divergence
construction: minimise the smooth convex potential `θ ↦ E[log(1 + exp⟪θ,Y⟫)]`; under
no arbitrage it is coercive transverse to `{u : ⟪u,Y⟫ = 0 a.e.}`, so a minimiser `θ*`
exists, and its first-order condition `E[Y · σ(⟪θ*,Y⟫)] = 0` (with `σ` the logistic
function) hands back a strictly-positive bounded density `z = σ(⟪θ*,Y⟫)`. No
Hahn–Banach, no L⁰-cone closedness, no measurable selection — those are needed only
for the general-Ω **multi-period** DMW.

## Scope

One trading period, **`d` assets**, **trivial `ℱ₀`** (constant `θ`), arbitrary
`(Ω, P)`. The general-Ω multi-period DMW (predictable `L⁰(ℱ_t)`-strategies and the
L⁰ gains-cone closedness) remains open.

## Main result

* `MathFin.OnePeriodVector.ftap_one_period_vector`
-/

@[expose] public section

namespace MathFin.OnePeriodVector

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  {d : ℕ} (Y : Ω → EuclideanSpace ℝ (Fin d))

/-- **No arbitrage** (`d` assets, one period): no constant portfolio `θ ∈ ℝᵈ` turns
zero cost into a sure non-negative discounted gain `⟪θ, Y⟫` with a chance of profit —
any `θ` whose gain `⟪θ, Y⟫` is `≥ 0` a.e. already has `⟪θ, Y⟫ = 0` a.e. -/
def NoArbitrage : Prop :=
  ∀ θ : EuclideanSpace ℝ (Fin d), 0 ≤ᵐ[P] (fun ω => inner ℝ θ (Y ω)) →
    (fun ω => inner ℝ θ (Y ω)) =ᵐ[P] 0

/-- **Equivalent martingale measure** (one period, vector): `Q ~ P`, `Y` is
`Q`-integrable, and `E_Q[Y] = 0 ∈ ℝᵈ`. -/
structure IsEMM (Q : Measure Ω) : Prop where
  prob : IsProbabilityMeasure Q
  absP : Q ≪ P
  Pabs : P ≪ Q
  int  : Integrable Y Q
  fair : ∫ ω, Y ω ∂Q = 0

omit [IsProbabilityMeasure P] in
/-- **Forward direction**: an equivalent martingale measure precludes arbitrage.
Under `Q`, `∫ ⟪θ, Y⟫ ∂Q = ⟪θ, E_Q[Y]⟫ = 0`, so a non-negative `⟪θ, Y⟫` is `0` a.e.;
equivalence transports this back to `P`. -/
theorem noArbitrage_of_isEMM {Q : Measure Ω} (hQ : IsEMM P Y Q) : NoArbitrage P Y := by
  haveI := hQ.prob
  intro θ hpos
  have hposQ : 0 ≤ᵐ[Q] (fun ω => inner ℝ θ (Y ω)) := hQ.absP.ae_le hpos
  have hint : ∫ ω, inner ℝ θ (Y ω) ∂Q = 0 := by
    rw [integral_inner hQ.int, hQ.fair, inner_zero_right]
  have hzeroQ : (fun ω => inner ℝ θ (Y ω)) =ᵐ[Q] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hposQ (hQ.int.const_inner θ)).mp hint
  exact hQ.Pabs.ae_eq hzeroQ

end MathFin.OnePeriodVector
