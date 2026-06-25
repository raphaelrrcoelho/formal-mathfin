/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# One-period FTAP on a general probability space (scalar)

The Föllmer–Schied (Thm 1.55) / one-period Dalang–Morton–Willinger Fundamental
Theorem of Asset Pricing for a single scalar discounted excess return `Y` on an
**arbitrary** probability space `(Ω, P)`: no arbitrage ⟺ there is an equivalent
martingale measure `Q ~ P` with `Y` integrable and `E_Q[Y] = 0`.

This is the step from finite Ω (`Foundations/FTAPDiscrete.lean`) to genuine
measure theory: `Y ∈ L⁰` (not bounded, integrability not free). The backward
direction is the elementary route — a bounded-density reduction to `L¹`, a scalar
no-arbitrage dichotomy, and a two-region `withDensity` construction that
re-weights the up- and down-moves until `Y` is fair (no Hahn–Banach, no
Kreps–Yan).

## Scope

One trading period, **one scalar asset**, arbitrary `(Ω, P)`. The general-Ω
**multi-period** Dalang–Morton–Willinger theorem (which glues one-period
conditional markets and needs a measurable selection theorem) and the `d`-asset
case remain open.

## Main result

* `MathFin.OnePeriod.ftap_one_period`
-/

@[expose] public section

namespace MathFin.OnePeriod

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  (Y : Ω → ℝ)

/-- **No arbitrage**: no scalar position `θ` turns zero wealth into a sure
non-loss with a chance of gain — any `θ` whose discounted gain `θ · Y` is `≥ 0`
a.e. already has `θ · Y = 0` a.e. -/
def NoArbitrage : Prop :=
  ∀ θ : ℝ, 0 ≤ᵐ[P] (fun ω => θ * Y ω) → (fun ω => θ * Y ω) =ᵐ[P] 0

/-- **Equivalent martingale measure** (one period): `Q ~ P`, `Y` is `Q`-integrable,
and `E_Q[Y] = 0`. -/
structure IsEMM (Q : Measure Ω) : Prop where
  prob : IsProbabilityMeasure Q
  absP : Q ≪ P
  Pabs : P ≪ Q
  int  : Integrable Y Q
  fair : ∫ ω, Y ω ∂Q = 0

omit [IsProbabilityMeasure P] in
/-- **Forward direction**: an equivalent martingale measure precludes arbitrage.
Under `Q`, a non-negative discounted gain integrates to `θ · E_Q[Y] = 0`, so it is
`0` a.e.; equivalence transports this back to `P`. -/
theorem noArbitrage_of_isEMM {Q : Measure Ω} (hQ : IsEMM P Y Q) : NoArbitrage P Y := by
  haveI := hQ.prob
  intro θ hpos
  have hposQ : 0 ≤ᵐ[Q] (fun ω => θ * Y ω) := hQ.absP.ae_le hpos
  have hintegral : ∫ ω, θ * Y ω ∂Q = 0 := by
    rw [integral_const_mul, hQ.fair, mul_zero]
  have hzeroQ : (fun ω => θ * Y ω) =ᵐ[Q] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hposQ (hQ.int.const_mul θ)).mp hintegral
  exact hQ.Pabs.ae_eq hzeroQ

end MathFin.OnePeriod
