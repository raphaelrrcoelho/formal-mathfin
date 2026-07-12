/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Continuous-time market vocabulary: `IsEMM`, simple strategies, no-arbitrage

A **model-agnostic** frame for the continuous-time first fundamental theorem of asset
pricing (FTAP), parametric over a finite-dimensional real inner-product-space-valued
discounted price process `S : ℝ≥0 → Ω → F`. The Black–Scholes model (`ContinuousFTAP.lean`)
instantiates it at `F = ℝ`; a multi-asset model would instantiate at `F = Fin n → ℝ`.

* `IsEMM S Q` — `Q` is an equivalent martingale measure for `S`: `Q ≈ P` (mutual absolute
  continuity) and `S` is a `Q`-martingale w.r.t. the filtration `𝓕`.
* `SimpleStrategy 𝓕 F` — a piecewise-constant, predictable, bounded trading strategy:
  finitely many trading dates `time : Fin (N+1) → ℝ≥0` and `𝓕`-measurable bounded holdings
  `hold : Fin N → Ω → F` between consecutive dates.
* `SimpleStrategy.gains` — the discounted terminal gains of a simple strategy against `S`.
* `NoArbitrageSimple S` — no simple strategy's gains are `P`-a.s. nonnegative and strictly
  positive on a `P`-non-null set.

## Scope: meaning-1 (operational) vs. meaning-2 (Delbaen–Schachermayer) FTAP

This file builds **meaning 1**: an EMM for a *given* process, restricted to the honest,
economically transparent class of *simple* (piecewise-constant) strategies. It deliberately
does **not** build meaning 2, the Delbaen–Schachermayer theorem (`NFLVR ⟺ ∃ EMM` for a
general locally-bounded semimartingale, admissible strategies over a continuum of trading
times, and the general stochastic integral `∫ φ dS`). Absent by design:

* general **admissible** strategies (not just piecewise-constant) and the general stochastic
  integral `∫ φ dS` against a semimartingale;
* **NFLVR** (no free lunch with vanishing risk) and its distinction from plain no-arbitrage;
* the **converse** direction `NoArbitrageSimple S → ∃ Q, IsEMM S Q`, and closedness of the
  set of claims super-replicable from zero wealth (the Kreps–Yan / Hahn–Banach core DS needs).

`IsEMM` here is stated *on a process* `S`, exactly the object Delbaen–Schachermayer's theorem
would produce — so this frame is a strict sub-object of the DS one, and extending it to
meaning 2 is additive (new strategy class + new theorem), not a rewrite.
-/

@[expose] public section

namespace MathFin.ContinuousMarket

open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `Q` is an **equivalent martingale measure (EMM)** for the discounted price process `S`:
`Q` is a probability measure mutually absolutely continuous with `P` (`Q ≈ P`), and `S` is a
`Q`-martingale w.r.t. the filtration `𝓕`. -/
structure IsEMM (S : ℝ≥0 → Ω → F) (Q : Measure Ω) : Prop where
  isProb : IsProbabilityMeasure Q
  ac : Q ≪ P
  ac' : P ≪ Q
  martingale : Martingale S 𝓕 Q

/-- A **simple strategy**: finitely many trading dates `time 0 ≤ time 1 ≤ ⋯ ≤ time N`, with
piecewise-constant, `𝓕`-predictable, bounded holdings `hold i` held over `(time i, time i+1]`.
Does not depend on any measure — it is a purely path-space/filtration object. -/
structure SimpleStrategy (𝓕 : Filtration ℝ≥0 mΩ) (F : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  N : ℕ
  time : Fin (N + 1) → ℝ≥0
  mono : Monotone time
  hold : Fin N → Ω → F
  meas : ∀ i : Fin N, StronglyMeasurable[𝓕 (time i.castSucc)] (hold i)
  bdd : ∃ K : ℝ, ∀ (i : Fin N) ω, ‖hold i ω‖ ≤ K

/-- The **discounted terminal gains** of a simple strategy `ψ` against the price process `S`:
`∑ᵢ ⟪hold i, S(time i+1) − S(time i)⟫`. -/
noncomputable def SimpleStrategy.gains (ψ : SimpleStrategy 𝓕 F)
    (S : ℝ≥0 → Ω → F) (ω : Ω) : ℝ :=
  ∑ i : Fin ψ.N, ⟪ψ.hold i ω, S (ψ.time i.succ) ω - S (ψ.time i.castSucc) ω⟫_ℝ

/-- **No simple-strategy arbitrage**: no simple strategy's gains against `S` are `P`-a.s.
nonnegative and strictly positive on a `P`-non-null set. -/
def NoArbitrageSimple (S : ℝ≥0 → Ω → F) : Prop :=
  ∀ ψ : SimpleStrategy 𝓕 F, (0 ≤ᵐ[P] fun ω ↦ ψ.gains S ω) →
    P {ω | 0 < ψ.gains S ω} = 0

end MathFin.ContinuousMarket
