/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.FixedIncome.KMVMerton
public import MathFin.BlackScholes.RiskNeutralProbabilities

/-!
# KMV-Merton structural model: probabilistic content of `kmvPD`

The pre-existing `FixedIncome/KMVMerton.lean` defines `kmvPD := Phi(−kmvDD)`
and proves the algebraic survival identity `1 − kmvPD = Phi(kmvDD)`. The
*probabilistic content* — namely, that `kmvPD` is the actual risk-neutral
probability of default `Q({V_T ≤ F})` — was previously stated only in the
docstring.

This file proves the connection rigorously using `riskNeutralProb_S_T_gt_K`
from `BlackScholes/RiskNeutralProbabilities.lean`. With firm asset value
`V_T = bsTerminal V_0 r σ_V T (Z ·)` under the risk-neutral measure `Q` and
debt face `F`, the no-default probability is

  `Q({V_T > F}) = Phi(bsd2 V_0 F r σ_V T) = 1 − kmvPD`,

so default probability `Q({V_T ≤ F}) = kmvPD = Phi(−bsd2)`.

Additionally, the structural identity **equity = call on firm assets**
(Merton 1974) is recorded as a direct specialisation of `bs_call_formula`
with finance-specific variable renaming.

## Results

* `kmvPD_eq_one_sub_survival_probability`: connects `kmvPD` to the actual
  risk-neutral probability `Q({V_T > F})`.
* `merton_equity_eq_bs_call`: equity holders' value as the discounted
  expectation of `max(V_T − F, 0)` is the BS call closed form
  (`bs_call_formula` with `(S_0, K) ↦ (V_0, F)` and `σ ↦ σ_V`).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **KMV-Merton default probability identification**: under the BS lognormal
hypothesis for firm asset value `V_T = bsTerminal V_0 r σ_V T (Z ·)`,

  `kmvPD V_0 F r σ_V T = 1 − Q({ω | V_T(ω) > F}).toReal`.

The RHS is *one minus the risk-neutral survival probability*. Combined with
`riskNeutralProb_S_T_gt_K`, this gives `kmvPD` the genuine probabilistic
interpretation it was advertised to have. -/
theorem kmvPD_eq_one_sub_survival_probability
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V_0 F r σ_V T : ℝ} {Z : Ω → ℝ}
    (hV : 0 < V_0) (hF : 0 < F)
    (h : BSCallHyp Q V_0 F r σ_V T Z) :
    kmvPD V_0 F r σ_V T =
      1 - (Q {ω | bsTerminal V_0 r σ_V T (Z ω) > F}).toReal := by
  rw [riskNeutralProb_S_T_gt_K h]
  rw [← kmvDistanceToDefault_eq_bsd2 V_0 F r σ_V T hV hF]
  have := kmv_survival_eq_Phi_d2 V_0 F r σ_V T
  linarith

/-- **KMV-Merton survival probability closed form**: under the BS lognormal
hypothesis for the firm asset value `V_T = bsTerminal V_0 r σ_V T (Z ·)`, the
risk-neutral survival (no-default) probability *is* `Φ` of the distance to
default:

  `Q({ω | V_T(ω) > F}).toReal = Phi (kmvDistanceToDefault V_0 F r σ_V T)`.

This is the genuinely probabilistic survival statement — it computes the
measure of the no-default event itself through the lognormal tail
(`riskNeutralProb_S_T_gt_K`), not merely the CDF symmetry
`1 − Φ(−DD) = Φ(DD)` recorded in `KMVMerton.lean`. Complements
`kmvPD_eq_one_sub_survival_probability` (the PD identification) with the
closed form on the survival side. -/
theorem survival_probability_eq_Phi_distanceToDefault
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V_0 F r σ_V T : ℝ} {Z : Ω → ℝ}
    (hV : 0 < V_0) (hF : 0 < F)
    (h : BSCallHyp Q V_0 F r σ_V T Z) :
    (Q {ω | bsTerminal V_0 r σ_V T (Z ω) > F}).toReal =
      Phi (kmvDistanceToDefault V_0 F r σ_V T) := by
  rw [riskNeutralProb_S_T_gt_K h, kmvDistanceToDefault_eq_bsd2 V_0 F r σ_V T hV hF]

/-- **Equity-as-call-on-assets structural identity** (Merton 1974). In the
structural credit model, equity holders are protected by limited liability,
so the equity payoff at maturity is `max(V_T − F, 0)` (debt holders are
paid `F` first; equity gets the remainder, or nothing if `V_T < F`).
Therefore the discounted risk-neutral expectation of the equity payoff
equals the BS call price with `(S_0, K, σ) ↦ (V_0, F, σ_V)`.

This is *not a new derivation*: it is `bs_call_formula` applied with
finance-specific variable renaming. The first-principles content is the
recognition that the structural credit model is *literally* a BS call
problem — no extra mathematical machinery is needed beyond the lognormal
hypothesis on `V_T`. -/
theorem merton_equity_eq_bs_call
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V_0 F r σ_V T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q V_0 F r σ_V T Z) :
    ∫ ω, Real.exp (-r * T) *
        max (bsTerminal V_0 r σ_V T (Z ω) - F) 0 ∂Q =
      V_0 * Phi (bsd1 V_0 F r σ_V T) -
        F * Real.exp (-r * T) * Phi (bsd2 V_0 F r σ_V T) :=
  bs_call_formula h

end MathFin
