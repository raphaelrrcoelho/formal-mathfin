/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholes.Call
import HybridVerify.FixedIncome.Credit

/-!
# KMV-Merton structural credit model

In the Merton (1974) / KMV structural credit-risk model, the firm's asset
value `V_t` follows the same lognormal dynamics as a Black-Scholes asset.
Default occurs at maturity `T` if `V_T < F`, where `F` is the face value
of the firm's debt.

Under the risk-neutral measure, the **distance to default** at time `0` is
exactly the BS `d_2` parameter with `V_0` as spot and `F` as strike:

  `d_2^{KMV} = (log(V_0 / F) + (r − σ_V²/2) · T) / (σ_V · √T)`,

and the **risk-neutral probability of default** is

  `PD = Q(V_T < F) = Φ(−d_2^{KMV})`.

This is the natural counterpart to the reduced-form `survivalProbability` in
`Credit.lean`: the same library now has both *structural* (asset-value-driven)
and *reduced-form* (hazard-driven) credit. They model the same default event
through different lenses.

## Why this is just BS in disguise

The Merton (1974) insight: a corporate debt-holder is short a put on the firm's
assets (the firm is "called away" by the equity-holders if `V_T ≥ F`, leaving
the debt-holder with `F`; otherwise the firm defaults and debt-holders recover
`V_T < F`). So the credit-risky bond price is `F · e^{−rT} − bsP(F, r, σ_V, V_0, T)`.
The default probability `PD = Φ(−d_2)` falls out of the same BS machinery.

## Results

* `kmvDistanceToDefault`: `d_2^{KMV}` with firm value as spot, debt as strike.
* `kmvPD`: `Φ(−d_2^{KMV})`.
* `kmvPD_nonneg`, `kmvPD_le_one`: PD is in `[0, 1]`.
* `kmv_survival_eq_Phi_d2`: `1 − PD = Φ(d_2^{KMV})`.
* `kmvDistanceToDefault_eq_bsd2`: the namesake identity.
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Distance to default** in the KMV-Merton model: the BS `d_2` parameter
with firm value `V_0` as spot and face debt `F` as strike. -/
noncomputable def kmvDistanceToDefault (V_0 F r σ_V T : ℝ) : ℝ :=
  bsd2 V_0 F r σ_V T

/-- **Risk-neutral probability of default** at maturity `T` in the KMV-Merton
model: `PD = Φ(−d_2^{KMV})`. -/
noncomputable def kmvPD (V_0 F r σ_V T : ℝ) : ℝ :=
  Phi (-(kmvDistanceToDefault V_0 F r σ_V T))

/-- The KMV-Merton distance to default equals the BS `d_2` parameter (with
firm value as spot). Trivial by definition, recorded for cross-referencing. -/
lemma kmvDistanceToDefault_eq_bsd2 (V_0 F r σ_V T : ℝ) :
    kmvDistanceToDefault V_0 F r σ_V T = bsd2 V_0 F r σ_V T := rfl

/-- **PD ≥ 0**: probabilities are non-negative. -/
lemma kmvPD_nonneg (V_0 F r σ_V T : ℝ) : 0 ≤ kmvPD V_0 F r σ_V T :=
  Phi_nonneg _

/-- **PD ≤ 1**: probabilities are at most 1. -/
lemma kmvPD_le_one (V_0 F r σ_V T : ℝ) : kmvPD V_0 F r σ_V T ≤ 1 := by
  unfold kmvPD
  have h_sum : Phi (-(kmvDistanceToDefault V_0 F r σ_V T)) +
               Phi (kmvDistanceToDefault V_0 F r σ_V T) = 1 := by
    have := Phi_add_Phi_neg (kmvDistanceToDefault V_0 F r σ_V T)
    linarith
  have h_pos : 0 ≤ Phi (kmvDistanceToDefault V_0 F r σ_V T) := Phi_nonneg _
  linarith

/-- **Survival = 1 − PD = Φ(d_2^{KMV})**: the risk-neutral probability of no
default. -/
theorem kmv_survival_eq_Phi_d2 (V_0 F r σ_V T : ℝ) :
    1 - kmvPD V_0 F r σ_V T = Phi (kmvDistanceToDefault V_0 F r σ_V T) := by
  unfold kmvPD
  have := Phi_add_Phi_neg (kmvDistanceToDefault V_0 F r σ_V T)
  linarith

end HybridVerify
