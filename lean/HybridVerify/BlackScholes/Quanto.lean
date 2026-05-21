/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Quanto correction

A **quanto** is a derivative whose payoff is denominated in a different currency
from its underlying. The canonical example: a payoff `max(S_T^foreign − K, 0)`
paid in domestic currency, where `S^foreign` is a foreign asset.

Under the domestic risk-neutral measure, the foreign asset acquires a
*quanto-adjusted drift*

  `μ^{quanto} = r_dom − ρ · σ_S · σ_FX`,

where `ρ` is the correlation between the asset's log-return and the FX rate's
log-return, and `σ_S`, `σ_FX` are the respective volatilities. The resulting
forward price under the domestic measure is

  `F^{quanto} = S_0 · exp((r_dom − ρ σ_S σ_FX) · T)`,

vs the un-adjusted domestic forward

  `F^{dom} = S_0 · exp(r_dom · T)`.

The **quanto correction factor** is the multiplicative ratio:

  `F^{quanto} / F^{dom} = exp(−ρ σ_S σ_FX · T)`.

## Why this matters

Hedging quanto risk requires modelling the joint dynamics of the asset and the
FX rate. The correction is *exactly* the log-covariance term that appears in
the joint MGF: positive correlation between the asset and the FX rate reduces
the forward (correction `< 1`), negative correlation increases it.

## Results

* `quantoForward`: the quanto-adjusted forward.
* `quanto_correction_factor`: ratio to the un-adjusted forward.
-/

namespace HybridVerify

open Real

/-- **Quanto-adjusted forward**: foreign asset's forward price under the
domestic risk-neutral measure. -/
noncomputable def quantoForward (S_0 r_dom ρ σ_S σ_FX T : ℝ) : ℝ :=
  S_0 * Real.exp ((r_dom - ρ * σ_S * σ_FX) * T)

/-- **Quanto correction factor**: the multiplicative ratio of the quanto-adjusted
forward to the un-adjusted domestic forward equals `exp(−ρ σ_S σ_FX · T)`.
Positive correlation reduces the forward; negative correlation increases it. -/
theorem quanto_correction_factor (S_0 r_dom ρ σ_S σ_FX T : ℝ) (hS : 0 < S_0) :
    quantoForward S_0 r_dom ρ σ_S σ_FX T / (S_0 * Real.exp (r_dom * T))
      = Real.exp (-(ρ * σ_S * σ_FX * T)) := by
  unfold quantoForward
  have hS_ne : S_0 ≠ 0 := hS.ne'
  have h_exp_pos : 0 < Real.exp (r_dom * T) := Real.exp_pos _
  have h_exp_ne : Real.exp (r_dom * T) ≠ 0 := h_exp_pos.ne'
  rw [mul_div_mul_left _ _ hS_ne, ← Real.exp_sub]
  congr 1
  ring

end HybridVerify
