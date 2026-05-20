/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholes.StrikeGreeks

/-!
# Breeden-Litzenberger: implied risk-neutral PDF from option prices

The Breeden-Litzenberger identity says the risk-neutral PDF of the terminal
asset price `S_T`, evaluated at strike `K`, equals `e^{rT}` times the second
strike-derivative of the European call price:

  `f_{S_T}(K) = e^{rT} · ∂²_K C(K)`.

Specializing to the BS model: `∂²_K bsV = e^{-rT} · ϕ(d_2)/(K σ √T)`
(`hasDerivAt_bsV_KK` in `StrikeGreeks.lean`), so

  `f_{S_T}(K) = ϕ(d_2(K)) / (K σ √T)`,

which is exactly the lognormal density at `K` (with parameters
`log S_0 + (r − σ²/2)T, σ² T`).

We package this as: the second strike-derivative of the BS call equals
`e^{-rT} · lognormalTerminalPDF(K)`, where the latter is the natural
re-expression of the lognormal density in terms of `bsd2`.

Results:

* `lognormalTerminalPDF`: definition.
* `breedenLitzenberger`: `∂²_K bsV(K) = e^{-rT} · lognormalTerminalPDF(K)`.
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Lognormal PDF of `S_T`** at strike `K`, expressed via the BS `d_2`
parameter: `f(K) = ϕ(d_2(K)) / (K · σ · √T)`. -/
noncomputable def lognormalTerminalPDF (S_0 r σ T K : ℝ) : ℝ :=
  gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) / (K * σ * Real.sqrt T)

/-- **Breeden-Litzenberger formula** under the Black-Scholes model: the
discounted PDF of `S_T` at `K` equals the second strike-derivative of the
call price. Stated as the derivative of the first strike-derivative
`-(e^{-rT}·Φ(d_2))` of `bsV`. -/
theorem breedenLitzenberger {S_0 r σ : ℝ} (hS : 0 < S_0) (hσ : 0 < σ)
    {K T : ℝ} (hK : 0 < K) (hT : 0 < T) :
    HasDerivAt (fun k => -(Real.exp (-(r * T)) * Phi (bsd2 S_0 k r σ T)))
      (Real.exp (-(r * T)) * lognormalTerminalPDF S_0 r σ T K) K := by
  have h := hasDerivAt_bsV_KK (S := S_0) (r := r) (σ := σ) hS hσ hK hT
  convert h using 1
  unfold lognormalTerminalPDF
  have hK_ne : K ≠ 0 := hK.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hsqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsqrtT_ne : Real.sqrt T ≠ 0 := hsqrtT_pos.ne'
  field_simp

end HybridVerify
