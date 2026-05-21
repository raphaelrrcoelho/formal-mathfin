/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholes.StrikeGreeks
import HybridVerify.BlackScholes.StrikeConvexity

/-!
# Breeden-Litzenberger: implied risk-neutral PDF from option prices

The Breeden-Litzenberger identity says the risk-neutral PDF of the terminal
asset price `S_T`, evaluated at strike `K`, equals `e^{rT}` times the second
strike-derivative of the European call price:

  `f_{S_T}(K) = e^{rT} · ∂²_K C(K)`.

Specialising to the BS model: `∂²_K bsV = e^{-rT} · ϕ(d_2)/(K σ √T)`
(`hasDerivAt_bsV_KK` in `StrikeGreeks.lean`), so

  `f_{S_T}(K) = ϕ(d_2(K)) / (K σ √T)`,

which is the lognormal density at `K` (parameters
`log S_0 + (r − σ²/2)T, σ² T`).

## Structural connection: PDF positivity = strike-convexity of the price

The non-negativity `0 ≤ f_{S_T}(K)` is *not* an independent fact. It is the
infinitesimal manifestation of the convexity chain that runs through this
library:

1. The call **payoff** is convex in `K` (`convexOn_call_payoff` in
   `StrikeConvexity.lean`).
2. Risk-neutral expectation preserves convexity (positive linear operator).
3. So the call **price** `K ↦ bsV K r σ S T` is convex in `K`.
4. So `∂²_K bsV ≥ 0`.
5. By Breeden-Litzenberger, `∂²_K bsV = e^{-rT} · f_{S_T}(K)`, so
   `f_{S_T}(K) ≥ 0`.

Steps 1, 4, 5 are formal lemmas in this library; steps 2-3 are conceptual
(risk-neutral expectation preserving convexity is the Jensen-inequality
direction for `E_Q`). The PDF positivity at step 5 is what
`lognormalTerminalPDF_nonneg` below records.

Results:

* `lognormalTerminalPDF`: definition.
* `breedenLitzenberger`: `∂²_K bsV(K) = e^{-rT} · lognormalTerminalPDF(K)`.
* `lognormalTerminalPDF_nonneg`: `0 ≤ lognormalTerminalPDF`, the
  infinitesimal face of payoff convexity (the discrete face is
  `butterfly_payoff_nonneg`).
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

/-- **Implied PDF non-negativity** = *infinitesimal* face of call-payoff
convexity in `K`. The same convexity that gives `butterfly_payoff_nonneg`
discretely gives `0 ≤ ∂²_K bsV` infinitesimally, and Breeden-Litzenberger
identifies this with `e^{-rT} · f_{S_T}(K)`. So `f_{S_T} ≥ 0` is the
non-negativity of the implied probability density — as it must be, since
it *is* a probability density. -/
theorem lognormalTerminalPDF_nonneg
    {S_0 r σ T K : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    0 ≤ lognormalTerminalPDF S_0 r σ T K := by
  unfold lognormalTerminalPDF
  have h_pdf_nn : 0 ≤ gaussianPDFReal 0 1 (bsd2 S_0 K r σ T) :=
    gaussianPDFReal_nonneg _ _ _
  have h_den_pos : 0 < K * σ * Real.sqrt T :=
    mul_pos (mul_pos hK hσ) (Real.sqrt_pos.mpr hT)
  exact div_nonneg h_pdf_nn h_den_pos.le

end HybridVerify
