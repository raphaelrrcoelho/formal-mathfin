/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackFutures
import HybridVerify.BlackScholesPDE

/-!
# Black-76 Greeks

For the Black-76 futures call price `V_B(F, σ, T) = e^{-rT} · [F Φ(d₁) − K Φ(d₂)]`
with `d_i = bsdi F K 0 σ T` (i.e., zero drift), the Greeks are simply the BS
Greeks evaluated at `r = 0` and post-multiplied by the discount factor `e^{-rT}`:

* `hasDerivAt_blackV_F` — δ = e^{-rT} · Φ(d₁).
* `hasDerivAt_blackV_FF` — γ = e^{-rT} · ϕ(d₁) / (F σ √T).
* `hasDerivAt_blackV_sigma` — vega = e^{-rT} · F · ϕ(d₁) · √T.
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- Black-76 futures call price as a function of `(F, σ, T)` plus discount rate `r`.
Specialization of `bsV` to zero drift, times an external discount `e^{-rT}`. -/
noncomputable def blackV (K σ : ℝ) (r F T : ℝ) : ℝ :=
  Real.exp (-(r * T)) * bsV K 0 σ F T

/-- **Black-76 delta**: `∂_F V_B = e^{-rT} · Φ(d₁)`. -/
lemma hasDerivAt_blackV_F {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (r : ℝ)
    {F T : ℝ} (hF : 0 < F) (hT : 0 < T) :
    HasDerivAt (fun f => blackV K σ r f T) (Real.exp (-(r * T)) * Phi (bsd1 F K 0 σ T)) F := by
  have h_bs := hasDerivAt_bsV_S (r := 0) hK hσ hF hT
  have h := h_bs.const_mul (Real.exp (-(r * T)))
  exact h

/-- **Black-76 gamma**: `∂²_F V_B = e^{-rT} · ϕ(d₁) / (F σ √T)`. -/
lemma hasDerivAt_blackV_FF {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (r : ℝ)
    {F T : ℝ} (hF : 0 < F) (hT : 0 < T) :
    HasDerivAt (fun f => Real.exp (-(r * T)) * Phi (bsd1 f K 0 σ T))
      (Real.exp (-(r * T)) * gaussianPDFReal 0 1 (bsd1 F K 0 σ T) / (F * σ * Real.sqrt T)) F := by
  have h_bs := hasDerivAt_bsV_SS (r := 0) hK hσ hF hT
  have h := h_bs.const_mul (Real.exp (-(r * T)))
  convert h using 1
  ring

/-- **Black-76 vega**: `∂_σ V_B = e^{-rT} · F · ϕ(d₁) · √T`. -/
lemma hasDerivAt_blackV_sigma {K : ℝ} (hK : 0 < K) (r : ℝ)
    {F σ T : ℝ} (hF : 0 < F) (hσ : 0 < σ) (hT : 0 < T) :
    HasDerivAt (fun s => blackV K s r F T)
      (Real.exp (-(r * T)) * F * gaussianPDFReal 0 1 (bsd1 F K 0 σ T) * Real.sqrt T) σ := by
  have h_bs := hasDerivAt_bsV_sigma (r := 0) hK hF hσ hT
  have h := h_bs.const_mul (Real.exp (-(r * T)))
  convert h using 1
  ring

end HybridVerify
