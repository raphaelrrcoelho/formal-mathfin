/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Futures.Black76
public import MathFin.BlackScholes.PDE

/-!
# Black-76 Greeks

For the Black-76 futures call price `V_B(F, σ, T) = e^{-rT} · [F Φ(d₁) − K Φ(d₂)]`
with `d_i = bsdi F K 0 σ T` (i.e., zero drift), the Greeks are simply the BS
Greeks evaluated at `r = 0` and post-multiplied by the discount factor `e^{-rT}`:

* `hasDerivAt_blackV_F` — δ = e^{-rT} · Φ(d₁).
* `hasDerivAt_blackV_FF` — γ = e^{-rT} · ϕ(d₁) / (F σ √T).
* `hasDerivAt_blackV_sigma` — vega = e^{-rT} · F · ϕ(d₁) · √T.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- Black-76 futures call price as a function of `(F, σ, T)` plus discount rate `r`.
Specialization of `bsV` to zero drift, times an external discount `e^{-rT}`. -/
noncomputable def blackV (K σ : ℝ) (r F T : ℝ) : ℝ :=
  Real.exp (-(r * T)) * bsV K 0 σ F T

/-- **Black-76 delta**: `∂_F V_B = e^{-rT} · Φ(d₁)`. -/
lemma hasDerivAt_blackV_F {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (r : ℝ)
    {F T : ℝ} (hF : 0 < F) (hT : 0 < T) :
    HasDerivAt (fun f ↦ blackV K σ r f T) (Real.exp (-(r * T)) * Phi (bsd1 F K 0 σ T)) F := by
  have h_bs := hasDerivAt_bsV_S (r := 0) hK hσ hF hT
  have h := h_bs.const_mul (Real.exp (-(r * T)))
  exact h

/-- **Black-76 gamma**: `∂²_F V_B = e^{-rT} · ϕ(d₁) / (F σ √T)`. -/
lemma hasDerivAt_blackV_FF {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (r : ℝ)
    {F T : ℝ} (hF : 0 < F) (hT : 0 < T) :
    HasDerivAt (fun f ↦ Real.exp (-(r * T)) * Phi (bsd1 f K 0 σ T))
      (Real.exp (-(r * T)) * gaussianPDFReal 0 1 (bsd1 F K 0 σ T) / (F * σ * Real.sqrt T)) F := by
  have h_bs := hasDerivAt_bsV_SS (r := 0) hK hσ hF hT
  have h := h_bs.const_mul (Real.exp (-(r * T)))
  convert h using 1 <;> try rfl
  ring

/-- **Black-76 vega**: `∂_σ V_B = e^{-rT} · F · ϕ(d₁) · √T`. -/
lemma hasDerivAt_blackV_sigma {K : ℝ} (hK : 0 < K) (r : ℝ)
    {F σ T : ℝ} (hF : 0 < F) (hσ : 0 < σ) (hT : 0 < T) :
    HasDerivAt (fun s ↦ blackV K s r F T)
      (Real.exp (-(r * T)) * F * gaussianPDFReal 0 1 (bsd1 F K 0 σ T) * Real.sqrt T) σ := by
  have h_bs := hasDerivAt_bsV_sigma (r := 0) hK hF hσ hT
  have h := h_bs.const_mul (Real.exp (-(r * T)))
  convert h using 1 <;> try rfl
  ring

/-- **Black-76 rho**: `∂_r V_B = -T · V_B`.

`V_B = e^{-rT} · bsV(K, 0, σ, F, T)`; the inner bsV is `r`-independent (zero-drift
futures setup), so only the discount factor contributes. Clean closed form. -/
lemma hasDerivAt_blackV_r (K σ F T : ℝ) (r : ℝ) :
    HasDerivAt (fun r' ↦ blackV K σ r' F T)
      (-T * blackV K σ r F T) r := by
  have h_neg : HasDerivAt (fun r' : ℝ ↦ -(r' * T)) (-T) r := by
    have h := (hasDerivAt_id r).mul_const T
    convert h.neg using 1 <;> first | rfl | ring
  have h_exp : HasDerivAt (fun r' : ℝ ↦ Real.exp (-(r' * T)))
      (Real.exp (-(r * T)) * (-T)) r := h_neg.exp
  have h := h_exp.mul_const (bsV K 0 σ F T)
  unfold blackV
  convert h using 1 <;> try rfl
  ring

/-- **Black-76 theta** (`∂_T` form): `∂_T V_B = -r · V_B + e^{-rT} · σ · F · ϕ(d₁) / (2√T)`.

Product rule on `V_B = e^{-rT} · bsV(K, 0, σ, F, T)`:
* `∂_T e^{-rT} = -r · e^{-rT}`
* `∂_T bsV(K, 0, σ, F, T) = σ · F · ϕ(d₁) / (2√T)` from `hasDerivAt_bsV_tau` at `r = 0`. -/
lemma hasDerivAt_blackV_T {K σ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (r : ℝ)
    {F T : ℝ} (hF : 0 < F) (hT : 0 < T) :
    HasDerivAt (fun t ↦ blackV K σ r F t)
      (-r * blackV K σ r F T +
        Real.exp (-(r * T)) *
          (σ * F * gaussianPDFReal 0 1 (bsd1 F K 0 σ T) / (2 * Real.sqrt T))) T := by
  have h_neg : HasDerivAt (fun t : ℝ ↦ -(r * t)) (-r) T := by
    have h := (hasDerivAt_id T).const_mul r
    convert h.neg using 1 <;> first | rfl | ring
  have h_exp : HasDerivAt (fun t : ℝ ↦ Real.exp (-(r * t)))
      (Real.exp (-(r * T)) * (-r)) T := h_neg.exp
  have h_bsV := hasDerivAt_bsV_tau (r := 0) hK hσ hF hT
  have h := h_exp.mul h_bsV
  unfold blackV
  convert h using 1 <;> try rfl
  simp
  ring

end MathFin
