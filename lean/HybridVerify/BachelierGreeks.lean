/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BachelierModel
import HybridVerify.BlackScholesPDE

/-!
# Bachelier model Greeks

For the Bachelier call price `V_bach(S, σ, T) = (S − K) Φ(d) + σ √T ϕ(d)`
where `d = (S − K)/(σ √T)`, we derive the two first-order Greeks:

* **Delta**: `∂V/∂S = Φ(d)`. The chain-rule contributions through `d` cancel
  via the identity `(S − K)/(σ √T) = d`.
* **Vega**: `∂V/∂σ = √T · ϕ(d)`. Similar cancellation, using `(S − K) · d / σ =
  √T · d² · ϕ(d)`.

These parallel the Black–Scholes Greeks but with much simpler algebra
(no exponential, no log).
-/

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- The Bachelier call price as a function of `(S, σ)`:
`V_bach = (S − K) Φ(d) + σ √T ϕ(d)` where `d = (S − K)/(σ √T)`. -/
noncomputable def bachelierV (K σ T : ℝ) (S : ℝ) : ℝ :=
  (S - K) * Phi (bachelierD S K σ T) +
    σ * Real.sqrt T * gaussianPDFReal 0 1 (bachelierD S K σ T)

/-- `(d/dz) ϕ(0, 1, z) = -z · ϕ(0, 1, z)`. -/
private lemma hasDerivAt_pdf (z : ℝ) :
    HasDerivAt (fun z' : ℝ => gaussianPDFReal 0 1 z')
      (-(z * gaussianPDFReal 0 1 z)) z := by
  have h := (hasDerivAt_neg_gaussianPDFReal_zero_one z).neg
  have h_eq : ((-fun z' : ℝ => -gaussianPDFReal 0 1 z') : ℝ → ℝ)
            = fun z' : ℝ => gaussianPDFReal 0 1 z' := by funext z'; simp
  rw [h_eq] at h
  exact h

/-- `∂_S [bachelierD S K σ T] = 1 / (σ √T)`. -/
private lemma hasDerivAt_bachelierD_S {K σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) (S : ℝ) :
    HasDerivAt (fun s => bachelierD s K σ T) (1 / (σ * Real.sqrt T)) S := by
  have h_sqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_στ_pos : 0 < σ * Real.sqrt T := mul_pos hσ h_sqrt_pos
  have h_num : HasDerivAt (fun s : ℝ => s - K) 1 S := by
    simpa using (hasDerivAt_id S).sub_const K
  exact h_num.div_const (σ * Real.sqrt T)

/-- **Bachelier delta**: `∂V/∂S = Φ(d)`. -/
lemma hasDerivAt_bachelierV_S {K σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) (S : ℝ) :
    HasDerivAt (fun s => bachelierV K σ T s) (Phi (bachelierD S K σ T)) S := by
  have h_sqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_sqrt_ne : Real.sqrt T ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have h_d_S := hasDerivAt_bachelierD_S (K := K) hσ hT S
  -- Chain rule: ∂_S Φ(d(S)) = ϕ(d) · ∂_S d
  have h_Phi_chain := (hasDerivAt_Phi (bachelierD S K σ T)).comp S h_d_S
  -- Chain rule: ∂_S ϕ(d(S)) = -d · ϕ(d) · ∂_S d
  have h_pdf_chain := (hasDerivAt_pdf (bachelierD S K σ T)).comp S h_d_S
  -- ∂_S [(S - K)] = 1
  have h_S_sub : HasDerivAt (fun s : ℝ => s - K) 1 S := by
    simpa using (hasDerivAt_id S).sub_const K
  -- ∂_S [(S-K) · Φ(d(S))] = Φ(d) + (S-K) · ϕ(d) · ∂_S d
  have h_term1 := h_S_sub.mul h_Phi_chain
  -- ∂_S [σ √T · ϕ(d(S))] = σ √T · (-d ϕ(d)) · ∂_S d
  have h_term2 := h_pdf_chain.const_mul (σ * Real.sqrt T)
  have h_full := h_term1.add h_term2
  unfold bachelierV
  convert h_full using 1
  -- Value match: (S - K) ϕ(d) · 1/(σ√T) - σ√T · d · ϕ(d) · 1/(σ√T)
  --            = ϕ(d) · [(S-K)/(σ√T) - d] = ϕ(d) · [d - d] = 0
  -- so Φ(d) = Φ(d) + 0. trivially.
  simp only [Function.comp]
  show Phi (bachelierD S K σ T) =
    (1 * Phi (bachelierD S K σ T) + (S - K) * (gaussianPDFReal 0 1 (bachelierD S K σ T) * (1 / (σ * Real.sqrt T))))
    + σ * Real.sqrt T * (-(bachelierD S K σ T * gaussianPDFReal 0 1 (bachelierD S K σ T)) * (1 / (σ * Real.sqrt T)))
  rw [bachelierD]
  field_simp
  ring

/-- **Bachelier vega**: `∂V/∂σ = √T · ϕ(d)`. -/
lemma hasDerivAt_bachelierV_sigma {K T : ℝ} (hT : 0 < T)
    {S σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun s => bachelierV K s T S)
      (Real.sqrt T * gaussianPDFReal 0 1 (bachelierD S K σ T)) σ := by
  have h_sqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h_sqrt_ne : Real.sqrt T ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  -- ∂_σ [bachelierD] = -(S - K) / (σ² √T) = -d/σ
  have h_d_σ : HasDerivAt (fun s => bachelierD S K s T)
      (-((S - K) / (σ^2 * Real.sqrt T))) σ := by
    have h_quot : HasDerivAt (fun s : ℝ => (S - K) / (s * Real.sqrt T))
        ((0 * (σ * Real.sqrt T) - (S - K) * (1 * Real.sqrt T)) / (σ * Real.sqrt T)^2) σ := by
      have h_const : HasDerivAt (fun _ : ℝ => (S - K)) 0 σ := hasDerivAt_const _ _
      have h_denom : HasDerivAt (fun s : ℝ => s * Real.sqrt T) (1 * Real.sqrt T) σ := by
        simpa using (hasDerivAt_id σ).mul_const (Real.sqrt T)
      exact h_const.div h_denom (mul_pos hσ h_sqrt_pos).ne'
    convert h_quot using 1
    field_simp
    ring
  -- Chain rules
  have h_Phi_chain := (hasDerivAt_Phi (bachelierD S K σ T)).comp σ h_d_σ
  have h_pdf_chain := (hasDerivAt_pdf (bachelierD S K σ T)).comp σ h_d_σ
  -- ∂_σ [(S-K) Φ(d(σ))] = (S-K) ϕ(d) · ∂_σ d
  have h_term1 := h_Phi_chain.const_mul (S - K)
  -- ∂_σ [σ √T] = √T
  have h_σ_sqrt : HasDerivAt (fun s : ℝ => s * Real.sqrt T) (Real.sqrt T) σ := by
    simpa using (hasDerivAt_id σ).mul_const (Real.sqrt T)
  -- ∂_σ [σ √T · ϕ(d(σ))] = √T · ϕ(d) + σ √T · (-d ϕ(d)) · ∂_σ d
  have h_term2 := h_σ_sqrt.mul h_pdf_chain
  have h_full := h_term1.add h_term2
  unfold bachelierV
  convert h_full using 1
  simp only [Function.comp]
  rw [bachelierD]
  field_simp
  ring

end HybridVerify
