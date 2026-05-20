/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import HybridVerify.BlackScholesCall
import HybridVerify.BlackScholesPDE
import HybridVerify.BlackScholesPutGreeks
import HybridVerify.OptionStrikeProperties
import HybridVerify.GaussianRiskMeasures
import HybridVerify.RiskMeasureAxioms

/-!
# Put-price convexity in strike + VaR additivity at ρ = 1

Two corollaries that complete pairs of results we've already established:

* **Put-price convexity in `K`** matches the call-price convexity, since
  `bsP(K) − bsV(K) = K · e^{-rτ} − S` is linear in `K`. The two prices have
  identical second `K`-derivatives — a clean expression of put-call symmetry.
* **VaR additivity at perfect positive correlation** (`ρ = 1`): the gaussian
  subadditivity inequality becomes equality when the two losses are perfectly
  positively correlated. This is the extremal case where diversification
  provides no benefit.

Results:

* `gaussianPDFReal_zero_one_neg`: `ϕ(−x) = ϕ(x)` for the standard normal PDF.
* `hasDerivAt_bsP_KK`: `∂²_K bsP = e^{-rτ} · ϕ(d₂) / (K σ √τ)`, same as
  `∂²_K bsV`.
* `gaussianVaR_additive_at_rho_one`: at `ρ = 1`, VaR is additive.
* `gaussianCVaR_additive_at_rho_one`: at `ρ = 1`, CVaR is additive.
-/

namespace HybridVerify

open Real ProbabilityTheory

/-- **Standard normal PDF symmetry**: `ϕ(−x) = ϕ(x)`. -/
lemma gaussianPDFReal_zero_one_neg (z : ℝ) :
    gaussianPDFReal 0 1 (-z) = gaussianPDFReal 0 1 z := by
  unfold gaussianPDFReal
  congr 1
  ring

/-- **Put-price convexity in `K`**: `∂²_K bsP = e^{-rτ} · ϕ(d₂) / (K σ √τ)`,
identical to the call-price convexity. The proof goes through the put
strike-derivative `∂_K bsP = e^{-rτ} · Φ(−d₂)` from `OptionStrikeProperties`. -/
lemma hasDerivAt_bsP_KK {S r σ : ℝ} (hS : 0 < S) (hσ : 0 < σ)
    {K τ : ℝ} (hK : 0 < K) (hτ : 0 < τ) :
    HasDerivAt (fun k => Real.exp (-(r * τ)) * Phi (-bsd2 S k r σ τ))
      (Real.exp (-(r * τ)) *
        gaussianPDFReal 0 1 (bsd2 S K r σ τ) /
        (K * σ * Real.sqrt τ)) K := by
  have h_d2_K := hasDerivAt_bsd2_K S r σ τ hS hσ hτ hK
  have h_neg_d2 := h_d2_K.neg
  have h_Phi_neg_d2 := (hasDerivAt_Phi (-bsd2 S K r σ τ)).comp K h_neg_d2
  have h := h_Phi_neg_d2.const_mul (Real.exp (-(r * τ)))
  have h_pdf_sym : gaussianPDFReal 0 1 (-bsd2 S K r σ τ) =
      gaussianPDFReal 0 1 (bsd2 S K r σ τ) := gaussianPDFReal_zero_one_neg _
  have h_sqrt_τ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_τ_ne : Real.sqrt τ ≠ 0 := h_sqrt_τ_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hK_ne : K ≠ 0 := hK.ne'
  convert h using 1
  rw [h_pdf_sym]
  field_simp

/-- **Gaussian VaR additivity at perfect positive correlation** (`ρ = 1`):
the joint stdev becomes `σ₁ + σ₂` and the subadditivity inequality is an
equality. -/
lemma gaussianVaR_additive_at_rho_one {μ₁ μ₂ σ₁ σ₂ z : ℝ}
    (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    gaussianVaR (μ₁ + μ₂)
        (Real.sqrt (σ₁^2 + 2 * 1 * σ₁ * σ₂ + σ₂^2)) z =
      gaussianVaR μ₁ σ₁ z + gaussianVaR μ₂ σ₂ z := by
  unfold gaussianVaR
  have h_sum_sq : σ₁^2 + 2 * 1 * σ₁ * σ₂ + σ₂^2 = (σ₁ + σ₂)^2 := by ring
  rw [h_sum_sq]
  have h_sum_nn : 0 ≤ σ₁ + σ₂ := add_nonneg h₁ h₂
  rw [Real.sqrt_sq h_sum_nn]
  ring

/-- **Gaussian CVaR additivity at perfect positive correlation** (`ρ = 1`). -/
lemma gaussianCVaR_additive_at_rho_one {μ₁ μ₂ σ₁ σ₂ z α : ℝ}
    (h₁ : 0 ≤ σ₁) (h₂ : 0 ≤ σ₂) :
    gaussianCVaR (μ₁ + μ₂)
        (Real.sqrt (σ₁^2 + 2 * 1 * σ₁ * σ₂ + σ₂^2)) z α =
      gaussianCVaR μ₁ σ₁ z α + gaussianCVaR μ₂ σ₂ z α := by
  unfold gaussianCVaR
  have h_sum_sq : σ₁^2 + 2 * 1 * σ₁ * σ₂ + σ₂^2 = (σ₁ + σ₂)^2 := by ring
  rw [h_sum_sq]
  have h_sum_nn : 0 ≤ σ₁ + σ₂ := add_nonneg h₁ h₂
  rw [Real.sqrt_sq h_sum_nn]
  ring

end HybridVerify
