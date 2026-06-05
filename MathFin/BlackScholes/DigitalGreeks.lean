/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.PDE
public import MathFin.BlackScholes.Bachelier

/-!
# Black–Scholes digital option Greeks

For the two digital (binary) European options:

* **Cash-or-nothing** call price `V_cash(S, τ) = e^{-rτ} Φ(d₂)`.
* **Asset-or-nothing** call price `V_asset(S, τ) = S Φ(d₁)`.

We derive their deltas and the asset-side gamma:

* `hasDerivAt_bsCashDigital_S` — δ_cash = e^{-rτ} ϕ(d₂) / (S σ √τ).
* `hasDerivAt_bsAssetDigital_S` — δ_asset = Φ(d₁) + ϕ(d₁) / (σ √τ).
* `hasDerivAt_bsAssetDigital_SS` — γ_asset = -ϕ(d₁) · d₂ / (S σ² τ).

(The latter follows from the BS magic identity `K e^{-rτ} ϕ(d₂) = S ϕ(d₁)`
which collapses the `S · ϕ(d₁) · ∂_S d₁` chain-rule term, and uses the
clean identity `σ√τ − d₁ = -d₂`.)
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- Cash-or-nothing digital call price as a function of `(S, τ)`. -/
noncomputable def bsCashDigital (K r σ : ℝ) (S τ : ℝ) : ℝ :=
  Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ)

/-- Asset-or-nothing digital call price as a function of `(S, τ)`. -/
noncomputable def bsAssetDigital (K r σ : ℝ) (S τ : ℝ) : ℝ :=
  S * Phi (bsd1 S K r σ τ)

/-- **Cash-or-nothing delta**: `∂_S V_cash = e^{-rτ} ϕ(d₂) / (S σ √τ)`.

Direct chain rule on `Φ ∘ d₂(S)`. -/
lemma hasDerivAt_bsCashDigital_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s => bsCashDigital K r σ s τ)
      (Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) / (S * σ * Real.sqrt τ)) S := by
  have h_d2_S := hasDerivAt_bsd2_S (r := r) hK hσ hτ hS
  have h_Phi_d2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp S h_d2_S
  have h := h_Phi_d2.const_mul (Real.exp (-(r * τ)))
  unfold bsCashDigital
  convert h using 1
  ring

/-- **Asset-or-nothing delta**: `∂_S V_asset = Φ(d₁) + ϕ(d₁) / (σ √τ)`.

The chain rule gives `Φ(d₁) + S · ϕ(d₁) · ∂_S d₁ = Φ(d₁) + S · ϕ(d₁) · 1/(S σ √τ)
= Φ(d₁) + ϕ(d₁) / (σ √τ)`. -/
lemma hasDerivAt_bsAssetDigital_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s => bsAssetDigital K r σ s τ)
      (Phi (bsd1 S K r σ τ) + gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (σ * Real.sqrt τ)) S := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  have h_d1_S := hasDerivAt_bsd1_S (r := r) hK hσ hτ hS
  have h_Phi_d1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp S h_d1_S
  have h_id : HasDerivAt (fun s : ℝ => s) 1 S := hasDerivAt_id S
  have h := h_id.mul h_Phi_d1
  unfold bsAssetDigital
  convert h using 1
  simp only [Function.comp_apply]
  field_simp

/-- **Asset-or-nothing gamma**: `∂²V_asset/∂S² = -ϕ(d₁) · d₂ / (S σ² τ)`.

Differentiating δ_asset = Φ(d₁) + ϕ(d₁)/(σ√τ): the Φ-term contributes
`ϕ(d₁) · ∂_S d₁ = ϕ(d₁)/(Sσ√τ)`, and the ϕ-term contributes
`-d₁ ϕ(d₁) · ∂_S d₁ / (σ√τ) = -d₁ ϕ(d₁)/(Sσ²τ)`. Sum via `σ√τ − d₁ = -d₂`. -/
lemma hasDerivAt_bsAssetDigital_SS {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt
      (fun s => Phi (bsd1 s K r σ τ) +
        gaussianPDFReal 0 1 (bsd1 s K r σ τ) / (σ * Real.sqrt τ))
      (-(gaussianPDFReal 0 1 (bsd1 S K r σ τ) *
        bsd2 S K r σ τ / (S * σ ^ 2 * τ))) S := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  have h_sqrt_sq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  have h_d1_S := hasDerivAt_bsd1_S (r := r) hK hσ hτ hS
  -- ∂_S Φ(d₁) = ϕ(d₁) · ∂_S d₁
  have h_Phi := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp S h_d1_S
  -- ∂_S ϕ(d₁) = -d₁ ϕ(d₁) · ∂_S d₁
  have h_pdf := (hasDerivAt_gaussianPDFReal_zero_one (bsd1 S K r σ τ)).comp S h_d1_S
  -- ∂_S [ϕ(d₁) / (σ √τ)] = (∂_S ϕ(d₁)) / (σ √τ)
  have h_pdf_div := h_pdf.div_const (σ * Real.sqrt τ)
  have h_full := h_Phi.add h_pdf_div
  convert h_full using 1
  rw [show bsd2 S K r σ τ = bsd1 S K r σ τ - σ * Real.sqrt τ from by rw [bsd2]]
  field_simp
  rw [show Real.sqrt τ ^ 2 = τ from h_sqrt_sq]
  ring

/-- **Asset-or-nothing theta**: `∂_τ V_asset = S · ϕ(d₁) · ∂_τ d₁`.

Direct chain rule. The Lean form of `∂_τ d₁` is `((r + σ²/2)τ − log(S/K)) / (2 σ τ √τ)`;
this equals the textbook clean form `(r + σ²/2)/(σ√τ) − d₁/(2τ)` by algebraic
identity (left to the consumer). -/
lemma hasDerivAt_bsAssetDigital_tau (S K r σ : ℝ) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t => bsAssetDigital K r σ S t)
      (S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) *
        (((r + σ^2/2) * τ - Real.log (S/K)) / (2 * σ * τ * Real.sqrt τ))) τ := by
  have h_d1_τ := hasDerivAt_bsd1_tau S K r σ hσ hτ
  have h_Phi := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp τ h_d1_τ
  have h := h_Phi.const_mul S
  unfold bsAssetDigital
  convert h using 1
  ring

/-- **Cash-or-nothing theta**: `∂_τ V_cash = -r · e^{-rτ} · Φ(d₂) + e^{-rτ} · ϕ(d₂) · ∂_τ d₂`.

Product rule on `V_cash(τ) = e^{-rτ} · Φ(d₂(τ))`:
* `∂_τ e^{-rτ} = -r · e^{-rτ}`
* `∂_τ Φ(d₂(τ)) = ϕ(d₂) · ∂_τ d₂`. -/
lemma hasDerivAt_bsCashDigital_tau (S K r σ : ℝ) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t => bsCashDigital K r σ S t)
      (-r * Real.exp (-(r * τ)) * Phi (bsd2 S K r σ τ) +
        Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) *
          (((r + σ^2/2) * τ - Real.log (S/K)) / (2 * σ * τ * Real.sqrt τ)
            - σ / (2 * Real.sqrt τ))) τ := by
  have h_d2_τ := hasDerivAt_bsd2_tau S K r σ hσ hτ
  have h_Phi := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp τ h_d2_τ
  have h_neg : HasDerivAt (fun t : ℝ => -(r * t)) (-r) τ := by
    have h := (hasDerivAt_id τ).const_mul r
    simpa using h.neg
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (-(r * t)))
      (Real.exp (-(r * τ)) * (-r)) τ := h_neg.exp
  have h := h_exp.mul h_Phi
  unfold bsCashDigital
  convert h using 1
  simp only [Function.comp_apply]
  ring

/-- **Asset-or-nothing vega**: `∂_σ V_asset = -S · ϕ(d₁) · d₂ / σ`.

Chain rule on `Φ ∘ d₁`. The Lean form of `∂_σ d₁` is
`(σ²τ/2 − log(S/K) − rτ)/(σ²√τ)`, which equals `-d₂/σ` via `bsd2_eq`. -/
lemma hasDerivAt_bsAssetDigital_sigma (S K r : ℝ) {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (fun σ' => bsAssetDigital K r σ' S τ)
      (-(S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) * bsd2 S K r σ τ / σ)) σ := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have h_sqrt_sq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  have h_d1_σ := hasDerivAt_bsd1_sigma S K r hσ hτ
  have h_Phi := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp σ h_d1_σ
  have h := h_Phi.const_mul S
  unfold bsAssetDigital
  convert h using 1
  rw [bsd2_eq hσ hτ]
  field_simp
  ring

/-- **Cash-or-nothing vega**: `∂_σ V_cash = -e^{-rτ} · ϕ(d₂) · d₁ / σ`.

Chain rule on `Φ ∘ d₂`. The Lean form of `∂_σ d₂ = ∂_σ d₁ − √τ` equals `-d₁/σ`
via `bsd2_eq` plus the identity `bsd2 + σ√τ = bsd1`. -/
lemma hasDerivAt_bsCashDigital_sigma (S K : ℝ) {r σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (fun σ' => bsCashDigital K r σ' S τ)
      (-(Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) *
        bsd1 S K r σ τ / σ)) σ := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have h_sqrt_sq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  have h_d2_σ := hasDerivAt_bsd2_sigma S K r hσ hτ
  have h_Phi := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp σ h_d2_σ
  have h := h_Phi.const_mul (Real.exp (-(r * τ)))
  unfold bsCashDigital
  convert h using 1
  rw [show bsd1 S K r σ τ = bsd2 S K r σ τ + σ * Real.sqrt τ from by
    rw [bsd2]; ring]
  rw [bsd2_eq hσ hτ]
  field_simp
  ring

/-- **Asset-or-nothing rho**: `∂_r V_asset = S · ϕ(d₁) · √τ / σ`.

Direct chain rule since `∂_r d₁ = √τ/σ` (the difference `d₁ − d₂` is `r`-independent). -/
lemma hasDerivAt_bsAssetDigital_r (S K σ : ℝ) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) (r : ℝ) :
    HasDerivAt (fun r' => bsAssetDigital K r' σ S τ)
      (S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) * (Real.sqrt τ / σ)) r := by
  have h_d1_r := hasDerivAt_bsd1_r S K σ τ hσ hτ r
  have h_Phi := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp r h_d1_r
  have h := h_Phi.const_mul S
  unfold bsAssetDigital
  convert h using 1
  ring

/-- **Cash-or-nothing rho**: `∂_r V_cash = e^{-rτ} · (ϕ(d₂) · √τ/σ − τ · Φ(d₂))`.

Product rule on `V_cash(r) = e^{-rτ} · Φ(d₂(r))`:
* `∂_r e^{-rτ} = -τ · e^{-rτ}`
* `∂_r Φ(d₂(r)) = ϕ(d₂) · √τ/σ`. -/
lemma hasDerivAt_bsCashDigital_r (S K σ : ℝ) (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) (r : ℝ) :
    HasDerivAt (fun r' => bsCashDigital K r' σ S τ)
      (Real.exp (-(r * τ)) *
        (gaussianPDFReal 0 1 (bsd2 S K r σ τ) * (Real.sqrt τ / σ)
          - τ * Phi (bsd2 S K r σ τ))) r := by
  have h_d2_r := hasDerivAt_bsd2_r S K σ τ hσ hτ r
  have h_Phi := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp r h_d2_r
  have h_neg_r : HasDerivAt (fun r' : ℝ => -(r' * τ)) (-τ) r := by
    have h := (hasDerivAt_id r).mul_const τ
    simpa using h.neg
  have h_exp : HasDerivAt (fun r' : ℝ => Real.exp (-(r' * τ)))
      (Real.exp (-(r * τ)) * (-τ)) r := h_neg_r.exp
  have h := h_exp.mul h_Phi
  unfold bsCashDigital
  convert h using 1
  simp only [Function.comp_apply]
  ring

/-- **Cash-or-nothing gamma**: `∂²V_cash/∂S² = -e^{-rτ} · ϕ(d₂) · d₁ / (S² σ² τ)`.

Differentiating δ_cash(s) = `e^{-rτ} · ϕ(d₂(s)) / (s · σ · √τ)` as a quotient
`f(s)/g(s)` with `f(s) = e^{-rτ} · ϕ(d₂(s))` and `g(s) = s · σ · √τ`:
* `f'(S) = e^{-rτ} · (-d₂ · ϕ(d₂)) · (1/(S σ √τ))`
* `g'(S) = σ · √τ`
* `(f/g)'(S) = (f' · g − f · g') / g²`
* Numerator algebraically collapses via `d₂ + σ√τ = d₁`. -/
lemma hasDerivAt_bsCashDigital_SS {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt
      (fun s => Real.exp (-(r * τ)) *
        gaussianPDFReal 0 1 (bsd2 s K r σ τ) / (s * σ * Real.sqrt τ))
      (-(Real.exp (-(r * τ)) * gaussianPDFReal 0 1 (bsd2 S K r σ τ) *
        bsd1 S K r σ τ / (S ^ 2 * σ ^ 2 * τ))) S := by
  have h_sqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h_sqrt_ne : Real.sqrt τ ≠ 0 := h_sqrt_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.ne'
  have hS_ne : S ≠ 0 := hS.ne'
  have h_sqrt_sq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  have h_denom_ne : S * σ * Real.sqrt τ ≠ 0 :=
    mul_ne_zero (mul_ne_zero hS_ne hσ_ne) h_sqrt_ne
  have h_d2_S := hasDerivAt_bsd2_S (r := r) hK hσ hτ hS
  have h_pdf := (hasDerivAt_gaussianPDFReal_zero_one (bsd2 S K r σ τ)).comp S h_d2_S
  -- Numerator f(s) = e^{-rτ} · ϕ(d₂(s)).
  have h_num := h_pdf.const_mul (Real.exp (-(r * τ)))
  -- Denominator g(s) = s · σ · √τ.
  have h_id : HasDerivAt (fun s : ℝ => s) 1 S := hasDerivAt_id S
  have h_denom : HasDerivAt (fun s : ℝ => s * σ * Real.sqrt τ) (σ * Real.sqrt τ) S := by
    have h := (h_id.mul_const σ).mul_const (Real.sqrt τ)
    simpa using h
  have h_div := h_num.div h_denom h_denom_ne
  convert h_div using 1
  have h_bsd1 : bsd1 S K r σ τ = bsd2 S K r σ τ + σ * Real.sqrt τ := by
    rw [bsd2]; ring
  rw [h_bsd1]
  simp only [Function.comp_apply]
  field_simp
  rw [show Real.sqrt τ ^ 2 = τ from h_sqrt_sq]
  ring

end MathFin
