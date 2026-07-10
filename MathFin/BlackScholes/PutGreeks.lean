/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.PDE
public import MathFin.BlackScholes.Put

/-!
# Black–Scholes put Greeks

For the European put price `P(S, τ) = K · e^{-rτ} · Φ(-d₂) − S · Φ(-d₁)`, we
derive the five first-order Greeks. The strategy is **put-call parity**:

  `P = V − S + K · e^{-rτ}`

(where `V` is the call price `bsV`). Each Greek is then a one-step Mathlib
derivative combinator applied to the corresponding call Greek + simple
constant/identity derivatives + put-call symmetry `Φ(d) + Φ(-d) = 1`.

## Main results

* `bsP` — the BS European put price as a function of `(S, τ)`.
* `bsP_eq_bsV` — put-call parity for the price functions.
* `hasDerivAt_bsP_S` — δ_P = Φ(d₁) − 1.
* `hasDerivAt_bsP_SS` — γ_P = ϕ(d₁) / (S σ √τ) (same as call gamma).
* `hasDerivAt_bsP_tau` — θ_P in `τ`-form.
* `hasDerivAt_bsP_sigma` — vega_P = S ϕ(d₁) √τ (same as call vega).
* `hasDerivAt_bsP_r` — ρ_P = -K τ e^{-rτ} Φ(-d₂).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- Black–Scholes European put price as a function of `(S, τ)`. -/
noncomputable def bsP (K r σ : ℝ) (S τ : ℝ) : ℝ :=
  K * Real.exp (-(r * τ)) * Phi (-bsd2 S K r σ τ) - S * Phi (-bsd1 S K r σ τ)

/-- **Put-call parity** (price form): `bsP = bsV − S + K · e^{-rτ}`. -/
lemma bsP_eq_bsV (K r σ S τ : ℝ) :
    bsP K r σ S τ = bsV K r σ S τ - S + K * Real.exp (-(r * τ)) := by
  unfold bsP bsV
  have h_d1 := Phi_add_Phi_neg (bsd1 S K r σ τ)
  have h_d2 := Phi_add_Phi_neg (bsd2 S K r σ τ)
  linear_combination -S * h_d1 + K * Real.exp (-(r * τ)) * h_d2

/-- **Put delta**: `∂_S P = Φ(d₁) − 1`. -/
lemma hasDerivAt_bsP_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsP K r σ s τ) (Phi (bsd1 S K r σ τ) - 1) S := by
  have h_eq : (fun s : ℝ ↦ bsP K r σ s τ)
            = fun s ↦ bsV K r σ s τ - s + K * Real.exp (-(r * τ)) := by
    funext s; exact bsP_eq_bsV K r σ s τ
  rw [h_eq]
  have h_V := hasDerivAt_bsV_S (r := r) hK hσ hS hτ
  have h_id : HasDerivAt (fun s : ℝ ↦ s) 1 S := hasDerivAt_id S
  have h_const : HasDerivAt (fun _ : ℝ ↦ K * Real.exp (-(r * τ))) 0 S := hasDerivAt_const _ _
  have h := (h_V.sub h_id).add h_const
  convert h using 1 <;> try rfl
  ring

/-- **Put gamma**: `∂²_S P = ϕ(d₁) / (S σ √τ)` — the same as call gamma
(differs from put by a linear term in `S`, which vanishes on second differentiation). -/
lemma hasDerivAt_bsP_SS {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ Phi (bsd1 s K r σ τ) - 1)
      (gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (S * σ * Real.sqrt τ)) S := by
  have h := hasDerivAt_bsV_SS (r := r) hK hσ hS hτ
  have h_const : HasDerivAt (fun _ : ℝ ↦ (1 : ℝ)) 0 S := hasDerivAt_const _ _
  have h' := h.sub h_const
  convert h' using 1 <;> try rfl
  ring

/-- **Put theta** (`∂_τ` form): `∂_τ P = σ S ϕ(d₁) / (2 √τ) − r K e^{-rτ} Φ(-d₂)`.

Via parity: `∂_τ P = ∂_τ V + ∂_τ (K e^{-rτ}) = (call theta) − r K e^{-rτ}`.
The `Φ(d₂) → Φ(-d₂)` rearrangement uses `Φ(d₂) + Φ(-d₂) = 1`. -/
lemma hasDerivAt_bsP_tau {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun t ↦ bsP K r σ S t)
      (σ * S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (2 * Real.sqrt τ)
        - r * K * Real.exp (-(r * τ)) * Phi (-bsd2 S K r σ τ)) τ := by
  have h_eq : (fun t : ℝ ↦ bsP K r σ S t)
            = fun t ↦ bsV K r σ S t - S + K * Real.exp (-(r * t)) := by
    funext t; exact bsP_eq_bsV K r σ S t
  rw [h_eq]
  have h_V := hasDerivAt_bsV_tau (r := r) hK hσ hS hτ
  have h_const_S : HasDerivAt (fun _ : ℝ ↦ S) 0 τ := hasDerivAt_const _ _
  have h_neg_r : HasDerivAt (fun t : ℝ ↦ -(r * t)) (-r) τ := by
    have h := (hasDerivAt_id τ).const_mul r
    convert h.neg using 1 <;> first | rfl | ring
  have h_exp : HasDerivAt (fun t : ℝ ↦ Real.exp (-(r * t)))
      (Real.exp (-(r * τ)) * -r) τ := h_neg_r.exp
  have h_K_exp : HasDerivAt (fun t : ℝ ↦ K * Real.exp (-(r * t)))
      (K * (Real.exp (-(r * τ)) * -r)) τ := h_exp.const_mul K
  have h := (h_V.sub h_const_S).add h_K_exp
  convert h using 1
  all_goals try rfl
  have h_phi := Phi_add_Phi_neg (bsd2 S K r σ τ)
  linear_combination -(r * K * Real.exp (-(r * τ))) * h_phi

/-- **Put vega**: `∂_σ P = S · ϕ(d₁) · √τ` — same as call vega (the `−S + K e^{-rτ}`
correction is `σ`-independent). -/
lemma hasDerivAt_bsP_sigma {K r : ℝ} (hK : 0 < K)
    {S σ τ : ℝ} (hS : 0 < S) (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ bsP K r s S τ)
      (S * gaussianPDFReal 0 1 (bsd1 S K r σ τ) * Real.sqrt τ) σ := by
  have h_eq : (fun s : ℝ ↦ bsP K r s S τ)
            = fun s ↦ bsV K r s S τ - S + K * Real.exp (-(r * τ)) := by
    funext s; exact bsP_eq_bsV K r s S τ
  rw [h_eq]
  have h_V := hasDerivAt_bsV_sigma (r := r) hK hS hσ hτ
  have h_const_S : HasDerivAt (fun _ : ℝ ↦ S) 0 σ := hasDerivAt_const _ _
  have h_const_disc : HasDerivAt (fun _ : ℝ ↦ K * Real.exp (-(r * τ))) 0 σ := hasDerivAt_const _ _
  have h := (h_V.sub h_const_S).add h_const_disc
  convert h using 1 <;> try rfl
  ring

/-- **Put rho**: `∂_r P = -K · τ · e^{-rτ} · Φ(-d₂)`.

Via parity: `∂_r P = ∂_r V + ∂_r (K e^{-rτ}) = K τ e^{-rτ} Φ(d₂) − K τ e^{-rτ}`,
and `Φ(d₂) − 1 = -Φ(-d₂)`. -/
lemma hasDerivAt_bsP_r {K σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) (r : ℝ) :
    HasDerivAt (fun r' ↦ bsP K r' σ S τ)
      (-(K * τ * Real.exp (-(r * τ)) * Phi (-bsd2 S K r σ τ))) r := by
  have h_eq : (fun r' : ℝ ↦ bsP K r' σ S τ)
            = fun r' ↦ bsV K r' σ S τ - S + K * Real.exp (-(r' * τ)) := by
    funext r'; exact bsP_eq_bsV K r' σ S τ
  rw [h_eq]
  have h_V := hasDerivAt_bsV_r hK hσ hτ hS r
  have h_const_S : HasDerivAt (fun _ : ℝ ↦ S) 0 r := hasDerivAt_const _ _
  have h_neg : HasDerivAt (fun r' : ℝ ↦ -(r' * τ)) (-τ) r := by
    have h := (hasDerivAt_id r).mul_const τ
    convert h.neg using 1 <;> first | rfl | ring
  have h_exp : HasDerivAt (fun r' : ℝ ↦ Real.exp (-(r' * τ)))
      (Real.exp (-(r * τ)) * -τ) r := h_neg.exp
  have h_K_exp : HasDerivAt (fun r' : ℝ ↦ K * Real.exp (-(r' * τ)))
      (K * (Real.exp (-(r * τ)) * -τ)) r := h_exp.const_mul K
  have h := (h_V.sub h_const_S).add h_K_exp
  convert h using 1
  all_goals try rfl
  have h_phi := Phi_add_Phi_neg (bsd2 S K r σ τ)
  linear_combination -(K * τ * Real.exp (-(r * τ))) * h_phi

end MathFin
