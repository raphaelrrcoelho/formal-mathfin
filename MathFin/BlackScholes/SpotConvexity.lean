/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.PDE

/-!
# Spot-direction convexity of the Black–Scholes call

`StrikeConvexity.lean` packages convexity-in-`K` at three scales; this file
is its spot-direction dual at the two scales that make sense for `S`:

1. **Payoff level**, `S ↦ max(S − K, 0)`: the positive part of an affine
   function is convex.
2. **Continuous price level**, `S ↦ bsV K r σ S τ`: convex on `(0, ∞)` by
   the second-derivative test — gamma is non-negative
   (`hasDerivAt_bsV_SS` + `convexOn_of_deriv2_nonneg'`).

Financially: pricing preserves the convexity of the payoff. Gamma-positivity
(`bsV_gamma_pos`) is the infinitesimal face of the same fact; the
supporting-tangent form below (`bsV_spot_tangent_le`, slope = delta) is the
workhorse for Jensen-type mixture bounds — `MertonDominance.lean` consumes
it to prove the jump-diffusion price dominates Black–Scholes.

## Results

* `convexOn_call_payoff_spot`: `S ↦ max(S − K, 0)` is convex (payoff level).
* `bsV_spot_convexOn`: `S ↦ bsV K r σ S τ` is convex on `(0, ∞)`
  (continuous price level).
* `bsV_spot_tangent_le`: the price lies above its tangent at any `S₀ > 0`,
  with slope delta: `bsV(S₀) + Φ(d₁(S₀))·(s − S₀) ≤ bsV(s)`.
-/

@[expose] public section

namespace MathFin

open Set Real ProbabilityTheory

/-- **Call payoff is convex in the spot**: `S ↦ max(S − K, 0)` is the
positive part of an affine function. The spot-direction sibling of
`convexOn_call_payoff`. -/
lemma convexOn_call_payoff_spot (K : ℝ) :
    ConvexOn ℝ Set.univ (fun S : ℝ => max (S - K) 0) := by
  refine ConvexOn.sup ⟨convex_univ, fun a _ b _ s t _ _ hst => ?_⟩
    (convexOn_const (0 : ℝ) convex_univ)
  show s • a + t • b - K ≤ s • (a - K) + t • (b - K)
  simp only [smul_eq_mul]
  have h_kk : s * K + t * K = K := by linear_combination K * hst
  linarith

/-! ## The continuous-price face

The proof is the second-derivative test, exactly parallel to
`bsV_strike_convexOn`:

* `hasDerivAt_bsV_S`: `∂_S bsV = Φ(d₁)` (delta) exists at every `S > 0`.
* `hasDerivAt_bsV_SS`: `∂²_S bsV = ϕ(d₁)/(S σ √τ)` (gamma) exists and is
  non-negative for every `S > 0`.

The only delicate step is identifying `deriv (fun s => bsV K r σ s τ)` with
the closed-form delta in a neighbourhood of each interior point, so the
second derivative inherits the closed form. -/

/-- **First-derivative identification on `(0, ∞)`**: `deriv` agrees with the
closed-form delta on the whole positive half-line. -/
private lemma deriv_bsV_S_eq_on_Ioi (K r σ τ : ℝ) (hK : 0 < K) (hσ : 0 < σ)
    (hτ : 0 < τ) {S : ℝ} (hS : S ∈ Set.Ioi (0 : ℝ)) :
    deriv (fun s => bsV K r σ s τ) S = Phi (bsd1 S K r σ τ) :=
  (hasDerivAt_bsV_S (K := K) (r := r) (σ := σ) hK hσ hS hτ).deriv

/-- **Local equality of derivatives on `(0, ∞)`**: in a neighbourhood of any
`S > 0`, `deriv (fun s => bsV K r σ s τ)` agrees with the closed-form delta,
so derivative facts about the closed form transfer to `deriv`. -/
private lemma deriv_bsV_S_eventuallyEq (K r σ τ : ℝ) (hK : 0 < K) (hσ : 0 < σ)
    (hτ : 0 < τ) {S : ℝ} (hS : 0 < S) :
    (fun s => deriv (fun s' => bsV K r σ s' τ) s) =ᶠ[nhds S]
      (fun s => Phi (bsd1 s K r σ τ)) := by
  filter_upwards [isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hS)] with s hs
  exact deriv_bsV_S_eq_on_Ioi K r σ τ hK hσ hτ hs

/-- **BS call price is convex in the spot on `(0, ∞)`** — the continuous-
price face of S-convexity: at every `S > 0`,
`∂²_S bsV = ϕ(d₁)/(S σ √τ) ≥ 0` (gamma). -/
theorem bsV_spot_convexOn {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun s => bsV K r σ s τ) := by
  refine convexOn_of_deriv2_nonneg' (convex_Ioi 0) ?_ ?_ ?_
  -- (1) bsV is differentiable in S on Ioi 0 (from hasDerivAt_bsV_S).
  · intro S hS
    exact ((hasDerivAt_bsV_S (K := K) (r := r) (σ := σ) hK hσ hS hτ).differentiableAt
      ).differentiableWithinAt
  -- (2) deriv bsV is differentiable on Ioi 0 (from hasDerivAt_bsV_SS, transported).
  · intro S hS
    have h_pos : (0 : ℝ) < S := hS
    have h_SS := hasDerivAt_bsV_SS (K := K) (r := r) (σ := σ) hK hσ h_pos hτ
    have h_ev := deriv_bsV_S_eventuallyEq K r σ τ hK hσ hτ h_pos
    exact ((h_SS.congr_of_eventuallyEq h_ev).differentiableAt).differentiableWithinAt
  -- (3) deriv^[2] bsV S ≥ 0 for S > 0 — gamma is non-negative.
  · intro S hS
    have h_pos : (0 : ℝ) < S := hS
    have h_SS := hasDerivAt_bsV_SS (K := K) (r := r) (σ := σ) hK hσ h_pos hτ
    have h_ev := deriv_bsV_S_eventuallyEq K r σ τ hK hσ hτ h_pos
    have h_d2 : deriv^[2] (fun s => bsV K r σ s τ) S =
        gaussianPDFReal 0 1 (bsd1 S K r σ τ) / (S * σ * Real.sqrt τ) :=
      (h_SS.congr_of_eventuallyEq h_ev).deriv
    rw [h_d2]
    have h_den_pos : 0 < S * σ * Real.sqrt τ :=
      mul_pos (mul_pos h_pos hσ) (Real.sqrt_pos.mpr hτ)
    exact div_nonneg (gaussianPDFReal_nonneg _ _ _) h_den_pos.le

/-- **The price lies above its tangent at any `S₀ > 0`, with slope delta**:
`bsV(S₀) + Φ(d₁(S₀))·(s − S₀) ≤ bsV(s)`. The supporting-hyperplane form of
`bsV_spot_convexOn` — convexity plus the closed-form delta
(`hasDerivAt_bsV_S`) via the slope comparison lemmas. -/
theorem bsV_spot_tangent_le {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hτ : 0 < τ) {S₀ s : ℝ} (hS₀ : 0 < S₀) (hs : 0 < s) :
    bsV K r σ S₀ τ + Phi (bsd1 S₀ K r σ τ) * (s - S₀) ≤ bsV K r σ s τ := by
  have hconv := bsV_spot_convexOn (K := K) (r := r) (σ := σ) (τ := τ) hK hσ hτ
  have hder := hasDerivAt_bsV_S (K := K) (r := r) (σ := σ) hK hσ hS₀ hτ
  rcases lt_trichotomy S₀ s with hlt | heq | hgt
  · -- to the right of S₀: delta ≤ slope S₀ s.
    have h := hconv.le_slope_of_hasDerivAt (Set.mem_Ioi.mpr hS₀)
      (Set.mem_Ioi.mpr hs) hlt hder
    rw [slope_def_field] at h
    have h' := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    linarith
  · simp [heq]
  · -- to the left of S₀: slope s S₀ ≤ delta.
    have h := hconv.slope_le_of_hasDerivAt (Set.mem_Ioi.mpr hs)
      (Set.mem_Ioi.mpr hS₀) hgt hder
    rw [slope_def_field] at h
    have h' := (div_le_iff₀ (sub_pos.mpr hgt)).mp h
    nlinarith [h']

end MathFin
