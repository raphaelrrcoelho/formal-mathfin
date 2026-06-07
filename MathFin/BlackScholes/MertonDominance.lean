/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.MertonJumpDiffusion
public import MathFin.BlackScholes.SpotConvexity
public import MathFin.BlackScholes.ImpliedVolatility

/-!
# Merton dominance: jump risk is never free

The Merton (1976) jump-diffusion call price dominates the Black–Scholes
price at the diffusion volatility:

  `C_BS(S₀, σ) ≤ C_Merton(S₀, σ, k, δ, Λ)`  for every `Λ`, `δ`, `k > −1`.

The proof decomposes jump risk into its two channels, each priced by a
structural fact of the library:

1. **Jump-size uncertainty (vol channel)**: conditional vols satisfy
   `σ ≤ vol_n`, and the BS value is increasing in vol
   (`bsV_strictMonoOn_sigma`, vega positivity) — so the mixture at jump vol
   `δ` dominates the mixture at `δ = 0` term by term.
2. **Jump-count uncertainty (spot channel)**: at `δ = 0` the mixture
   averages BS values over the *spread* of compensated conditional spots.
   The BS price is convex in the spot (`bsV_spot_convexOn`, gamma), so the
   value lies above its tangent at `S₀` (`bsV_spot_tangent_le`), and the
   linear tangent term integrates to **zero** by the compensation identity
   `E[mertonSpot] = S₀` (`integral_mertonSpot`) — the Jensen floor.

Financially: jumps add value through vega *and* through gamma, and the
compensator is exactly what makes the gamma channel a clean Jensen
argument. Both channels consume the existing structural layer (vega
positivity, gamma convexity, the pgf recombination identity); nothing new
is assumed.

## Main result

* `bsV_le_mertonCallPrice` : `bsV K r σ S₀ T ≤ mertonCallPrice S₀ K r σ T k δ Λ`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal Nat

/-- With zero jump volatility the conditional vol collapses to the diffusion
vol: `mertonVol σ 0 T n = σ`. -/
lemma mertonVol_delta_zero {σ : ℝ} (hσ : 0 ≤ σ) (T : ℝ) (n : ℕ) :
    mertonVol σ 0 T n = σ := by
  unfold mertonVol
  simp [Real.sqrt_sq hσ]

/-- Jump uncertainty only adds variance: `σ ≤ mertonVol σ δ T n`. -/
lemma le_mertonVol {σ T : ℝ} (δ : ℝ) (hσ : 0 ≤ σ) (hT : 0 < T) (n : ℕ) :
    σ ≤ mertonVol σ δ T n := by
  unfold mertonVol
  calc σ = Real.sqrt (σ ^ 2) := (Real.sqrt_sq hσ).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right
        (div_nonneg (by positivity) hT.le))

/-- **Per-term vol-monotonicity**: the zero-jump-vol conditional value lower-
bounds the conditional value at any jump vol `δ` — the BS value is increasing
in vol (vega) and jump variance only adds. -/
lemma mertonCallTerm_delta_zero_le {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k)
    (n : ℕ) :
    mertonCallTerm S_0 K r σ T k 0 Λ n ≤ mertonCallTerm S_0 K r σ T k δ Λ n := by
  rw [mertonCallTerm_eq_bsV, mertonCallTerm_eq_bsV, mertonVol_delta_zero hσ.le]
  exact (bsV_strictMonoOn_sigma hK hT (mertonSpot_pos hS_0 hk Λ n)).monotoneOn
    (Set.mem_Ioi.mpr hσ) (Set.mem_Ioi.mpr (mertonVol_pos hσ hT n))
    (le_mertonVol δ hσ.le hT n)

/-- **Price-level vol-monotonicity**: the δ = 0 mixture lower-bounds the
Merton price. -/
lemma mertonCallPrice_delta_zero_le {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) :
    mertonCallPrice S_0 K r σ T k 0 Λ ≤ mertonCallPrice S_0 K r σ T k δ Λ := by
  unfold mertonCallPrice
  exact integral_mono (integrable_mertonCallTerm 0 Λ hS_0 hK hσ hT hk)
    (integrable_mertonCallTerm δ Λ hS_0 hK hσ hT hk)
    (mertonCallTerm_delta_zero_le δ Λ hS_0 hK hσ hT hk)

/-- **The Jensen floor at zero jump-vol**: spot convexity (tangent at `S₀`,
slope delta) plus the compensation identity `E[mertonSpot] = S₀` make the
δ = 0 mixture dominate the Black–Scholes value — the linear tangent term
integrates to zero *because* the conditional forwards recombine. -/
lemma bsV_le_mertonCallPrice_delta_zero {S_0 K r σ T k : ℝ} (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) :
    bsV K r σ S_0 T ≤ mertonCallPrice S_0 K r σ T k 0 Λ := by
  have h_spot_int : Integrable (mertonSpot S_0 k Λ) (poissonMeasure Λ) :=
    integrable_mertonSpot Λ hS_0 hk
  -- the affine tangent minorant …
  have h_lin_int : Integrable
      (fun n => Phi (bsd1 S_0 K r σ T) * (mertonSpot S_0 k Λ n - S_0))
      (poissonMeasure Λ) :=
    (h_spot_int.sub (integrable_const _)).const_mul _
  have h_tan_int : Integrable (fun n =>
      bsV K r σ S_0 T + Phi (bsd1 S_0 K r σ T) * (mertonSpot S_0 k Λ n - S_0))
      (poissonMeasure Λ) :=
    (integrable_const _).add h_lin_int
  -- … lies below every conditional value (tangent bound at each spot_n) …
  have h_tan_le : ∀ n, bsV K r σ S_0 T
      + Phi (bsd1 S_0 K r σ T) * (mertonSpot S_0 k Λ n - S_0)
      ≤ mertonCallTerm S_0 K r σ T k 0 Λ n := fun n => by
    rw [mertonCallTerm_eq_bsV, mertonVol_delta_zero hσ.le]
    exact bsV_spot_tangent_le hK hσ hT hS_0 (mertonSpot_pos hS_0 hk Λ n)
  -- … and integrates to exactly `bsV` by the compensation identity.
  have h_tan_integral : ∫ n, (bsV K r σ S_0 T
      + Phi (bsd1 S_0 K r σ T) * (mertonSpot S_0 k Λ n - S_0))
      ∂(poissonMeasure Λ) = bsV K r σ S_0 T := by
    rw [integral_add (integrable_const _) h_lin_int,
      integral_const_mul, integral_sub h_spot_int (integrable_const _),
      integral_mertonSpot, integral_const, integral_const, probReal_univ,
      one_smul, one_smul, sub_self, mul_zero, add_zero]
  calc bsV K r σ S_0 T
      = ∫ n, (bsV K r σ S_0 T
          + Phi (bsd1 S_0 K r σ T) * (mertonSpot S_0 k Λ n - S_0))
          ∂(poissonMeasure Λ) := h_tan_integral.symm
    _ ≤ ∫ n, mertonCallTerm S_0 K r σ T k 0 Λ n ∂(poissonMeasure Λ) :=
        integral_mono h_tan_int
          (integrable_mertonCallTerm 0 Λ hS_0 hK hσ hT hk) h_tan_le
    _ = mertonCallPrice S_0 K r σ T k 0 Λ := rfl

/-- **Merton dominance — jump risk is never free.** The Merton (1976)
jump-diffusion call price dominates the Black–Scholes price at the diffusion
volatility, for every jump intensity `Λ`, mean jump size `k > −1`, and jump
vol `δ`:

  `C_BS(S₀, σ) ≤ C_Merton(S₀, σ, k, δ, Λ)`.

Chain: vol-monotonicity reduces to `δ = 0`
(`mertonCallPrice_delta_zero_le`, the vega channel), then spot convexity
plus the compensation identity give the Jensen floor
(`bsV_le_mertonCallPrice_delta_zero`, the gamma channel). -/
theorem bsV_le_mertonCallPrice {S_0 K r σ T k : ℝ} (δ : ℝ) (Λ : ℝ≥0)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (hk : -1 < k) :
    bsV K r σ S_0 T ≤ mertonCallPrice S_0 K r σ T k δ Λ :=
  (bsV_le_mertonCallPrice_delta_zero Λ hS_0 hK hσ hT hk).trans
    (mertonCallPrice_delta_zero_le δ Λ hS_0 hK hσ hT hk)

end MathFin
