/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- `import Mathlib` comes transitively through `BlackScholes.PDE` /
-- `Foundations.FeynmanKacHeatEquation`.
public import MathFin.Foundations.FeynmanKacHeatEquation
public import MathFin.BlackScholes.PDE
public import MathFin.BlackScholes.Call

/-!
# The Black–Scholes PDE, derived from Feynman–Kac

`BlackScholes/PDE.lean` proves `bs_pde_holds` *backward*: it has the closed form
`bsV` and checks, by differentiating it, that it satisfies
`∂_t V + ½σ²S²∂_SS V + rS∂_S V − rV = 0`. `BlackScholes/PDEFromIto.lean` records
the *algebraic* shape of the no-arbitrage relation but is explicit that the
continuous-time martingale step is deferred — its `… = 0` is a `ring` identity,
not a derivation.

This file closes that gap from the **probabilistic** side. The Black–Scholes
value is a Gaussian convolution of the payoff — a Feynman–Kac representation —
and it satisfies the PDE *because* the heat kernel does. The deep machinery of
`Foundations/FeynmanKacHeatEquation.lean` (until now consumed by nothing) becomes
load-bearing for pricing.

## The program (four steps)

1. **Kernel-side heat equation** *(in `Foundations/FeynmanKacHeatEquation.lean`)*:
   for `g` locally integrable with sub-Gaussian growth and `τ > 0`,
   `u(τ, x) := feynmanU g τ x` is smooth and `∂_τ u = ½ ∂_xx u`. The derivatives
   fall on the smooth, fast-decaying *kernel* (`∂_τ K = ½ ∂_yy K`, already
   proved), so `g` needs no regularity — the call payoff's kink and exponential
   growth are irrelevant.
2. **Feynman–Kac representation of the price** *(`bsV_eq_feynmanU`, below)*:
   `bsV K r σ S τ = feynmanU (fun ξ ↦ e^{−rτ}·(e^ξ − K)⁺) (σ²τ) (log S + (r − σ²/2)τ)`.
   This is the milestone that wires `feynmanU` into the pricing layer.
3. **Log-price + discount change of variables** `S = eˣ`, `t = T − τ`: transport
   step 1's heat equation through the substitution onto the Black–Scholes
   operator.
4. **`bsV` solves the BS PDE, via Feynman–Kac**: assemble 1–3 — an independent,
   conceptually grounded derivation of `bs_pde_holds`.

Steps 1, 3, 4 are in progress; this file currently establishes step 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathFin

/-- **Step 2 — Feynman–Kac representation of the Black–Scholes call value.**

The closed-form value `bsV K r σ S τ` equals the heat-kernel convolution
`feynmanU g (σ²τ) x` of the discounted log-payoff
`g ξ = e^{−rτ}·(e^ξ − K)⁺`, evaluated at the log-forward
`x = log S + (r − σ²/2)τ` with variance `σ²τ`.

This is the bridge that makes `Foundations.FeynmanKacHeatEquation.feynmanU`
load-bearing for the pricing layer. Proof chain:
* `feynmanU g (σ²τ) x = ∫ ω, g (x + ω) ∂(gaussianReal 0 (σ²τ))`
  (`feynmanU_eq_integral_of_map` with `B = id`, `μ = gaussianReal 0 (σ²τ)`);
* rescale `ω = σ√τ · z` to the standard normal
  (`Measure.map (σ√τ · ·) (gaussianReal 0 1) = gaussianReal 0 (σ²τ)`,
  `integral_map`);
* `x + σ√τ·z = log (bsTerminal S r σ τ z)`, so
  `g (x + σ√τ·z) = e^{−rτ}·(bsTerminal S r σ τ z − K)⁺`;
* `bs_call_formula` on `(ℝ, gaussianReal 0 1, Z = id)` evaluates the integral to
  the closed form `bsV`. -/
theorem bsV_eq_feynmanU {K r σ S τ : ℝ}
    (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    bsV K r σ S τ =
      FeynmanKacHeatEquation.feynmanU
        (fun ξ => Real.exp (-(r * τ)) * max (Real.exp ξ - K) 0)
        (σ ^ 2 * τ)
        (Real.log S + (r - σ ^ 2 / 2) * τ) := by
  have hvar : (0:ℝ) < σ ^ 2 * τ := by positivity
  set g : ℝ → ℝ := fun ξ => Real.exp (-(r * τ)) * max (Real.exp ξ - K) 0 with hg
  have hg_cont : Continuous g := by
    rw [hg]
    exact continuous_const.mul
      ((Real.continuous_exp.sub continuous_const).max continuous_const)
  -- the scaling map  `σ√τ · N(0,1) = N(0, σ²τ)`
  have hmap : Measure.map (fun ω => σ * Real.sqrt τ * ω) (gaussianReal 0 1)
      = gaussianReal 0 (σ ^ 2 * τ).toNNReal := by
    rw [gaussianReal_map_const_mul (σ * Real.sqrt τ), mul_zero, mul_one]
    congr 1
    apply NNReal.coe_injective
    rw [NNReal.coe_mk, Real.coe_toNNReal _ hvar.le, mul_pow, Real.sq_sqrt hτ.le]
  -- Feynman–Kac convolution = standard-normal expectation of the shifted payoff
  rw [FeynmanKacHeatEquation.feynmanU_eq_integral_of_map
        (B := fun _ ω => σ * Real.sqrt τ * ω) (μ := gaussianReal 0 1)
        (measurable_const.mul measurable_id).aemeasurable hmap hg_cont hvar
        (Real.log S + (r - σ ^ 2 / 2) * τ)]
  -- identify the shifted payoff with the discounted call payoff at `S_T`
  have hpoint : ∀ ω : ℝ,
      g (Real.log S + (r - σ ^ 2 / 2) * τ + σ * Real.sqrt τ * ω)
        = Real.exp (-r * τ) * max (bsTerminal S r σ τ ω - K) 0 := by
    intro ω
    have hexp : Real.exp (Real.log S + (r - σ ^ 2 / 2) * τ + σ * Real.sqrt τ * ω)
        = bsTerminal S r σ τ ω := by
      simp only [bsTerminal]
      rw [show Real.log S + (r - σ ^ 2 / 2) * τ + σ * Real.sqrt τ * ω
            = Real.log S + ((r - σ ^ 2 / 2) * τ + σ * Real.sqrt τ * ω) from by ring,
          Real.exp_add, Real.exp_log hS]
    simp only [hg, hexp, neg_mul]
  simp_rw [hpoint]
  -- evaluate the Gaussian integral by the closed-form Black–Scholes formula
  have hcf := bs_call_formula (Q := gaussianReal 0 1) (Z := (id : ℝ → ℝ))
    (S_0 := S) (K := K) (r := r) (σ := σ) (T := τ) ⟨hS, hK, hσ, hτ, HasLaw.id⟩
  simp only [id_eq] at hcf
  rw [hcf, bsV, neg_mul]

end MathFin
