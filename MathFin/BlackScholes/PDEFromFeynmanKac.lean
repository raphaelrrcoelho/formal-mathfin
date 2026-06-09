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

Step 1 is proved in `Foundations/FeynmanKacHeatEquation`. This file establishes step 2
(`bsV_eq_feynmanU`), the discounted-heat-flow bridge (`bsV_eq_discount_feynmanU` — the result that
makes `feynmanU` load-bearing for pricing), and Delta via Feynman–Kac (`hasDerivAt_bsV_S_fk`, the
`S`-derivative as a kernel moment) and the `τ`-derivative `hasDerivAt_bsV_tau_fk` (Theta — the product
rule on the discount `e^{−rτ'}` times the discounted heat flow, with *both* kernel arguments `σ²τ'` and
`log S + (r−σ²/2)τ'` moving with `τ'`). The Theta consumes `hasDerivAt_feynmanU_comp` and through it the
heat kernel's joint Fréchet differentiability `hasFDerivAt_heatKernel`, so `feynmanU` is now
load-bearing for the Black–Scholes time-derivative — the curve domination is handled by bounding the two
kernel-derivative terms separately (`Foundations.curve_sq_ratio_le` / `curve_abs_ratio_le` +
`heatKernel_loc_le`), avoiding the single-mega-constant blow-up that defeated the brute force.

Only step 4 — the PDE assembly `−V_τ + ½σ²S²V_SS + rSV_S − rV = e^{−rτ}σ²(½U_xx − U_t) = 0` via
`feynmanU_heat_equation` — remains: it needs `∂_SS` via Feynman–Kac plus the operator cancellation, on
top of the in-place Greeks `hasDerivAt_bsV_S_fk` / `hasDerivAt_bsV_tau_fk`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathFin

open FeynmanKacHeatEquation

/-- **Step 2 — Feynman–Kac representation of the Black–Scholes call value.** -/
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
  have hmap : Measure.map (fun ω => σ * Real.sqrt τ * ω) (gaussianReal 0 1)
      = gaussianReal 0 (σ ^ 2 * τ).toNNReal := by
    rw [gaussianReal_map_const_mul (σ * Real.sqrt τ), mul_zero, mul_one]
    congr 1
    apply NNReal.coe_injective
    rw [NNReal.coe_mk, Real.coe_toNNReal _ hvar.le, mul_pow, Real.sq_sqrt hτ.le]
  rw [FeynmanKacHeatEquation.feynmanU_eq_integral_of_map
        (B := fun _ ω => σ * Real.sqrt τ * ω) (μ := gaussianReal 0 1)
        (measurable_const.mul measurable_id).aemeasurable hmap hg_cont hvar
        (Real.log S + (r - σ ^ 2 / 2) * τ)]
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
  have hcf := bs_call_formula (Q := gaussianReal 0 1) (Z := (id : ℝ → ℝ))
    (S_0 := S) (K := K) (r := r) (σ := σ) (T := τ) ⟨hS, hK, hσ, hτ, HasLaw.id⟩
  simp only [id_eq] at hcf
  rw [hcf, bsV, neg_mul]

private lemma callPayoff_continuous (K : ℝ) :
    Continuous (fun ξ => max (Real.exp ξ - K) 0) :=
  (Real.continuous_exp.sub continuous_const).max continuous_const

private lemma callPayoff_le_exp {K : ℝ} (hK : 0 < K) (z : ℝ) :
    |max (Real.exp z - K) 0| ≤ Real.exp z := by
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith) (Real.exp_nonneg z)

/-- **Step 3 (bridge) — the Black–Scholes value is a discounted heat flow.** -/
theorem bsV_eq_discount_feynmanU {K r σ S τ : ℝ}
    (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    bsV K r σ S τ = Real.exp (-(r * τ))
      * feynmanU (fun ξ => max (Real.exp ξ - K) 0) (σ ^ 2 * τ)
          (Real.log S + (r - σ ^ 2 / 2) * τ) := by
  rw [bsV_eq_feynmanU hS hK hσ hτ]
  simp only [feynmanU]
  rw [← integral_const_mul]
  congr 1
  ext z
  ring

/-- **Step 3 (Delta) — the `S`-derivative of `bsV`, via Feynman–Kac.** -/
private lemma hasDerivAt_bsV_S_fk {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) :
    HasDerivAt (fun S' => bsV K r σ S' τ)
      (Real.exp (-(r * τ))
        * ((∫ z, max (Real.exp z - K) 0
              * ((z - (Real.log S + (r - σ ^ 2 / 2) * τ)) / (σ ^ 2 * τ)
                * heatKernel (σ ^ 2 * τ) (z - (Real.log S + (r - σ ^ 2 / 2) * τ))))
            * S⁻¹)) S := by
  have ht₀ : (0 : ℝ) < σ ^ 2 * τ := by positivity
  have hchain :=
    (hasDerivAt_feynmanU_x ht₀ (callPayoff_continuous K) (callPayoff_le_exp hK)
        (Real.log S + (r - σ ^ 2 / 2) * τ)).comp S
      ((Real.hasDerivAt_log hS.ne').add_const ((r - σ ^ 2 / 2) * τ))
  refine (hchain.const_mul (Real.exp (-(r * τ)))).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hS] with S' hS'
  exact bsV_eq_discount_feynmanU hS' hK hσ hτ

/-- **Step 3 (Theta) — the `τ`-derivative of `bsV`, via Feynman–Kac.** The price's time-decay, derived
from the heat kernel's curve derivative (`hasDerivAt_feynmanU_comp`): product rule on the discount
`e^{−rτ'}` and the discounted heat flow (both kernel arguments `σ²τ'` and `log S + (r−σ²/2)τ'` move
with `τ'`), with the bridge `bsV_eq_discount_feynmanU` for the `τ' > 0` domain. This is the consumer
that makes `hasDerivAt_feynmanU_comp` — and through it the heat kernel's *joint* differentiability
`hasFDerivAt_heatKernel` — load-bearing for the Black–Scholes time-derivative. -/
private lemma hasDerivAt_bsV_tau_fk {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S : ℝ} (hS : 0 < S) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun τ' => bsV K r σ S τ')
      (-r * Real.exp (-(r * τ))
          * feynmanU (fun ξ => max (Real.exp ξ - K) 0) (σ ^ 2 * τ)
              (Real.log S + (r - σ ^ 2 / 2) * τ)
        + Real.exp (-(r * τ))
          * (∫ z, max (Real.exp z - K) 0
              * (σ ^ 2 * (heatKernel (σ ^ 2 * τ) (z - (Real.log S + (r - σ ^ 2 / 2) * τ))
                    * ((z - (Real.log S + (r - σ ^ 2 / 2) * τ)) ^ 2 - σ ^ 2 * τ)
                    / (2 * (σ ^ 2 * τ) ^ 2))
                + (r - σ ^ 2 / 2) * ((z - (Real.log S + (r - σ ^ 2 / 2) * τ)) / (σ ^ 2 * τ)
                    * heatKernel (σ ^ 2 * τ) (z - (Real.log S + (r - σ ^ 2 / 2) * τ)))) ∂volume)) τ := by
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  have hexp : HasDerivAt (fun τ' => Real.exp (-(r * τ'))) (-r * Real.exp (-(r * τ))) τ := by
    have h1 : HasDerivAt (fun τ' : ℝ => -(r * τ')) (-r) τ := by
      simpa using ((hasDerivAt_id τ).const_mul r).neg
    have h2 := h1.exp
    convert h2 using 1
    ring
  have hfk := hasDerivAt_feynmanU_comp (h := fun ξ => max (Real.exp ξ - K) 0)
    (callPayoff_continuous K) (callPayoff_le_exp hK) (α := σ ^ 2) (β := r - σ ^ 2 / 2)
    (x₀ := Real.log S) hσ2 hτ
  refine (hexp.mul hfk).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hτ] with τ' hτ'
  exact bsV_eq_discount_feynmanU hS hK hσ hτ'

end MathFin
