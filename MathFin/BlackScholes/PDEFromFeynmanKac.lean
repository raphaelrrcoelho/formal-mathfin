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

/-- **Step 3 (Gamma) — the second `S`-derivative of `bsV`, via Feynman–Kac.** Differentiating the
Delta `e^{−rτ}·U_x·S⁻¹` (from `hasDerivAt_bsV_S_fk`) in `S`: the first space-derivative integral `U_x`
moves through `log S` (chain rule on `hasDerivAt_feynmanU_xx`, giving `U_xx·S⁻¹`) and the `S⁻¹` factor
contributes `−U_x·S⁻²`, so `∂_SS V = e^{−rτ}·(U_xx − U_x)/S²`. The third in-place Greek-via-FK awaiting
the step-4 PDE assembly. -/
private lemma hasDerivAt_bsV_SS_fk {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ)
    {S : ℝ} (hS : 0 < S) :
    HasDerivAt (fun S' => Real.exp (-(r * τ))
        * ((∫ z, max (Real.exp z - K) 0
              * ((z - (Real.log S' + (r - σ ^ 2 / 2) * τ)) / (σ ^ 2 * τ)
                * heatKernel (σ ^ 2 * τ) (z - (Real.log S' + (r - σ ^ 2 / 2) * τ)))) * S'⁻¹))
      (Real.exp (-(r * τ))
        * (((∫ z, max (Real.exp z - K) 0
                * (heatKernel (σ ^ 2 * τ) (z - (Real.log S + (r - σ ^ 2 / 2) * τ))
                    * ((z - (Real.log S + (r - σ ^ 2 / 2) * τ)) ^ 2 - σ ^ 2 * τ) / (σ ^ 2 * τ) ^ 2))
              - (∫ z, max (Real.exp z - K) 0
                * ((z - (Real.log S + (r - σ ^ 2 / 2) * τ)) / (σ ^ 2 * τ)
                  * heatKernel (σ ^ 2 * τ) (z - (Real.log S + (r - σ ^ 2 / 2) * τ))))) / S ^ 2)) S := by
  have ht₀ : (0 : ℝ) < σ ^ 2 * τ := by positivity
  have hg := (hasDerivAt_feynmanU_xx ht₀ (callPayoff_continuous K) (callPayoff_le_exp hK)
      (Real.log S + (r - σ ^ 2 / 2) * τ)).comp S
    ((Real.hasDerivAt_log hS.ne').add_const ((r - σ ^ 2 / 2) * τ))
  have hprod := (hg.mul (hasDerivAt_inv hS.ne')).const_mul (Real.exp (-(r * τ)))
  have hSne : S ≠ 0 := hS.ne'
  convert hprod using 1
  simp only [Function.comp_apply]
  set Uxx := ∫ z, max (Real.exp z - K) 0
      * (heatKernel (σ ^ 2 * τ) (z - (Real.log S + (r - σ ^ 2 / 2) * τ))
          * ((z - (Real.log S + (r - σ ^ 2 / 2) * τ)) ^ 2 - σ ^ 2 * τ) / (σ ^ 2 * τ) ^ 2)
  set Ux := ∫ z, max (Real.exp z - K) 0
      * ((z - (Real.log S + (r - σ ^ 2 / 2) * τ)) / (σ ^ 2 * τ)
          * heatKernel (σ ^ 2 * τ) (z - (Real.log S + (r - σ ^ 2 / 2) * τ)))
  field_simp
  ring

/-- Integrability of the call payoff against the kernel's time-derivative integrand `h·∂_t K`
(`|h| ≤ eᶻ`), dominated by the sub-Gaussian envelope. Needed to split the combined `τ`-derivative
integral in the PDE assembly. -/
private lemma integrable_payoff_mul_dtK {t : ℝ} (ht : 0 < t) {K : ℝ} (hK : 0 < K) (x : ℝ) :
    Integrable (fun z => max (Real.exp z - K) 0
      * (heatKernel t (z - x) * ((z - x) ^ 2 - t) / (2 * t ^ 2))) volume := by
  apply ((integrable_exp_mul_poly_heatKernel ht x t).const_mul (1 / (2 * t ^ 2))).mono'
  · exact ((callPayoff_continuous K).mul
      (((continuous_heatKernel t).comp (continuous_id.sub continuous_const)).mul
        (((continuous_id.sub continuous_const).pow 2).sub continuous_const)
        |>.div_const _)).aestronglyMeasurable
  · refine ae_of_all _ fun z => ?_
    have hKnn := heatKernel_nonneg ht (z - x)
    have hnorm : ‖max (Real.exp z - K) 0 * (heatKernel t (z - x) * ((z - x) ^ 2 - t) / (2 * t ^ 2))‖
        = 1 / (2 * t ^ 2) * (|max (Real.exp z - K) 0| * (heatKernel t (z - x) * |(z - x) ^ 2 - t|)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_of_nonneg hKnn,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * t ^ 2)]; ring
    rw [hnorm]
    have habs : |(z - x) ^ 2 - t| ≤ (z - x) ^ 2 + t := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (z - x)]
    apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 1 / (2 * t ^ 2))
    calc |max (Real.exp z - K) 0| * (heatKernel t (z - x) * |(z - x) ^ 2 - t|)
        ≤ Real.exp z * (heatKernel t (z - x) * ((z - x) ^ 2 + t)) := by
          refine mul_le_mul (callPayoff_le_exp hK z) ?_ (mul_nonneg hKnn (abs_nonneg _))
            (Real.exp_nonneg z)
          exact mul_le_mul_of_nonneg_left habs hKnn
      _ = Real.exp z * (((z - x) ^ 2 + t) * heatKernel t (z - x)) := by ring

/-- Integrability of the call payoff against the kernel's space-derivative integrand `h·∂_x K`. -/
private lemma integrable_payoff_mul_dxK {t : ℝ} (ht : 0 < t) {K : ℝ} (hK : 0 < K) (x : ℝ) :
    Integrable (fun z => max (Real.exp z - K) 0
      * ((z - x) / t * heatKernel t (z - x))) volume := by
  apply ((integrable_exp_mul_poly_heatKernel ht x 1).const_mul (1 / t)).mono'
  · exact ((callPayoff_continuous K).mul
      (((continuous_id.sub continuous_const).div_const t).mul
        ((continuous_heatKernel t).comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
  · refine ae_of_all _ fun z => ?_
    have hKnn := heatKernel_nonneg ht (z - x)
    have hnorm : ‖max (Real.exp z - K) 0 * ((z - x) / t * heatKernel t (z - x))‖
        = 1 / t * (|max (Real.exp z - K) 0| * (|z - x| * heatKernel t (z - x))) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_nonneg hKnn, abs_of_nonneg ht.le]; ring
    rw [hnorm]
    have habs : |z - x| ≤ (z - x) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|z - x| - 1), sq_abs (z - x), abs_nonneg (z - x)]
    apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 1 / t)
    refine mul_le_mul (callPayoff_le_exp hK z) ?_ (mul_nonneg (abs_nonneg _) hKnn) (Real.exp_nonneg z)
    exact mul_le_mul_of_nonneg_right habs hKnn

/-- **Step 4 — the Black–Scholes PDE, derived from Feynman–Kac.** The call value's actual derivatives
satisfy `−∂_τ V + ½σ²S²·∂_SS V + rS·∂_S V − rV = 0`. The three derivatives are the Feynman–Kac Greeks
(`hasDerivAt_bsV_{S,SS,tau}_fk`), each a heat-kernel integral; the operator vanishes *because the heat
kernel does*: the `U_x` drift terms cancel algebraically and `∂_t U = ½ ∂_xx U` is the kernel heat
equation (`feynmanU_heat_equation`). This is the independent, probabilistically-grounded re-derivation
of `bs_pde_holds` — closing the two-tower gap by making `feynmanU` load-bearing for the PDE. (The hard
differentiability work — uniform domination, differentiation under the integral — already lives in
`hasDerivAt_feynmanU_comp` and the Greeks; `feynmanU_heat_equation` supplies only the algebraic kernel
identity `∂_t K = ½ ∂_xx K`, and the operator vanishing is then exact algebra.) -/
theorem bsV_satisfies_bs_pde_via_feynmanKac {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    ∃ Vτ VS VSS : ℝ,
      HasDerivAt (fun τ' => bsV K r σ S τ') Vτ τ ∧
      HasDerivAt (fun S' => bsV K r σ S' τ) VS S ∧
      HasDerivAt (fun S' => deriv (fun S'' => bsV K r σ S'' τ) S') VSS S ∧
      -Vτ + (1 / 2) * σ ^ 2 * S ^ 2 * VSS + r * S * VS - r * bsV K r σ S τ = 0 := by
  refine ⟨_, _, _, hasDerivAt_bsV_tau_fk hK hσ hS hτ, hasDerivAt_bsV_S_fk hK hσ hτ hS,
    (hasDerivAt_bsV_SS_fk (r := r) hK hσ hτ hS).congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [isOpen_Ioi.mem_nhds hS] with S' hS'
    exact (hasDerivAt_bsV_S_fk hK hσ hτ hS').deriv
  · have ht₀ : (0 : ℝ) < σ ^ 2 * τ := by positivity
    have hSne : S ≠ 0 := hS.ne'
    set c₀ : ℝ := Real.log S + (r - σ ^ 2 / 2) * τ
    have hheat := feynmanU_heat_equation ht₀ (fun ξ => max (Real.exp ξ - K) 0) c₀
    simp only [] at hheat
    rw [bsV_eq_discount_feynmanU hS hK hσ hτ,
      show (∫ z, max (Real.exp z - K) 0
            * (σ ^ 2 * (heatKernel (σ ^ 2 * τ) (z - c₀)
                  * ((z - c₀) ^ 2 - σ ^ 2 * τ) / (2 * (σ ^ 2 * τ) ^ 2))
              + (r - σ ^ 2 / 2) * ((z - c₀) / (σ ^ 2 * τ) * heatKernel (σ ^ 2 * τ) (z - c₀))))
          = σ ^ 2 * (∫ z, max (Real.exp z - K) 0
                * (heatKernel (σ ^ 2 * τ) (z - c₀) * ((z - c₀) ^ 2 - σ ^ 2 * τ) / (2 * (σ ^ 2 * τ) ^ 2)))
            + (r - σ ^ 2 / 2) * (∫ z, max (Real.exp z - K) 0
                * ((z - c₀) / (σ ^ 2 * τ) * heatKernel (σ ^ 2 * τ) (z - c₀))) from by
        rw [← integral_const_mul, ← integral_const_mul,
          ← integral_add ((integrable_payoff_mul_dtK ht₀ hK c₀).const_mul _)
            ((integrable_payoff_mul_dxK ht₀ hK c₀).const_mul _)]
        congr 1; ext z; ring,
      hheat]
    set U := feynmanU (fun ξ => max (Real.exp ξ - K) 0) (σ ^ 2 * τ) c₀
    set Uxx := ∫ z, max (Real.exp z - K) 0
        * (heatKernel (σ ^ 2 * τ) (z - c₀) * ((z - c₀) ^ 2 - σ ^ 2 * τ) / (σ ^ 2 * τ) ^ 2)
    set Ux := ∫ z, max (Real.exp z - K) 0
        * ((z - c₀) / (σ ^ 2 * τ) * heatKernel (σ ^ 2 * τ) (z - c₀))
    field_simp
    ring

end MathFin
