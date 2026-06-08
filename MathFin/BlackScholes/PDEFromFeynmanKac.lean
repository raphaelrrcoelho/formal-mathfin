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

/-- **Total `τ`-derivative of the heat kernel along the Black–Scholes curve.** -/
private lemma hasDerivAt_kernelCurve {r σ S z : ℝ} (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun τ' => heatKernel (σ ^ 2 * τ') (z - Real.log S - (r - σ ^ 2 / 2) * τ'))
      (σ ^ 2 * (heatKernel (σ ^ 2 * τ) (z - Real.log S - (r - σ ^ 2 / 2) * τ)
                * ((z - Real.log S - (r - σ ^ 2 / 2) * τ) ^ 2 - σ ^ 2 * τ) / (2 * (σ ^ 2 * τ) ^ 2))
        + (r - σ ^ 2 / 2) * ((z - Real.log S - (r - σ ^ 2 / 2) * τ) / (σ ^ 2 * τ)
                * heatKernel (σ ^ 2 * τ) (z - Real.log S - (r - σ ^ 2 / 2) * τ))) τ := by
  have hipos : (0 : ℝ) < 2 * Real.pi * (σ ^ 2 * τ) := by positivity
  have hsqne : Real.sqrt (2 * Real.pi * (σ ^ 2 * τ)) ≠ 0 := (Real.sqrt_pos.mpr hipos).ne'
  have hss : Real.sqrt (2 * Real.pi * (σ ^ 2 * τ)) ^ 2 = 2 * Real.pi * (σ ^ 2 * τ) :=
    Real.sq_sqrt hipos.le
  have hi : HasDerivAt (fun τ' => 2 * Real.pi * (σ ^ 2 * τ')) (2 * Real.pi * σ ^ 2) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (σ ^ 2)).const_mul (2 * Real.pi)
  have hb : HasDerivAt (fun τ' => z - Real.log S - (r - σ ^ 2 / 2) * τ') (-(r - σ ^ 2 / 2)) τ := by
    have h1 : HasDerivAt (fun τ' => (r - σ ^ 2 / 2) * τ') (r - σ ^ 2 / 2) τ := by
      simpa using (hasDerivAt_id τ).const_mul (r - σ ^ 2 / 2)
    exact h1.const_sub (z - Real.log S)
  have h2s : HasDerivAt (fun τ' => 2 * (σ ^ 2 * τ')) (2 * σ ^ 2) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (σ ^ 2)).const_mul 2
  have hsqrt := (Real.hasDerivAt_sqrt hipos.ne').comp τ hi
  have hP := hsqrt.inv hsqne
  have hQ := ((hb.pow 2).neg.div h2s (by positivity : (2 : ℝ) * (σ ^ 2 * τ) ≠ 0)).exp
  have hPQ := hP.mul hQ
  unfold heatKernel
  convert hPQ using 1
  simp only [Function.comp_apply, Pi.inv_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply]
  rw [hss]
  set E := Real.exp (-(z - Real.log S - (r - σ ^ 2 / 2) * τ) ^ 2 / (2 * (σ ^ 2 * τ))) with hEdef
  set s0 := Real.sqrt (2 * Real.pi * (σ ^ 2 * τ)) with hs0def
  field_simp
  ring

/-- **Combined time-and-space kernel bound along the Black–Scholes curve.** For `τ' ∈ (τ/2, 3τ/2)`,
both the kernel's time `σ²τ'` and its centre `log S + (r−σ²/2)τ'` move with `τ'`; the kernel is
nonetheless dominated by a single fixed *wider* kernel at `τ`. Spatial shift via the public
`heatKernel_shift_le` (the centre moves by `≤ |r−σ²/2|·τ/2`), then a direct time-monotonicity step
(`2σ²τ' ≤ 3σ²τ`). The `τ'`-uniform dominating kernel for differentiating `bsV` under the integral. -/
private lemma heatKernel_curve_le {r σ S : ℝ} (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ)
    {τ' : ℝ} (hlo : τ / 2 < τ') (hhi : τ' < 3 * τ / 2) (z : ℝ) :
    heatKernel (σ ^ 2 * τ') (z - Real.log S - (r - σ ^ 2 / 2) * τ')
      ≤ Real.sqrt 2 * Real.exp ((|r - σ ^ 2 / 2| * (τ / 2) + 1) ^ 2 / (σ ^ 2 * τ))
          * (Real.sqrt 3 * heatKernel (3 * σ ^ 2 * τ) (z - Real.log S - (r - σ ^ 2 / 2) * τ)) := by
  have hτ'pos : 0 < τ' := by linarith
  have htt' : (0 : ℝ) < σ ^ 2 * τ' := by positivity
  have hKt0 : 0 ≤ heatKernel (3 * σ ^ 2 * τ) (z - Real.log S - (r - σ ^ 2 / 2) * τ) :=
    heatKernel_nonneg (by positivity) _
  -- spatial shift: centre moves by < δ := |r−σ²/2|·τ/2 + 1
  have hsub : z - Real.log S - (r - σ ^ 2 / 2) * τ'
      = z - (Real.log S + (r - σ ^ 2 / 2) * τ') := by ring
  have hsp : |(Real.log S + (r - σ ^ 2 / 2) * τ') - (Real.log S + (r - σ ^ 2 / 2) * τ)|
      < |r - σ ^ 2 / 2| * (τ / 2) + 1 := by
    rw [show (Real.log S + (r - σ ^ 2 / 2) * τ') - (Real.log S + (r - σ ^ 2 / 2) * τ)
          = (r - σ ^ 2 / 2) * (τ' - τ) from by ring, abs_mul]
    have h1 : |τ' - τ| ≤ τ / 2 := by rw [abs_le]; constructor <;> linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg (r - σ ^ 2 / 2)), abs_nonneg (r - σ ^ 2 / 2)]
  have hspatial := heatKernel_shift_le htt' (x := Real.log S + (r - σ ^ 2 / 2) * τ')
    (x₀ := Real.log S + (r - σ ^ 2 / 2) * τ) (δ := |r - σ ^ 2 / 2| * (τ / 2) + 1) hsp z
  rw [hsub]
  -- the spatial bound lands on heatKernel (2σ²τ'); now a time-monotonicity step to 3σ²τ
  have htemporal : heatKernel (2 * (σ ^ 2 * τ')) (z - (Real.log S + (r - σ ^ 2 / 2) * τ))
      ≤ Real.sqrt 3 * heatKernel (3 * σ ^ 2 * τ) (z - Real.log S - (r - σ ^ 2 / 2) * τ) := by
    rw [show z - (Real.log S + (r - σ ^ 2 / 2) * τ) = z - Real.log S - (r - σ ^ 2 / 2) * τ from by ring]
    set y := z - Real.log S - (r - σ ^ 2 / 2) * τ with hy
    rw [heatKernel, heatKernel]
    have hpre : (Real.sqrt (2 * Real.pi * (2 * (σ ^ 2 * τ'))))⁻¹
        ≤ Real.sqrt 3 * (Real.sqrt (2 * Real.pi * (3 * σ ^ 2 * τ)))⁻¹ := by
      have h3ne : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)).ne'
      have key : Real.sqrt 3 * (Real.sqrt (2 * Real.pi * (3 * σ ^ 2 * τ)))⁻¹
          = (Real.sqrt (2 * Real.pi * (σ ^ 2 * τ)))⁻¹ := by
        rw [show (2 * Real.pi * (3 * σ ^ 2 * τ)) = 3 * (2 * Real.pi * (σ ^ 2 * τ)) from by ring,
            Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), mul_inv, mul_inv_cancel_left₀ h3ne]
      rw [key]
      exact inv_anti₀ (by positivity) (Real.sqrt_le_sqrt (by
        nlinarith [mul_pos (mul_pos Real.pi_pos (mul_pos hσ hσ))
          (show (0:ℝ) < 2 * τ' - τ by linarith)]))
    have hexp : Real.exp (-y ^ 2 / (2 * (2 * (σ ^ 2 * τ'))))
        ≤ Real.exp (-y ^ 2 / (2 * (3 * σ ^ 2 * τ))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (sq_nonneg y) (mul_nonneg (sq_nonneg σ)
        (show (0:ℝ) ≤ 3 * τ - 2 * τ' by linarith))]
    calc (Real.sqrt (2 * Real.pi * (2 * (σ ^ 2 * τ'))))⁻¹ * Real.exp (-y ^ 2 / (2 * (2 * (σ ^ 2 * τ'))))
        ≤ (Real.sqrt 3 * (Real.sqrt (2 * Real.pi * (3 * σ ^ 2 * τ)))⁻¹)
            * Real.exp (-y ^ 2 / (2 * (3 * σ ^ 2 * τ))) :=
          mul_le_mul hpre hexp (Real.exp_nonneg _) (by positivity)
      _ = Real.sqrt 3 * ((Real.sqrt (2 * Real.pi * (3 * σ ^ 2 * τ)))⁻¹
            * Real.exp (-y ^ 2 / (2 * (3 * σ ^ 2 * τ)))) := by ring
  -- assemble: spatial ≤, then temporal ≤, then bound the τ'-dependent exp by a τ'-free one
  have hexpc : Real.exp ((|r - σ ^ 2 / 2| * (τ / 2) + 1) ^ 2 / (2 * (σ ^ 2 * τ')))
      ≤ Real.exp ((|r - σ ^ 2 / 2| * (τ / 2) + 1) ^ 2 / (σ ^ 2 * τ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (|r - σ ^ 2 / 2| * (τ / 2) + 1)) (mul_nonneg (sq_nonneg σ)
      (show (0:ℝ) ≤ 2 * τ' - τ by linarith))]
  calc heatKernel (σ ^ 2 * τ') (z - (Real.log S + (r - σ ^ 2 / 2) * τ'))
      ≤ Real.sqrt 2 * Real.exp ((|r - σ ^ 2 / 2| * (τ / 2) + 1) ^ 2 / (2 * (σ ^ 2 * τ')))
          * heatKernel (2 * (σ ^ 2 * τ')) (z - (Real.log S + (r - σ ^ 2 / 2) * τ)) := hspatial
    _ ≤ Real.sqrt 2 * Real.exp ((|r - σ ^ 2 / 2| * (τ / 2) + 1) ^ 2 / (σ ^ 2 * τ))
          * (Real.sqrt 3 * heatKernel (3 * σ ^ 2 * τ) (z - Real.log S - (r - σ ^ 2 / 2) * τ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hexpc (Real.sqrt_nonneg 2)) htemporal
          (heatKernel_nonneg (by positivity) _) (by positivity)

/-- `eᶻ`-envelope integrability of `eᶻ · poly · K(3σ²τ, z−m)` — the dominating function for the
`τ`-differentiation, a constant multiple of the step-1 envelope. -/
private lemma integrable_tau_bound {r σ S : ℝ} (hσ : 0 < σ) {τ : ℝ} (hτ : 0 < τ) (M d : ℝ) :
    Integrable (fun z => M * (Real.exp z
      * (((z - Real.log S - (r - σ ^ 2 / 2) * τ) ^ 2 + d)
        * heatKernel (3 * σ ^ 2 * τ) (z - Real.log S - (r - σ ^ 2 / 2) * τ)))) volume := by
  refine ((integrable_exp_mul_poly_heatKernel (show (0:ℝ) < 3 * σ ^ 2 * τ by positivity)
    (Real.log S + (r - σ ^ 2 / 2) * τ) d).const_mul M).congr
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [sub_sub]
end MathFin
