/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# One-period FTAP on a general probability space (d assets)

The Föllmer–Schied / one-period Dalang–Morton–Willinger Fundamental Theorem of Asset
Pricing for a `ℝᵈ`-valued discounted excess return `Y` and **constant** portfolios
`θ ∈ ℝᵈ` (trivial initial information) on an **arbitrary** probability space `(Ω, P)`:
no arbitrage ⟺ there is an equivalent martingale measure `Q ~ P` with `Y` integrable
and `E_Q[Y] = 0 ∈ ℝᵈ`.

This is the `d`-asset generalisation of the scalar `Foundations/FTAPOnePeriod.lean`.
Because `θ` ranges over the **finite-dimensional** `ℝᵈ`, the equivalent martingale
measure is **explicit** — the backward direction is the Esscher / minimal-divergence
construction: minimise the smooth convex potential `θ ↦ E[log(1 + exp⟪θ,Y⟫)]`; under
no arbitrage it is coercive transverse to `{u : ⟪u,Y⟫ = 0 a.e.}`, so a minimiser `θ*`
exists, and its first-order condition `E[Y · σ(⟪θ*,Y⟫)] = 0` (with `σ` the logistic
function) hands back a strictly-positive bounded density `z = σ(⟪θ*,Y⟫)`. No
Hahn–Banach, no L⁰-cone closedness, no measurable selection — those are needed only
for the general-Ω **multi-period** DMW.

## Scope

One trading period, **`d` assets**, **trivial `ℱ₀`** (constant `θ`), arbitrary
`(Ω, P)`. The general-Ω multi-period DMW (predictable `L⁰(ℱ_t)`-strategies and the
L⁰ gains-cone closedness) remains open.

## Main result

* `MathFin.OnePeriodVector.ftap_one_period_vector`
-/

@[expose] public section

namespace MathFin.OnePeriodVector

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  {d : ℕ} (Y : Ω → EuclideanSpace ℝ (Fin d))

/-- **No arbitrage** (`d` assets, one period): no constant portfolio `θ ∈ ℝᵈ` turns
zero cost into a sure non-negative discounted gain `⟪θ, Y⟫` with a chance of profit —
any `θ` whose gain `⟪θ, Y⟫` is `≥ 0` a.e. already has `⟪θ, Y⟫ = 0` a.e. -/
def NoArbitrage : Prop :=
  ∀ θ : EuclideanSpace ℝ (Fin d), 0 ≤ᵐ[P] (fun ω => inner ℝ θ (Y ω)) →
    (fun ω => inner ℝ θ (Y ω)) =ᵐ[P] 0

/-- **Equivalent martingale measure** (one period, vector): `Q ~ P`, `Y` is
`Q`-integrable, and `E_Q[Y] = 0 ∈ ℝᵈ`. -/
structure IsEMM (Q : Measure Ω) : Prop where
  prob : IsProbabilityMeasure Q
  absP : Q ≪ P
  Pabs : P ≪ Q
  int  : Integrable Y Q
  fair : ∫ ω, Y ω ∂Q = 0

omit [IsProbabilityMeasure P] in
/-- **Forward direction**: an equivalent martingale measure precludes arbitrage.
Under `Q`, `∫ ⟪θ, Y⟫ ∂Q = ⟪θ, E_Q[Y]⟫ = 0`, so a non-negative `⟪θ, Y⟫` is `0` a.e.;
equivalence transports this back to `P`. -/
theorem noArbitrage_of_isEMM {Q : Measure Ω} (hQ : IsEMM P Y Q) : NoArbitrage P Y := by
  haveI := hQ.prob
  intro θ hpos
  have hposQ : 0 ≤ᵐ[Q] (fun ω => inner ℝ θ (Y ω)) := hQ.absP.ae_le hpos
  have hint : ∫ ω, inner ℝ θ (Y ω) ∂Q = 0 := by
    rw [integral_inner hQ.int, hQ.fair, inner_zero_right]
  have hzeroQ : (fun ω => inner ℝ θ (Y ω)) =ᵐ[Q] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hposQ (hQ.int.const_inner θ)).mp hint
  exact hQ.Pabs.ae_eq hzeroQ

/-! ### The softplus potential and its logistic derivative

The backward direction minimises `θ ↦ ∫ softplus ⟪θ,Y⟫`; `softplus u = log(1+eᵘ)` is
the smooth convex penalty whose derivative is the **logistic** `σ(u) = eᵘ/(1+eᵘ) ∈
(0,1)`. The bounds `u⁺ ≤ softplus u ≤ |u| + log 2` give coercivity and integrability;
`σ ∈ (0,1)` gives the uniform `L¹` domination for differentiating under the integral. -/

/-- Softplus penalty `log(1 + eᵘ)`. -/
noncomputable def softplus (u : ℝ) : ℝ := Real.log (1 + Real.exp u)

/-- Logistic function `eᵘ/(1 + eᵘ) = σ(u)`, the derivative of `softplus`. -/
noncomputable def logistic (u : ℝ) : ℝ := Real.exp u / (1 + Real.exp u)

lemma logistic_pos (u : ℝ) : 0 < logistic u := by rw [logistic]; positivity

lemma logistic_lt_one (u : ℝ) : logistic u < 1 := by
  rw [logistic, div_lt_one (by positivity)]; linarith [Real.exp_pos u]

lemma softplus_nonneg (u : ℝ) : 0 ≤ softplus u := by
  rw [softplus]; exact Real.log_nonneg (by linarith [Real.exp_pos u])

lemma self_le_softplus (u : ℝ) : u ≤ softplus u := by
  rw [softplus]
  calc u = Real.log (Real.exp u) := (Real.log_exp u).symm
    _ ≤ Real.log (1 + Real.exp u) :=
        Real.log_le_log (Real.exp_pos u) (by linarith [Real.exp_pos u])

/-- `u⁺ = max u 0 ≤ softplus u`: the lower bound powering coercivity of the potential. -/
lemma posPart_le_softplus (u : ℝ) : max u 0 ≤ softplus u :=
  max_le (self_le_softplus u) (softplus_nonneg u)

/-- `softplus u ≤ |u| + log 2`: the linear-growth upper bound giving `L¹`-integrability. -/
lemma softplus_le (u : ℝ) : softplus u ≤ |u| + Real.log 2 := by
  rw [softplus]
  have hb : 1 + Real.exp u ≤ 2 * Real.exp |u| := by
    have h1 : Real.exp u ≤ Real.exp |u| := Real.exp_le_exp.mpr (le_abs_self u)
    have h2 : (1 : ℝ) ≤ Real.exp |u| := Real.one_le_exp (abs_nonneg u)
    linarith
  calc Real.log (1 + Real.exp u) ≤ Real.log (2 * Real.exp |u|) :=
        Real.log_le_log (by positivity) hb
    _ = |u| + Real.log 2 := by
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]; ring

/-- `softplus` is differentiable with derivative the logistic `σ`. -/
lemma hasDerivAt_softplus (u : ℝ) : HasDerivAt softplus (logistic u) u := by
  have h2 : (1 : ℝ) + Real.exp u ≠ 0 := by positivity
  have h1 : HasDerivAt (fun v => 1 + Real.exp v) (Real.exp u) u := by
    simpa using (Real.hasDerivAt_exp u).const_add 1
  have h3 := (Real.hasDerivAt_log h2).comp u h1
  rw [show logistic u = (1 + Real.exp u)⁻¹ * Real.exp u from by rw [logistic, div_eq_inv_mul]]
  exact h3

lemma continuous_softplus : Continuous softplus := by
  have hpos : ∀ u : ℝ, (0 : ℝ) < 1 + Real.exp u := fun u => by positivity
  exact (continuous_const.add Real.continuous_exp).log (fun u => (hpos u).ne')

lemma continuous_logistic : Continuous logistic := by
  have hpos : ∀ u : ℝ, (0 : ℝ) < 1 + Real.exp u := fun u => by positivity
  exact Real.continuous_exp.div (continuous_const.add Real.continuous_exp) (fun u => (hpos u).ne')

/-- The **softplus potential** `f(θ) = ∫ softplus⟪θ,Y⟫ ∂P`, minimised in the backward
direction; its first-order condition produces the equivalent martingale measure. -/
noncomputable def potential (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ ω, softplus (inner ℝ θ (Y ω)) ∂P

/-- `softplus⟪θ,Y⟫` is `P`-integrable, dominated by `‖θ‖‖Y‖ + log 2`. -/
lemma integrable_softplus_inner (hYint : Integrable Y P) (θ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ω => softplus (inner ℝ θ (Y ω))) P := by
  have hmeas : AEStronglyMeasurable (fun ω => softplus (inner ℝ θ (Y ω))) P :=
    continuous_softplus.comp_aestronglyMeasurable
      ((continuous_const.inner continuous_id).comp_aestronglyMeasurable hYint.aestronglyMeasurable)
  refine Integrable.mono' (g := fun ω => ‖θ‖ * ‖Y ω‖ + Real.log 2) ?_ hmeas ?_
  · exact (hYint.norm.const_mul ‖θ‖).add (integrable_const _)
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (softplus_nonneg _)]
    exact (softplus_le _).trans (by gcongr; exact abs_real_inner_le_norm _ _)

/-- **Directional derivative of the potential**. For `Y ∈ L¹`, `t ↦ f(θ + t•u)` is
differentiable at `0` with derivative `∫ σ⟪θ,Y⟫ · ⟪u,Y⟫ ∂P` — differentiation under the
integral, dominated by `‖u‖‖Y‖` since `σ ∈ (0,1)`. -/
lemma hasDerivAt_potential_dir (hY : Measurable Y) (hYint : Integrable Y P)
    (θ u : EuclideanSpace ℝ (Fin d)) :
    HasDerivAt (fun t : ℝ => potential P Y (θ + t • u))
      (∫ ω, logistic (inner ℝ θ (Y ω)) * inner ℝ u (Y ω) ∂P) 0 := by
  have hbmeas : Measurable (fun ω => inner ℝ u (Y ω)) := measurable_const.inner hY
  have hexp : ∀ (t : ℝ) (ω : Ω),
      inner ℝ (θ + t • u) (Y ω) = inner ℝ θ (Y ω) + t * inner ℝ u (Y ω) := fun t ω => by
    rw [inner_add_left, real_inner_smul_left]
  set F : ℝ → Ω → ℝ :=
    fun t ω => softplus (inner ℝ θ (Y ω) + t * inner ℝ u (Y ω)) with hF
  set F' : ℝ → Ω → ℝ :=
    fun t ω => logistic (inner ℝ θ (Y ω) + t * inner ℝ u (Y ω)) * inner ℝ u (Y ω) with hF'
  have hmeas_arg : ∀ t : ℝ, AEStronglyMeasurable
      (fun ω => inner ℝ θ (Y ω) + t * inner ℝ u (Y ω)) P :=
    fun t => ((measurable_const.inner hY).add (hbmeas.const_mul t)).aestronglyMeasurable
  have hF_meas : ∀ᶠ t in nhds (0 : ℝ), AEStronglyMeasurable (F t) P :=
    Filter.Eventually.of_forall fun t =>
      continuous_softplus.comp_aestronglyMeasurable (hmeas_arg t)
  have hF_int : Integrable (F 0) P := by
    simp only [hF, zero_mul, add_zero]; exact integrable_softplus_inner P Y hYint θ
  have hF'_meas : AEStronglyMeasurable (F' 0) P :=
    (continuous_logistic.comp_aestronglyMeasurable (hmeas_arg 0)).mul hbmeas.aestronglyMeasurable
  have h_bound : ∀ᵐ ω ∂P, ∀ x ∈ (Set.univ : Set ℝ), ‖F' x ω‖ ≤ ‖u‖ * ‖Y ω‖ := by
    filter_upwards with ω x _
    rw [hF', Real.norm_eq_abs, abs_mul]
    have h1 : |logistic (inner ℝ θ (Y ω) + x * inner ℝ u (Y ω))| ≤ 1 := by
      rw [abs_of_pos (logistic_pos _)]; exact (logistic_lt_one _).le
    have h2 : |inner ℝ u (Y ω)| ≤ ‖u‖ * ‖Y ω‖ := abs_real_inner_le_norm u (Y ω)
    calc |logistic (inner ℝ θ (Y ω) + x * inner ℝ u (Y ω))| * |inner ℝ u (Y ω)|
        ≤ 1 * (‖u‖ * ‖Y ω‖) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = ‖u‖ * ‖Y ω‖ := one_mul _
  have h_diff : ∀ᵐ ω ∂P, ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun t => F t ω) (F' x ω) x := by
    filter_upwards with ω x _
    have haff : HasDerivAt (fun t : ℝ => inner ℝ θ (Y ω) + t * inner ℝ u (Y ω))
        (inner ℝ u (Y ω)) x := by
      simpa using ((hasDerivAt_id x).mul_const (inner ℝ u (Y ω))).const_add (inner ℝ θ (Y ω))
    have hc := (hasDerivAt_softplus _).comp x haff
    simpa only [hF, hF', Function.comp_def] using hc
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
    (bound := fun ω => ‖u‖ * ‖Y ω‖) Filter.univ_mem hF_meas hF_int hF'_meas h_bound
    (hYint.norm.const_mul ‖u‖) h_diff
  have hpot : (fun t : ℝ => potential P Y (θ + t • u)) = fun t => ∫ ω, F t ω ∂P := by
    funext t; simp only [potential, hF]
    exact integral_congr_ae (by filter_upwards with ω; rw [hexp t ω])
  have hval : (∫ ω, F' 0 ω ∂P) = ∫ ω, logistic (inner ℝ θ (Y ω)) * inner ℝ u (Y ω) ∂P := by
    refine integral_congr_ae ?_; filter_upwards with ω; simp only [hF', zero_mul, add_zero]
  rw [hpot, ← hval]; exact hderiv

end MathFin.OnePeriodVector
