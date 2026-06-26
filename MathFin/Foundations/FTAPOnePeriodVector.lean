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

/-- `softplus` is `1`-Lipschitz (its derivative `σ` lies in `(0,1)`). -/
lemma lipschitzWith_softplus : LipschitzWith 1 softplus := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_softplus x).differentiableAt) fun x => ?_
  rw [(hasDerivAt_softplus x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one,
    Real.norm_eq_abs, abs_of_pos (logistic_pos x)]
  exact (logistic_lt_one x).le

/-- For a `1`-Lipschitz `φ`, the averaged map `θ ↦ ∫ φ⟪θ,Y⟫ ∂P` is `(∫‖Y‖)`-Lipschitz
(`φ` is `1`-Lipschitz and `θ ↦ ⟪θ,Y ω⟫` is `‖Y ω‖`-Lipschitz, by Cauchy–Schwarz). -/
lemma lipschitzWith_integral_inner {φ : ℝ → ℝ} (hφ : LipschitzWith 1 φ)
    (hint : ∀ θ : EuclideanSpace ℝ (Fin d), Integrable (fun ω => φ (inner ℝ θ (Y ω))) P)
    (hYint : Integrable Y P) :
    LipschitzWith (∫ ω, ‖Y ω‖ ∂P).toNNReal (fun θ => ∫ ω, φ (inner ℝ θ (Y ω)) ∂P) := by
  have hnn : 0 ≤ ∫ ω, ‖Y ω‖ ∂P := integral_nonneg fun ω => norm_nonneg _
  refine LipschitzWith.of_dist_le_mul fun θ θ' => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ hnn, ← integral_sub (hint θ) (hint θ')]
  have hbound : ∀ ω, ‖φ (inner ℝ θ (Y ω)) - φ (inner ℝ θ' (Y ω))‖ ≤ ‖Y ω‖ * ‖θ - θ'‖ := by
    intro ω
    have h1 := hφ.dist_le_mul (inner ℝ θ (Y ω)) (inner ℝ θ' (Y ω))
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h1
    calc ‖φ (inner ℝ θ (Y ω)) - φ (inner ℝ θ' (Y ω))‖
        = |φ (inner ℝ θ (Y ω)) - φ (inner ℝ θ' (Y ω))| := Real.norm_eq_abs _
      _ ≤ |inner ℝ θ (Y ω) - inner ℝ θ' (Y ω)| := h1
      _ = |inner ℝ (θ - θ') (Y ω)| := by rw [inner_sub_left]
      _ ≤ ‖Y ω‖ * ‖θ - θ'‖ := by rw [mul_comm]; exact abs_real_inner_le_norm (θ - θ') (Y ω)
  calc |∫ ω, (φ (inner ℝ θ (Y ω)) - φ (inner ℝ θ' (Y ω))) ∂P|
      ≤ ∫ ω, ‖φ (inner ℝ θ (Y ω)) - φ (inner ℝ θ' (Y ω))‖ ∂P := abs_integral_le_integral_abs ..
    _ ≤ ∫ ω, ‖Y ω‖ * ‖θ - θ'‖ ∂P :=
        integral_mono_ae ((hint θ).sub (hint θ')).norm (hYint.norm.mul_const _)
          (Filter.Eventually.of_forall hbound)
    _ = (∫ ω, ‖Y ω‖ ∂P) * ‖θ - θ'‖ := integral_mul_const _ _

/-- The potential is continuous. -/
lemma continuous_potential (hYint : Integrable Y P) : Continuous (potential P Y) :=
  (lipschitzWith_integral_inner P Y lipschitzWith_softplus
    (integrable_softplus_inner P Y hYint) hYint).continuous

/-- `s ↦ max s 0` (positive part) is `1`-Lipschitz. -/
lemma lipschitzWith_posPart : LipschitzWith 1 (fun s : ℝ => max s 0) :=
  LipschitzWith.id.max_const 0

/-- `max⟪θ,Y⟫ 0` is `P`-integrable (dominated by `‖θ‖‖Y‖`). -/
lemma integrable_posPart_inner (hYint : Integrable Y P) (θ : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun ω => max (inner ℝ θ (Y ω)) 0) P := by
  have hmeas : AEStronglyMeasurable (fun ω => max (inner ℝ θ (Y ω)) 0) P :=
    (continuous_id.max continuous_const).comp_aestronglyMeasurable
      ((continuous_const.inner continuous_id).comp_aestronglyMeasurable hYint.aestronglyMeasurable)
  refine Integrable.mono' (hYint.norm.const_mul ‖θ‖) hmeas (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), max_le_iff]
  exact ⟨(le_abs_self _).trans (abs_real_inner_le_norm θ (Y ω)), by positivity⟩

/-- The positive-gain average `g(θ) = ∫⟪θ,Y⟫⁺ ∂P` is continuous. It lower-bounds the
potential (`softplus s ≥ s⁺`) and drives the coercivity argument. -/
lemma continuous_gainsPos (hYint : Integrable Y P) :
    Continuous (fun θ => ∫ ω, max (inner ℝ θ (Y ω)) 0 ∂P) :=
  (lipschitzWith_integral_inner P Y lipschitzWith_posPart
    (integrable_posPart_inner P Y hYint) hYint).continuous

/-- **Coercivity** of the potential (non-redundant market, no arbitrage). The positive
gain average `g(θ) = ∫⟪θ,Y⟫⁺` is positive off `0` (no arbitrage + non-redundancy),
continuous and positively homogeneous; its minimum `c` over the unit sphere is positive,
and `softplus s ≥ s⁺` gives `c‖θ‖ ≤ f(θ)`. -/
lemma exists_pos_lower_bound [Nonempty (Fin d)] (hYint : Integrable Y P)
    (hNA : NoArbitrage P Y)
    (hndg : ∀ θ : EuclideanSpace ℝ (Fin d), (fun ω => inner ℝ θ (Y ω)) =ᵐ[P] 0 → θ = 0) :
    ∃ c > 0, ∀ θ, c * ‖θ‖ ≤ potential P Y θ := by
  classical
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun θ => ∫ ω, max (inner ℝ θ (Y ω)) 0 ∂P with hg
  have hg_nonneg : ∀ θ, 0 ≤ g θ := fun θ => integral_nonneg fun ω => le_max_right _ _
  -- `g` is positive off `0`
  have hg_pos : ∀ θ, θ ≠ 0 → 0 < g θ := by
    intro θ hθ
    refine (hg_nonneg θ).lt_of_ne fun h => hθ ?_
    apply hndg
    have hmax : (fun ω => max (inner ℝ θ (Y ω)) 0) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun ω => le_max_right _ _)
        (integrable_posPart_inner P Y hYint θ)).mp h.symm
    have hnonpos : (fun ω => inner ℝ θ (Y ω)) ≤ᵐ[P] 0 := by
      filter_upwards [hmax] with ω hm
      have hle : inner ℝ θ (Y ω) ≤ max (inner ℝ θ (Y ω)) 0 := le_max_left _ _
      simp only [Pi.zero_apply] at hm ⊢; rwa [hm] at hle
    have hneg := hNA (-θ) (by
      filter_upwards [hnonpos] with ω h
      simp only [Pi.zero_apply] at h ⊢; rw [inner_neg_left]; linarith)
    filter_upwards [hneg] with ω h
    simp only [Pi.zero_apply, inner_neg_left] at h ⊢; linarith
  -- `g` is positively homogeneous
  have hg_hom : ∀ (r : ℝ), 0 ≤ r → ∀ θ, g (r • θ) = r * g θ := by
    intro r hr θ
    simp only [hg]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show max (inner ℝ (r • θ) (Y ω)) 0 = r * max (inner ℝ θ (Y ω)) 0
    rw [real_inner_smul_left]
    rcases le_total 0 (inner ℝ θ (Y ω)) with hs | hs
    · rw [max_eq_left hs, max_eq_left (mul_nonneg hr hs)]
    · rw [max_eq_right hs, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hr hs), mul_zero]
  -- minimum of `g` over the unit sphere is positive
  obtain ⟨u₀, hu₀S, hu₀min⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) (continuous_gainsPos P Y hYint).continuousOn
  have hu₀ne : u₀ ≠ 0 := fun h => by
    rw [Metric.mem_sphere, h, dist_self] at hu₀S; exact one_ne_zero hu₀S.symm
  refine ⟨g u₀, hg_pos u₀ hu₀ne, fun θ => ?_⟩
  have hpg : g θ ≤ potential P Y θ := by
    rw [hg, potential]
    exact integral_mono_ae (integrable_posPart_inner P Y hYint θ)
      (integrable_softplus_inner P Y hYint θ)
      (Filter.Eventually.of_forall fun ω => posPart_le_softplus _)
  refine le_trans ?_ hpg
  rcases eq_or_ne θ 0 with rfl | hθ
  · simpa using hg_nonneg 0
  · have hθ0 : (0 : ℝ) < ‖θ‖ := norm_pos_iff.mpr hθ
    have hunit : (‖θ‖⁻¹ : ℝ) • θ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hθ0, inv_mul_cancel₀ hθ0.ne']
    calc g u₀ * ‖θ‖ = ‖θ‖ * g u₀ := mul_comm _ _
      _ ≤ ‖θ‖ * g ((‖θ‖⁻¹ : ℝ) • θ) :=
          mul_le_mul_of_nonneg_left (isMinOn_iff.mp hu₀min _ hunit) hθ0.le
      _ = g θ := by
          rw [hg_hom ‖θ‖⁻¹ (inv_nonneg.mpr hθ0.le) θ, ← mul_assoc, mul_inv_cancel₀ hθ0.ne', one_mul]

end MathFin.OnePeriodVector
