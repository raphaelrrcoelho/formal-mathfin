/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# One-period FTAP on a general probability space (scalar)

The Föllmer–Schied (Thm 1.55) / one-period Dalang–Morton–Willinger Fundamental
Theorem of Asset Pricing for a single scalar discounted excess return `Y` on an
**arbitrary** probability space `(Ω, P)`: no arbitrage ⟺ there is an equivalent
martingale measure `Q ~ P` with `Y` integrable and `E_Q[Y] = 0`.

This is the step from finite Ω (`Foundations/FTAPDiscrete.lean`) to genuine
measure theory: `Y ∈ L⁰` (not bounded, integrability not free). The backward
direction is the elementary route — a bounded-density reduction to `L¹`, a scalar
no-arbitrage dichotomy, and a two-region `withDensity` construction that
re-weights the up- and down-moves until `Y` is fair (no Hahn–Banach, no
Kreps–Yan).

## Scope

One trading period, **one scalar asset**, arbitrary `(Ω, P)`. The general-Ω
**multi-period** Dalang–Morton–Willinger theorem (which glues one-period
conditional markets and needs a measurable selection theorem) and the `d`-asset
case remain open.

## Main result

* `MathFin.OnePeriod.ftap_one_period`
-/

@[expose] public section

namespace MathFin.OnePeriod

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  (Y : Ω → ℝ)

/-- **No arbitrage**: no scalar position `θ` turns zero wealth into a sure
non-loss with a chance of gain — any `θ` whose discounted gain `θ · Y` is `≥ 0`
a.e. already has `θ · Y = 0` a.e. -/
def NoArbitrage : Prop :=
  ∀ θ : ℝ, 0 ≤ᵐ[P] (fun ω => θ * Y ω) → (fun ω => θ * Y ω) =ᵐ[P] 0

/-- **Equivalent martingale measure** (one period): `Q ~ P`, `Y` is `Q`-integrable,
and `E_Q[Y] = 0`. -/
structure IsEMM (Q : Measure Ω) : Prop where
  prob : IsProbabilityMeasure Q
  absP : Q ≪ P
  Pabs : P ≪ Q
  int  : Integrable Y Q
  fair : ∫ ω, Y ω ∂Q = 0

omit [IsProbabilityMeasure P] in
/-- **Forward direction**: an equivalent martingale measure precludes arbitrage.
Under `Q`, a non-negative discounted gain integrates to `θ · E_Q[Y] = 0`, so it is
`0` a.e.; equivalence transports this back to `P`. -/
theorem noArbitrage_of_isEMM {Q : Measure Ω} (hQ : IsEMM P Y Q) : NoArbitrage P Y := by
  haveI := hQ.prob
  intro θ hpos
  have hposQ : 0 ≤ᵐ[Q] (fun ω => θ * Y ω) := hQ.absP.ae_le hpos
  have hintegral : ∫ ω, θ * Y ω ∂Q = 0 := by
    rw [integral_const_mul, hQ.fair, mul_zero]
  have hzeroQ : (fun ω => θ * Y ω) =ᵐ[Q] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hposQ (hQ.int.const_mul θ)).mp hintegral
  exact hQ.Pabs.ae_eq hzeroQ

/-- **Balancing-density EMM** (the integrable, non-degenerate core). For an
integrable `Y` with a strictly-positive expected gain on `{Y ≥ 0}` and a
strictly-negative one on its complement, the two-region density
`Z = λ·𝟙_{Y≥0} + μ·𝟙_{Y<0}` — with `λ, μ > 0` chosen so the up- and down-moves
balance (`λ·∫_{Y≥0}Y = −μ·∫_{Y<0}Y`) and `Z` normalises — gives an EMM
`Q = P.withDensity Z`: re-weight up vs down until `Y` is fair. -/
theorem exists_isEMM_of_pos_tails (hY : Measurable Y) (hYint : Integrable Y P)
    (ha : 0 < ∫ ω in {ω | 0 ≤ Y ω}, Y ω ∂P)
    (hb : ∫ ω in {ω | 0 ≤ Y ω}ᶜ, Y ω ∂P < 0) :
    ∃ Q, IsEMM P Y Q := by
  classical
  set s : Set Ω := {ω | 0 ≤ Y ω} with hsdef
  have hs : MeasurableSet s := measurableSet_le measurable_const hY
  set a : ℝ := ∫ ω in s, Y ω ∂P with hadef
  set c : ℝ := ∫ ω in sᶜ, Y ω ∂P with hcdef
  have hpp0 : (0 : ℝ) ≤ (P s).toReal := ENNReal.toReal_nonneg
  have hpn0 : (0 : ℝ) ≤ (P sᶜ).toReal := ENNReal.toReal_nonneg
  have hppn : (P s).toReal + (P sᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top P s) (measure_ne_top P sᶜ),
      measure_add_measure_compl hs, measure_univ, ENNReal.toReal_one]
  -- weights `λ, m > 0`
  set D : ℝ := (-c) * (P s).toReal + a * (P sᶜ).toReal with hDdef
  have hD : 0 < D := by
    rcases eq_or_lt_of_le hpp0 with hpp | hpp
    · have hpn1 : (P sᶜ).toReal = 1 := by linarith
      rw [hDdef, ← hpp, hpn1]; simpa using ha
    · have h1 : 0 < (-c) * (P s).toReal := mul_pos (neg_pos.mpr hb) hpp
      have h2 : 0 ≤ a * (P sᶜ).toReal := mul_nonneg ha.le hpn0
      rw [hDdef]; linarith
  set lam : ℝ := (-c) / D with hlamdef
  set m : ℝ := a / D with hmdef
  have hlam : 0 < lam := div_pos (neg_pos.mpr hb) hD
  have hm : 0 < m := div_pos ha hD
  set Z : Ω → ℝ := fun ω => if 0 ≤ Y ω then lam else m with hZdef
  have hZpos : ∀ ω, 0 < Z ω := fun ω => by simp only [hZdef]; split_ifs <;> assumption
  have hZmeas : Measurable Z := Measurable.ite hs measurable_const measurable_const
  have hZbound : ∀ ω, ‖Z ω‖ ≤ max lam m := fun ω => by
    rw [Real.norm_eq_abs, abs_of_pos (hZpos ω)]
    simp only [hZdef]; split_ifs <;> [exact le_max_left _ _; exact le_max_right _ _]
  have hZint : Integrable Z P :=
    ⟨hZmeas.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hZbound)⟩
  have hZYint : Integrable (fun ω => Z ω * Y ω) P :=
    hYint.bdd_mul hZmeas.aestronglyMeasurable (Filter.Eventually.of_forall hZbound)
  -- `∫ Z·g = λ·∫_s g + m·∫_sᶜ g`
  have hsplit : ∀ g : Ω → ℝ, Integrable (fun ω => Z ω * g ω) P →
      ∫ ω, Z ω * g ω ∂P = lam * (∫ ω in s, g ω ∂P) + m * (∫ ω in sᶜ, g ω ∂P) := by
    intro g hZg
    rw [← integral_add_compl hs hZg]
    congr 1
    · rw [show (∫ ω in s, Z ω * g ω ∂P) = ∫ ω in s, lam * g ω ∂P from
        setIntegral_congr_fun hs fun ω hω => by
          simp only [hZdef, if_pos (show (0 : ℝ) ≤ Y ω from hω)],
        integral_const_mul]
    · rw [show (∫ ω in sᶜ, Z ω * g ω ∂P) = ∫ ω in sᶜ, m * g ω ∂P from
        setIntegral_congr_fun hs.compl fun ω hω => by
          simp only [hZdef, if_neg (show ¬ (0 : ℝ) ≤ Y ω from hω)],
        integral_const_mul]
  -- normalisation `∫ Z = 1`
  have hZsum : ∫ ω, Z ω ∂P = 1 := by
    have h := hsplit (fun _ => 1) (by simpa using hZint)
    simp only [mul_one, setIntegral_const, smul_eq_mul, Measure.real] at h
    rw [h, hlamdef, hmdef]
    field_simp [hD.ne']
    rw [hDdef]; ring
  -- fairness `∫ Z·Y = 0`
  have hZY : ∫ ω, Z ω * Y ω ∂P = 0 := by
    rw [hsplit Y hZYint, ← hadef, ← hcdef, hlamdef, hmdef]
    field_simp
    ring
  -- the EMM measure
  set Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (Z ω)) with hQdef
  have hofReal_meas : Measurable (fun ω => ENNReal.ofReal (Z ω)) :=
    ENNReal.measurable_ofReal.comp hZmeas
  haveI hQprob : IsProbabilityMeasure Q := by
    refine ⟨?_⟩
    rw [hQdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hZint (Filter.Eventually.of_forall fun ω => (hZpos ω).le),
      hZsum, ENNReal.ofReal_one]
  have hQP : Q ≪ P := by rw [hQdef]; exact withDensity_absolutelyContinuous _ _
  have hPQ : P ≪ Q := by
    rw [hQdef]
    refine withDensity_absolutelyContinuous' hofReal_meas.aemeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hZpos ω
  have hYintQ : Integrable Y Q := by
    rw [hQdef, integrable_withDensity_iff_integrable_smul' hofReal_meas
      (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
    refine hZYint.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [ENNReal.toReal_ofReal (hZpos ω).le, smul_eq_mul]
  have hQfair : ∫ ω, Y ω ∂Q = 0 := by
    rw [hQdef, integral_withDensity_eq_integral_toReal_smul hofReal_meas
      (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
    have hfe : (fun ω => (ENNReal.ofReal (Z ω)).toReal • Y ω) = fun ω => Z ω * Y ω := by
      funext ω
      simp only [ENNReal.toReal_ofReal (hZpos ω).le, smul_eq_mul]
    rw [hfe]; exact hZY
  exact ⟨Q, hQprob, hQP, hPQ, hYintQ, hQfair⟩

/-- **Integrable backward direction**. For an integrable `Y`, no arbitrage gives an
EMM. The scalar no-arbitrage *dichotomy*: a one-signed `Y` (`Y ≥ 0` a.e. or `Y ≤ 0`
a.e.) is killed by the position `θ = ±1`, so if `Y ≢ 0` then it is strictly
positive on a set of positive measure and strictly negative on another — whence
`∫_{Y≥0} Y > 0` and `∫_{Y<0} Y < 0`, and the balancing density applies. The
degenerate `Y =ᵐ 0` case takes `Q = P`. -/
theorem exists_isEMM_of_noArbitrage_integrable (hY : Measurable Y) (hYint : Integrable Y P)
    (hNA : NoArbitrage P Y) : ∃ Q, IsEMM P Y Q := by
  classical
  -- the two halves of the no-arbitrage dichotomy: a one-signed `Y` is null
  have hpos_kills : 0 ≤ᵐ[P] Y → Y =ᵐ[P] 0 := fun h => by
    have hk := hNA 1 (by filter_upwards [h] with ω hh; simpa using hh)
    filter_upwards [hk] with ω hh; simpa using hh
  have hneg_kills : Y ≤ᵐ[P] 0 → Y =ᵐ[P] 0 := fun h => by
    have hk := hNA (-1) (by
      filter_upwards [h] with ω hh
      rw [neg_one_mul]; exact neg_nonneg.mpr (by simpa using hh))
    filter_upwards [hk] with ω hh; simpa using hh
  by_cases hY0 : Y =ᵐ[P] 0
  · -- degenerate: `Y` is already fair under `P`
    exact ⟨P, inferInstance, Measure.AbsolutelyContinuous.refl P,
      Measure.AbsolutelyContinuous.refl P, hYint, by rw [integral_congr_ae hY0]; simp⟩
  · -- non-degenerate: both tails are strictly signed
    set s : Set Ω := {ω | 0 ≤ Y ω} with hsdef
    have hs : MeasurableSet s := measurableSet_le measurable_const hY
    have hYs : ∀ ω ∈ s, 0 ≤ Y ω := fun ω hω => hω
    have hYsc : ∀ ω ∈ sᶜ, Y ω ≤ 0 := fun ω hω => le_of_lt (not_le.mp hω)
    have ha0 : 0 ≤ ∫ ω in s, Y ω ∂P := setIntegral_nonneg hs hYs
    have hc0 : ∫ ω in sᶜ, Y ω ∂P ≤ 0 := setIntegral_nonpos hs.compl hYsc
    have ha_pos : 0 < ∫ ω in s, Y ω ∂P := by
      rcases lt_or_eq_of_le ha0 with h | h
      · exact h
      · -- `∫_s Y = 0` with `Y ≥ 0` on `s` ⟹ `Y ≤ᵐ 0` ⟹ (NA, θ=−1) `Y =ᵐ 0`
        refine absurd (hneg_kills ?_) hY0
        have hsz := (ae_restrict_iff' hs).mp
          ((integral_eq_zero_iff_of_nonneg_ae ((ae_restrict_iff' hs).mpr (ae_of_all _ hYs))
            hYint.restrict).mp h.symm)
        filter_upwards [hsz] with ω hω
        by_cases hωs : ω ∈ s
        · exact (hω hωs).le
        · exact hYsc ω hωs
    have hc_neg : ∫ ω in sᶜ, Y ω ∂P < 0 := by
      rcases lt_or_eq_of_le hc0 with h | h
      · exact h
      · -- `∫_{sᶜ} Y = 0` with `Y ≤ 0` on `sᶜ` ⟹ `Y ≥ᵐ 0` ⟹ (NA, θ=1) `Y =ᵐ 0`
        refine absurd (hpos_kills ?_) hY0
        have hscz : (fun ω => -Y ω) =ᵐ[P.restrict sᶜ] 0 := by
          have hnn : 0 ≤ᵐ[P.restrict sᶜ] (fun ω => -Y ω) :=
            (ae_restrict_iff' hs.compl).mpr (ae_of_all _ fun ω hω => by simpa using hYsc ω hω)
          have hint0 : ∫ ω in sᶜ, -Y ω ∂P = 0 := by rw [integral_neg, h, neg_zero]
          exact (integral_eq_zero_iff_of_nonneg_ae hnn hYint.neg.restrict).mp hint0
        filter_upwards [(ae_restrict_iff' hs.compl).mp hscz] with ω hω
        by_cases hωs : ω ∈ s
        · exact hYs ω hωs
        · have hz : -Y ω = 0 := hω hωs
          show (0 : ℝ) ≤ Y ω
          linarith
    exact exists_isEMM_of_pos_tails P Y hY hYint ha_pos hc_neg

/-- **General backward direction** (integrability dropped). No arbitrage gives an
EMM for any measurable `Y`. Pass to the equivalent probability measure
`P̃ = P.withDensity d` with bounded strictly-positive density `d = w / κ`,
`w = (1 + |Y|)⁻¹ ∈ (0,1]`, `κ = ∫ w ∂P ∈ (0,1]`: under `P̃` the variable `Y` is
integrable (`|Y · d| ≤ κ⁻¹` is bounded), and no-arbitrage — an a.e. notion — is
preserved by the equivalence `P̃ ~ P`. The integrable backward direction yields an
EMM `Q ~ P̃`, and `Q ~ P` by transitivity. -/
theorem exists_isEMM_of_noArbitrage (hY : Measurable Y) (hNA : NoArbitrage P Y) :
    ∃ Q, IsEMM P Y Q := by
  classical
  -- bounded strictly-positive weight `w = (1 + |Y|)⁻¹ ∈ (0, 1]`
  set w : Ω → ℝ := fun ω => (1 + |Y ω|)⁻¹ with hwdef
  have hw_meas : Measurable w := (measurable_const.add hY.abs).inv
  have hden_pos : ∀ ω, (0 : ℝ) < 1 + |Y ω| := fun ω => by positivity
  have hw_pos : ∀ ω, 0 < w ω := fun ω => by simp only [hwdef]; exact inv_pos.mpr (hden_pos ω)
  have hw_le_one : ∀ ω, w ω ≤ 1 := fun ω => by
    simp only [hwdef]; exact inv_le_one_of_one_le₀ (by linarith [abs_nonneg (Y ω)])
  have hw_int : Integrable w P :=
    ⟨hw_meas.aestronglyMeasurable, HasFiniteIntegral.of_bounded
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (hw_pos ω)]; exact hw_le_one ω)⟩
  -- normalising constant `κ = ∫ w ∂P ∈ (0, 1]`
  set κ : ℝ := ∫ ω, w ω ∂P with hκdef
  have hκ_pos : 0 < κ := by
    rw [hκdef, integral_pos_iff_support_of_nonneg_ae
        (ae_of_all _ fun ω => (hw_pos ω).le) hw_int,
      show Function.support w = Set.univ from
        Set.eq_univ_of_forall fun ω => (hw_pos ω).ne']
    rw [measure_univ]; exact one_pos
  -- bounded strictly-positive density `d = w / κ`, `∫ d ∂P = 1`
  set d : Ω → ℝ := fun ω => w ω / κ with hddef
  have hd_meas : Measurable d := hw_meas.div_const κ
  have hd_pos : ∀ ω, 0 < d ω := fun ω => div_pos (hw_pos ω) hκ_pos
  have hd_int : Integrable d P := hw_int.div_const κ
  have hd_sum : ∫ ω, d ω ∂P = 1 := by
    simp only [hddef, div_eq_inv_mul]
    rw [integral_const_mul, ← hκdef, inv_mul_cancel₀ hκ_pos.ne']
  -- equivalent probability measure `P̃`
  set Pt : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (d ω)) with hPtdef
  have hd_ofReal_meas : Measurable (fun ω => ENNReal.ofReal (d ω)) :=
    ENNReal.measurable_ofReal.comp hd_meas
  haveI hPt_prob : IsProbabilityMeasure Pt := by
    refine ⟨?_⟩
    rw [hPtdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hd_int
        (Filter.Eventually.of_forall fun ω => (hd_pos ω).le),
      hd_sum, ENNReal.ofReal_one]
  have hPt_ll_P : Pt ≪ P := by rw [hPtdef]; exact withDensity_absolutelyContinuous _ _
  have hP_ll_Pt : P ≪ Pt := by
    rw [hPtdef]
    refine withDensity_absolutelyContinuous' hd_ofReal_meas.aemeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hd_pos ω
  -- `Y` is `P̃`-integrable: `|Y · d| ≤ κ⁻¹` is bounded
  have hdY_int : Integrable (fun ω => d ω * Y ω) P := by
    refine ⟨(hd_meas.mul hY).aestronglyMeasurable, HasFiniteIntegral.of_bounded
      (C := κ⁻¹) (Filter.Eventually.of_forall fun ω => ?_)⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hd_pos ω)]
    have h1 : w ω * |Y ω| ≤ 1 := by
      simp only [hwdef, inv_mul_eq_div, div_le_one (hden_pos ω)]
      linarith [abs_nonneg (Y ω)]
    simp only [hddef, div_mul_eq_mul_div]
    rw [div_le_iff₀ hκ_pos, inv_mul_cancel₀ hκ_pos.ne']
    exact h1
  have hYintPt : Integrable Y Pt := by
    rw [hPtdef, integrable_withDensity_iff_integrable_smul' hd_ofReal_meas
      (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
    refine hdY_int.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [ENNReal.toReal_ofReal (hd_pos ω).le, smul_eq_mul]
  -- no-arbitrage transfers across the equivalence `P̃ ~ P`
  have hNAt : NoArbitrage Pt Y := fun θ h =>
    hPt_ll_P.ae_eq (hNA θ (hP_ll_Pt.ae_le h))
  obtain ⟨Q, hQ⟩ := exists_isEMM_of_noArbitrage_integrable Pt Y hY hYintPt hNAt
  exact ⟨Q, hQ.prob, hQ.absP.trans hPt_ll_P, hP_ll_Pt.trans hQ.Pabs, hQ.int, hQ.fair⟩

/-- **One-period Fundamental Theorem of Asset Pricing** (scalar, general `Ω`).
For a single measurable discounted excess return `Y` on an arbitrary probability
space, *no arbitrage* holds if and only if there exists an *equivalent martingale
measure*: a `Q ~ P` under which `Y` is integrable and `E_Q[Y] = 0`. This is the
Föllmer–Schied / one-period Dalang–Morton–Willinger theorem — the genuine
measure-theoretic step beyond the finite-`Ω` Harrison–Pliska result of
`Foundations/FTAPDiscrete.lean`. -/
theorem ftap_one_period (hY : Measurable Y) :
    NoArbitrage P Y ↔ ∃ Q, IsEMM P Y Q :=
  ⟨fun hNA => exists_isEMM_of_noArbitrage P Y hY hNA,
   fun ⟨_, hQ⟩ => noArbitrage_of_isEMM P Y hQ⟩

end MathFin.OnePeriod
