/-
  HybridVerify.ExpMin
  Appendix B.2: minimum of independent exponentials has Exp(sum of rates),
  derived from joint independence (`iIndepFun.meas_iInter`) and individual
  exponential laws (`expMeasure` CDF formula).
-/
import Mathlib

namespace HybridVerify

namespace ExpMin

open MeasureTheory ProbabilityTheory Finset

/-- A finite family of jointly independent exponential random variables on a
    probability space. The textbook claim "min has Exp(∑ rates) distribution"
    is *derived* below from joint independence + individual exponential laws.
    No min-law field is axiomatized. -/
structure IndependentExponentialMinimum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (rates : Fin n → ℝ)
    (τ : Fin n → Ω → ℝ) : Prop where
  rates_pos : ∀ i, 0 < rates i
  /-- Each component has the marginal Exp(rates i) law. -/
  exp_law : ∀ i, Measure.map (τ i) μ = expMeasure (rates i)
  /-- The components are jointly independent. -/
  joint_indep : iIndepFun τ μ
  /-- Each component is measurable. -/
  measurable : ∀ i, Measurable (τ i)

namespace IndependentExponentialMinimum

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} {rates : Fin n → ℝ} {τ : Fin n → Ω → ℝ}

/-- Survival function of `expMeasure r` for `t ≥ 0` (Mathlib v4.30 API). -/
private lemma expMeasure_Ioi (r : ℝ) (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    expMeasure r (Set.Ioi t) = ENNReal.ofReal (Real.exp (-(r * t))) := by
  haveI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have h_compl : expMeasure r (Set.Ioi t) = 1 - expMeasure r (Set.Iic t) := by
    have h_eq : (Set.Ioi t : Set ℝ) = (Set.Iic t)ᶜ := Set.compl_Iic.symm
    rw [h_eq, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ]
  have h_iic : expMeasure r (Set.Iic t) = ENNReal.ofReal (cdf (expMeasure r) t) :=
    (ProbabilityTheory.ofReal_cdf (expMeasure r) t).symm
  rw [h_compl, h_iic, cdf_expMeasure_eq hr t, if_pos ht]
  have hexp_le : Real.exp (-(r * t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := mul_nonneg hr.le ht
    linarith
  have h_diff_nonneg : (0 : ℝ) ≤ 1 - Real.exp (-(r * t)) := by linarith
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ h_diff_nonneg]
  congr 1
  ring

/-- Joint independence ⇒ measure of intersection of `Ioi`-preimages factors as
    a product. The witness `⟨Set.Ioi t, measurableSet_Ioi, rfl⟩` exhibits
    `(τ i) ⁻¹' Set.Ioi t` as comap-measurable. -/
private lemma indep_inter_Ioi (h : IndependentExponentialMinimum μ n rates τ)
    (t : ℝ) :
    μ (⋂ i : Fin n, (τ i) ⁻¹' Set.Ioi t) =
      ∏ i, μ ((τ i) ⁻¹' Set.Ioi t) :=
  h.joint_indep.meas_iInter (fun _ => ⟨Set.Ioi t, measurableSet_Ioi, rfl⟩)

/-- The set `{ω | t < min_i τ_i ω}` rewrites to `⋂_i {ω | t < τ_i ω}`. -/
private lemma min_gt_iInter (hn : 0 < n) (t : ℝ) :
    {ω : Ω | t < (Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      (fun i : Fin n => τ i ω))}
      = ⋂ i : Fin n, (τ i) ⁻¹' Set.Ioi t := by
  ext ω
  simp [Finset.lt_inf'_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi]

/-- **Theorem B.2 — Minimum of independent exponentials.** The survival
    function of the pointwise minimum of jointly independent `Exp(rates_i)`
    random variables is `exp(-(∑rates) · t)` for `t ≥ 0` — the textbook claim
    "min ~ Exp(∑rates)" at the survival-function (CDF) level. -/
theorem minimum_survival (h : IndependentExponentialMinimum μ n rates τ)
    (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      (fun i : Fin n => τ i ω)} =
        ENNReal.ofReal (Real.exp (-((∑ i, rates i) * t))) := by
  rw [min_gt_iInter hn t, indep_inter_Ioi h t]
  have step_each : ∀ i, μ ((τ i) ⁻¹' Set.Ioi t)
      = ENNReal.ofReal (Real.exp (-(rates i * t))) := by
    intro i
    have h_meas : MeasurableSet (Set.Ioi t) := measurableSet_Ioi
    have h_map : μ ((τ i) ⁻¹' Set.Ioi t) = (Measure.map (τ i) μ) (Set.Ioi t) := by
      rw [Measure.map_apply (h.measurable i) h_meas]
    rw [h_map, h.exp_law i, expMeasure_Ioi (rates i) (h.rates_pos i) ht]
  simp_rw [step_each]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib]
  simp [Finset.sum_mul, neg_mul]

end IndependentExponentialMinimum

end ExpMin

end HybridVerify
