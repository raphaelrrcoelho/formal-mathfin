/-
  Doob's L^p maximal inequality (textbook Theorem 2.4.6, Tier A.2).

  Goal: for `p > 1` and a non-negative submartingale `(M_n)`,
        ‖max_{k ≤ n} M_k‖_p ≤ (p / (p − 1)) · ‖M_n‖_p.

  Strategy follows the standard layer-cake + maximal-inequality + Fubini +
  Hölder argument; see `docs/superpowers/specs/2026-05-06-real-proof-tiers.md`
  §A.2 for the high-level outline.

  Status (2026-05-08): 10 lemmas verified locally against Mathlib v4.18.0
  (lean-interact, with the standard `~/.cache/mathlib/` ltar cache):

  | #  | Name                                | Content                                  |
  |----|-------------------------------------|------------------------------------------|
  | 1  | runMax                              | Definition (running max)                 |
  | 2  | runMax_nonneg                       | non-negativity                           |
  | 3  | runMax_measurable                   | via `Finset.measurable_range_sup''`      |
  | 4  | runMax_stronglyMeasurable           | upgrade from Measurable                  |
  | 5  | layer_meas_bound                    | maximal_ineq at fixed t > 0              |
  | 6  | lintegral_runMax_rpow_eq_layer      | layer cake                               |
  | 7  | layer_integrand_bound               | pointwise (in t) integrand bound         |
  | 8  | A_le_layer_integral                 | A ≤ ofReal p ⋅ ∫⁻ t in Ioi 0, ...        |
  | 9  | lintegral_rpow_Ioc                  | ∫⁻ t in Ioc 0 M, t^(p-2) = M^(p-1)/(p-1) |
  | 10 | ofReal_setIntegral_eq_setLIntegral  | ofReal(∫_S M_n) = ∫⁻_S ofReal(M_n)       |

  Remaining work, all multi-day Lean engineering:

  1. **Fubini swap** — the dominant cost. Set up a joint integrand on
     `ℝ × Ω`, prove its joint AEMeasurability, apply
     `MeasureTheory.lintegral_lintegral_swap`. Most of the difficulty lies in
     unifying the inner / outer set restrictions with the joint indicator.
     Concretely:
        ∫⁻ t in Ioi 0, ofReal(t^(p-2)) ⋅ ∫⁻ ω in {Mstar≥t}, ofReal(M_n)
        = ∫⁻ ω, ofReal(M_n ω) ⋅ ∫⁻ t in Ioc 0 (runMax M n ω), ofReal(t^(p-2))
     after which lemma #9 evaluates the inner integral pointwise to
        ofReal((runMax M n ω)^(p-1) / (p-1))   (with a separate base case
                                                for `runMax M n ω = 0`).

  2. **Hölder** — `ENNReal.lintegral_mul_le_Lp_mul_Lq` with the
     `p.HolderConjugate (p / (p-1))` instance (3-field constructor:
     1/p + 1/q = 1, 1 < p, 1 < q). Manage `((Mstar)^(p-1))^q = (Mstar)^p`
     via `ENNReal.rpow_mul` / `Real.rpow_mul` with explicit `(p-1)*q = p`.

  3. **Truncation argument** — to handle the case `eLpNorm Mstar = ⊤` while
     `eLpNorm M_n < ⊤`, work first with `min runMax K` and let `K → ⊤`,
     using `MeasureTheory.lintegral_iSup` on the monotone family.

  4. **eLpNorm conversion** — `eLpNorm f (ofReal p) μ = (∫⁻ ofReal(f^p))^(1/p)`
     for non-negative f and 1 < p. Use `eLpNorm_eq_lintegral_rpow_enorm` or
     `MemLp.eLpNorm_eq_integral_rpow_norm` (exact name TBD).

  Each step is independently feasible at v4.18.0 (the necessary Mathlib
  lemmas exist). The total estimated effort matches the spec: 1-3 focused
  days of Lean engineering.
-/

import Mathlib

open MeasureTheory ProbabilityTheory ENNReal Filter Set
open scoped BigOperators

noncomputable section

namespace HybridVerify.DoobLp

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω}

/-- Running maximum of `M` over `0..n`. -/
def runMax (M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => M k ω)

lemma runMax_nonneg {M : ℕ → Ω → ℝ} (hnn : ∀ n ω, 0 ≤ M n ω) (n : ℕ) (ω : Ω) :
    0 ≤ runMax M n ω :=
  le_trans (hnn 0 ω)
    (Finset.le_sup' (f := fun k => M k ω) (Finset.mem_range.mpr (Nat.succ_pos n)))

lemma runMax_measurable {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsub : Submartingale M 𝓕 μ) (n : ℕ) :
    Measurable (runMax M n) := by
  unfold runMax
  exact Finset.measurable_range_sup''
    (fun k _ => ((hsub.stronglyMeasurable k).mono (𝓕.le k)).measurable)

lemma runMax_stronglyMeasurable {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsub : Submartingale M 𝓕 μ) (n : ℕ) :
    StronglyMeasurable (runMax M n) :=
  (runMax_measurable hsub n).stronglyMeasurable

/-- Maximum-inequality at a fixed positive level `t`. -/
lemma layer_meas_bound
    [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0} {M : ℕ → Ω → ℝ}
    (hsub : Submartingale M 𝓕 μ) (hnn : ∀ n ω, 0 ≤ M n ω) (n : ℕ)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t * μ {ω | t ≤ runMax M n ω}
      ≤ ENNReal.ofReal (∫ ω in {ω | t ≤ runMax M n ω}, M n ω ∂μ) := by
  have hM_nn : 0 ≤ M := fun k ω => hnn k ω
  have key := MeasureTheory.maximal_ineq (μ := μ) (𝒢 := 𝓕)
    (f := M) hsub hM_nn (ε := t.toNNReal) n
  have h_set :
      ({ω | t ≤ runMax M n ω}) = ({ω | (↑t.toNNReal : ℝ) ≤ runMax M n ω}) := by
    rw [Real.coe_toNNReal _ ht.le]
  rw [h_set]
  exact key

/-- Layer-cake step. -/
lemma lintegral_runMax_rpow_eq_layer
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0} {p : ℝ}
    (hsub : Submartingale M 𝓕 μ) (hnn : ∀ n ω, 0 ≤ M n ω)
    (hp : 0 < p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((runMax M n ω) ^ p) ∂μ
      = ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi 0,
            μ {ω | t ≤ runMax M n ω} * ENNReal.ofReal (t ^ (p - 1)) :=
  MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul μ
    (ae_of_all _ (runMax_nonneg hnn n))
    (runMax_measurable hsub n).aemeasurable hp

/-- Pointwise (in `t > 0`) integrand bound. -/
lemma layer_integrand_bound
    [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0} {M : ℕ → Ω → ℝ}
    (hsub : Submartingale M 𝓕 μ) (hnn : ∀ n ω, 0 ≤ M n ω) (n : ℕ) {p : ℝ}
    {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ runMax M n ω} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal (t ^ (p - 2)) *
          ENNReal.ofReal (∫ ω in {ω | t ≤ runMax M n ω}, M n ω ∂μ) := by
  have lmb := layer_meas_bound hsub hnn n ht
  have ht_pow_pos : (0 : ℝ) ≤ t ^ (p - 2) := Real.rpow_nonneg ht.le _
  have h_decomp : t ^ (p - 1) = t ^ (p - 2) * t := by
    rw [show (p - 1) = (p - 2) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
  rw [h_decomp, ENNReal.ofReal_mul ht_pow_pos]
  rw [show μ {ω | t ≤ runMax M n ω} * (ENNReal.ofReal (t^(p-2)) * ENNReal.ofReal t)
        = ENNReal.ofReal (t^(p-2)) * (ENNReal.ofReal t * μ {ω | t ≤ runMax M n ω})
        by ring]
  exact mul_le_mul_left' lmb _

/-- Combining steps: A ≤ ofReal p · ∫⁻ t in Ioi 0, ofReal(t^(p-2)) · ofReal(∫_{Mstar ≥ t} M_n). -/
lemma A_le_layer_integral
    [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0} {M : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale M 𝓕 μ) (hnn : ∀ n ω, 0 ≤ M n ω)
    (hp : 1 < p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((runMax M n ω) ^ p) ∂μ
      ≤ ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi (0:ℝ),
            ENNReal.ofReal (t ^ (p - 2)) *
              ENNReal.ofReal (∫ ω in {ω | t ≤ runMax M n ω}, M n ω ∂μ) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  rw [MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul μ
        (ae_of_all _ (runMax_nonneg hnn n))
        (runMax_measurable hsub n).aemeasurable hp_pos]
  apply mul_le_mul_left' _ (ENNReal.ofReal p)
  apply MeasureTheory.setLIntegral_mono_ae'
  · exact measurableSet_Ioi
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  exact layer_integrand_bound hsub hnn n ht

/-- Inner integral evaluation: `∫⁻ t in Ioc 0 M, ofReal(t^(p-2)) = ofReal(M^(p-1)/(p-1))`. -/
lemma lintegral_rpow_Ioc
    {M p : ℝ} (hM : 0 < M) (hp : 1 < p) :
    ∫⁻ t in Set.Ioc (0:ℝ) M, ENNReal.ofReal (t^(p-2)) =
      ENNReal.ofReal (M^(p-1)/(p-1)) := by
  have hpm1 : -1 < p - 2 := by linarith
  rw [show (M^(p-1)/(p-1) : ℝ) = ∫ t in Set.Ioc (0:ℝ) M, t^(p-2) from ?_]
  · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · apply MeasureTheory.IntegrableOn.integrable
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le).mp
        (intervalIntegral.intervalIntegrable_rpow' hpm1)
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (ae_of_all _ (fun t ht => Real.rpow_nonneg ht.1.le _))
  rw [← intervalIntegral.integral_of_le hM.le]
  rw [integral_rpow (Or.inl hpm1)]
  have hzp : (0:ℝ)^(p - 2 + 1) = 0 := Real.zero_rpow (by linarith : p - 2 + 1 ≠ 0)
  rw [hzp, show p - 2 + 1 = p - 1 by ring]
  ring

/-- Convert `ofReal` of Bochner set integral to `setLIntegral` of `ofReal`. -/
lemma ofReal_setIntegral_eq_setLIntegral_ofReal
    [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0} {M : ℕ → Ω → ℝ}
    (hsub : Submartingale M 𝓕 μ) (hnn : ∀ n ω, 0 ≤ M n ω) (n : ℕ)
    {t : ℝ} :
    ENNReal.ofReal (∫ ω in {ω | t ≤ runMax M n ω}, M n ω ∂μ)
      = ∫⁻ ω in {ω | t ≤ runMax M n ω}, ENNReal.ofReal (M n ω) ∂μ := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · exact (hsub.integrable n).restrict
  · exact ae_of_all _ (hnn n)

/-- Pointwise inner integral: for `Mstar ≥ 0`, integrating `t^(p-2)` against
    the indicator `𝟙{0 < t ≤ Mstar}` evaluates to `Mstar^(p-1)/(p-1)`. -/
lemma inner_t_integral
    {Mstar p : ℝ} (hMstar : 0 ≤ Mstar) (hp : 1 < p) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        {t : ℝ | t ≤ Mstar}.indicator (fun _ => (1 : ℝ≥0∞)) t
      = ENNReal.ofReal (Mstar ^ (p - 1) / (p - 1)) := by
  rcases hMstar.lt_or_eq with hpos | hzero
  · -- Mstar > 0: rewrite indicator-restricted integral as setLIntegral on Ioc.
    have h_eq : Set.EqOn
        (fun t => ENNReal.ofReal (t ^ (p - 2)) *
            {t : ℝ | t ≤ Mstar}.indicator (fun _ => (1 : ℝ≥0∞)) t)
        ((Set.Ioc 0 Mstar).indicator (fun t => ENNReal.ofReal (t ^ (p - 2))))
        (Set.Ioi (0:ℝ)) := by
      intro t ht
      simp only
      by_cases hle : t ≤ Mstar
      · have hmem1 : t ∈ {t : ℝ | t ≤ Mstar} := hle
        have hmem2 : t ∈ Set.Ioc (0:ℝ) Mstar := ⟨ht, hle⟩
        rw [Set.indicator_of_mem hmem1, mul_one, Set.indicator_of_mem hmem2]
      · have hnmem1 : t ∉ {t : ℝ | t ≤ Mstar} := hle
        have hnmem2 : t ∉ Set.Ioc (0:ℝ) Mstar := fun h => hle h.2
        rw [Set.indicator_of_notMem hnmem1, mul_zero, Set.indicator_of_notMem hnmem2]
    rw [setLIntegral_congr_fun measurableSet_Ioi h_eq]
    have hsubset : Set.Ioc (0:ℝ) Mstar ⊆ Set.Ioi 0 :=
      fun _ ht => ht.1
    have : ∫⁻ t in Set.Ioi (0:ℝ), (Set.Ioc 0 Mstar).indicator
              (fun t => ENNReal.ofReal (t ^ (p - 2))) t
            = ∫⁻ t in Set.Ioc (0:ℝ) Mstar, ENNReal.ofReal (t ^ (p - 2)) := by
      rw [setLIntegral_indicator measurableSet_Ioc,
          Set.inter_eq_left.mpr hsubset]
    rw [this]
    exact lintegral_rpow_Ioc hpos hp
  · -- Mstar = 0: both sides are 0.
    subst hzero
    have h_eq : Set.EqOn
        (fun t => ENNReal.ofReal (t ^ (p - 2)) *
            {t : ℝ | t ≤ (0:ℝ)}.indicator (fun _ => (1 : ℝ≥0∞)) t)
        (fun _ => 0) (Set.Ioi (0:ℝ)) := by
      intro t ht
      simp only
      have hnot : t ∉ {t : ℝ | t ≤ (0:ℝ)} := by
        change ¬ t ≤ 0
        exact not_le.mpr ht
      rw [Set.indicator_of_notMem hnot, mul_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioi h_eq, lintegral_zero]
    have hp10 : p - 1 ≠ 0 := by linarith
    simp [Real.zero_rpow hp10]

/-- Fubini swap stage (Tier A.2 Stage 1).

    For `p > 1`, a non-negative submartingale `M`, and a time `n`, the
    iterated integral
       `∫⁻ t in Ioi 0, ofReal(t^(p-2)) ⋅ ∫⁻_{Mstar ≥ t} ofReal(M_n) dμ`
    equals
       `∫⁻ ω, ofReal(M_n ω) ⋅ ofReal((Mstar ω)^(p-1) / (p-1)) dμ`.

    Proof: rewrite the inner set-integral as an indicator-weighted full
    integral; apply `MeasureTheory.lintegral_lintegral_swap` to swap the
    order of integration; then evaluate the inner `t`-integral pointwise
    via `inner_t_integral`. -/
lemma fubini_swap
    [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0} {M : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale M 𝓕 μ) (hnn : ∀ n ω, 0 ≤ M n ω)
    (hp : 1 < p) (n : ℕ) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ ω in {ω | t ≤ runMax M n ω}, ENNReal.ofReal (M n ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (M n ω) *
              ENNReal.ofReal ((runMax M n ω) ^ (p - 1) / (p - 1)) ∂μ := by
  -- Measurability of runMax M n and M n.
  have hRunMaxMeas : Measurable (runMax M n) := runMax_measurable hsub n
  have hsubM : Measurable (M n) :=
    ((hsub.stronglyMeasurable n).measurable).mono (𝓕.le n) le_rfl
  -- Joint set {(t,ω) | t ≤ runMax M n ω} is product-measurable as the
  -- preimage of {(a,b) : ℝ×ℝ | a ≤ b} under (fst, runMax ∘ snd).
  have hJointSet : MeasurableSet {pr : ℝ × Ω | pr.1 ≤ runMax M n pr.2} := by
    have h1 : Measurable (fun pr : ℝ × Ω => pr.1) := measurable_fst
    have h2 : Measurable (fun pr : ℝ × Ω => runMax M n pr.2) :=
      hRunMaxMeas.comp measurable_snd
    exact measurableSet_le h1 h2
  -- Step 1: rewrite the inner setLIntegral as a full lintegral via indicator.
  have step1 : ∀ t,
      ∫⁻ ω in {ω | t ≤ runMax M n ω}, ENNReal.ofReal (M n ω) ∂μ
        = ∫⁻ ω, {ω | t ≤ runMax M n ω}.indicator
                  (fun ω => ENNReal.ofReal (M n ω)) ω ∂μ := by
    intro t
    rw [lintegral_indicator (measurableSet_le measurable_const hRunMaxMeas)]
  -- Step 2: pull the constant ofReal(t^(p-2)) inside the inner lintegral.
  have step2 : ∀ t, ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ ω, {ω | t ≤ runMax M n ω}.indicator
                (fun ω => ENNReal.ofReal (M n ω)) ω ∂μ
      = ∫⁻ ω, ENNReal.ofReal (t ^ (p - 2)) *
              {ω | t ≤ runMax M n ω}.indicator
                (fun ω => ENNReal.ofReal (M n ω)) ω ∂μ := by
    intro t
    exact (lintegral_const_mul _ ((ENNReal.measurable_ofReal.comp hsubM).indicator
            (measurableSet_le measurable_const hRunMaxMeas))).symm
  -- Combine step1 + step2 to a clean bivariate integrand expression.
  simp_rw [step1, step2]
  -- Joint measurability of the bivariate integrand.
  have hF_meas : Measurable (fun pr : ℝ × Ω =>
      ENNReal.ofReal (pr.1 ^ (p - 2)) *
        {q : ℝ × Ω | q.1 ≤ runMax M n q.2}.indicator
          (fun q => ENNReal.ofReal (M n q.2)) pr) := by
    refine Measurable.mul ?_ ?_
    · refine ENNReal.measurable_ofReal.comp ?_
      exact (measurable_fst : Measurable (fun pr : ℝ × Ω => pr.1)).pow_const (p - 2)
    · refine Measurable.indicator ?_ hJointSet
      exact ENNReal.measurable_ofReal.comp (hsubM.comp measurable_snd)
  -- Rewrite the LHS with indicator on Ioi 0 (so it becomes a full lintegral
  -- over ℝ) and apply lintegral_lintegral_swap on ℝ × Ω.
  rw [← lintegral_indicator measurableSet_Ioi]
  -- LHS now is ∫⁻ t, (Ioi 0).indicator (fun t => ∫⁻ ω, F(t,ω) ∂μ) t ∂volume
  -- Massage to ∫⁻ t, ∫⁻ ω, (Ioi 0).indicator (fun _ => F(t,ω)) t ∂μ
  have lhs_rewrite : ∫⁻ a, (Set.Ioi (0:ℝ)).indicator
        (fun t => ∫⁻ ω, ENNReal.ofReal (t ^ (p - 2)) *
                {ω | t ≤ runMax M n ω}.indicator
                  (fun ω => ENNReal.ofReal (M n ω)) ω ∂μ) a
      = ∫⁻ t, ∫⁻ ω, (Set.Ioi (0:ℝ)).indicator
              (fun s => ENNReal.ofReal (s ^ (p - 2)) *
                {ω | s ≤ runMax M n ω}.indicator
                  (fun ω => ENNReal.ofReal (M n ω)) ω) t ∂μ := by
    apply lintegral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem ht]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, ← lintegral_zero (μ := μ)]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_notMem ht]
  rw [lhs_rewrite]
  -- Now apply lintegral_lintegral_swap.
  have hSwap_meas : AEMeasurable
      (Function.uncurry (fun t ω => (Set.Ioi (0:ℝ)).indicator
          (fun s => ENNReal.ofReal (s ^ (p - 2)) *
            {ω | s ≤ runMax M n ω}.indicator
              (fun ω => ENNReal.ofReal (M n ω)) ω) t))
      (volume.prod μ) := by
    refine (Measurable.indicator ?_ ?_).aemeasurable
    · exact hF_meas
    · exact measurable_fst measurableSet_Ioi
  rw [lintegral_lintegral_swap hSwap_meas]
  -- Now have ∫⁻ ω, ∫⁻ t, indicator(Ioi 0) F(t,ω) ∂volume ∂μ.
  -- For each ω, the inner is the integral over Ioi 0 of
  --   ofReal(t^(p-2)) * 𝟙{t ≤ runMax M n ω} * ofReal(M n ω)
  -- = ofReal(M n ω) * (∫⁻ t in Ioi 0, ofReal(t^(p-2)) * 𝟙{t ≤ Mstar ω})
  -- = ofReal(M n ω) * ofReal((runMax M n ω)^(p-1) / (p-1))  [inner_t_integral]
  apply lintegral_congr_ae
  filter_upwards with ω
  -- Reduce the inner integral.
  have h_inner_simp :
      ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
          (fun s => ENNReal.ofReal (s ^ (p - 2)) *
            {ω' | s ≤ runMax M n ω'}.indicator
              (fun ω' => ENNReal.ofReal (M n ω')) ω) t
        = ENNReal.ofReal (M n ω) *
            ENNReal.ofReal ((runMax M n ω) ^ (p - 1) / (p - 1)) := by
    -- Rewrite the inner indicator
    have h_pointwise : ∀ t,
        (Set.Ioi (0:ℝ)).indicator
            (fun s => ENNReal.ofReal (s ^ (p - 2)) *
              {ω' | s ≤ runMax M n ω'}.indicator
                (fun ω' => ENNReal.ofReal (M n ω')) ω) t
          = ENNReal.ofReal (M n ω) *
              ((Set.Ioi (0:ℝ)).indicator
                (fun s => ENNReal.ofReal (s ^ (p - 2)) *
                  {s : ℝ | s ≤ runMax M n ω}.indicator
                    (fun _ => (1 : ℝ≥0∞)) s)) t := by
      intro t
      by_cases ht : t ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        by_cases hle : t ≤ runMax M n ω
        · have hmem1 : ω ∈ {ω' | t ≤ runMax M n ω'} := hle
          have hmem2 : t ∈ {s : ℝ | s ≤ runMax M n ω} := hle
          rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2, mul_one]
          ring
        · have hnmem1 : ω ∉ {ω' | t ≤ runMax M n ω'} := hle
          have hnmem2 : t ∉ {s : ℝ | s ≤ runMax M n ω} := hle
          rw [Set.indicator_of_notMem hnmem1, Set.indicator_of_notMem hnmem2,
              mul_zero, mul_zero]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
    simp_rw [h_pointwise]
    rw [lintegral_const_mul']
    · -- The inner lintegral matches inner_t_integral.
      have h_eq :
          ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
              (fun s => ENNReal.ofReal (s ^ (p - 2)) *
                {s : ℝ | s ≤ runMax M n ω}.indicator
                  (fun _ => (1 : ℝ≥0∞)) s) t
            = ∫⁻ t in Set.Ioi (0:ℝ),
                ENNReal.ofReal (t ^ (p - 2)) *
                  {s : ℝ | s ≤ runMax M n ω}.indicator
                    (fun _ => (1 : ℝ≥0∞)) t := by
        rw [← lintegral_indicator measurableSet_Ioi]
      rw [h_eq, inner_t_integral (runMax_nonneg hnn n ω) hp]
    · exact ENNReal.ofReal_ne_top
  rw [h_inner_simp]

/-- Stage 2 (Hölder + algebra): bound the post-Fubini integral by the
    Hölder inequality, yielding the L^p submartingale bound. -/
lemma holder_step
    [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0} {M : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale M 𝓕 μ) (hnn : ∀ n ω, 0 ≤ M n ω)
    (hp : 1 < p) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal ((runMax M n ω) ^ p) ∂μ)
      ≤ ENNReal.ofReal (p / (p - 1)) *
          (∫⁻ ω, ENNReal.ofReal (M n ω ^ p) ∂μ) ^ (p⁻¹) *
          (∫⁻ ω, ENNReal.ofReal ((runMax M n ω) ^ p) ∂μ) ^ ((p - 1) / p) := by
  sorry

/-- Doob's L^p maximal inequality for non-negative submartingales.

    PROOF SKELETON — main theorem still pending the truncation + eLpNorm
    conversion (see TODO list at top of file). -/
theorem doob_lp_maximal_inequality
    [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0} {M : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale M 𝓕 μ) (hnn : ∀ n ω, 0 ≤ M n ω)
    (hp : 1 < p) (n : ℕ) :
    eLpNorm (runMax M n) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) *
          eLpNorm (M n) (ENNReal.ofReal p) μ := by
  sorry

end HybridVerify.DoobLp
