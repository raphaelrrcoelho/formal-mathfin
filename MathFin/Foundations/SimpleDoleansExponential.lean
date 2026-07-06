/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.BrownianMartingale

/-!
# The simple Doléans exponential — the martingale foundation of adapted Girsanov (Track α)

Route-α, brick α1 (`docs/plans/2026-07-06-girsanov-track-alpha.md`). The market price
of risk `θ` of the general Girsanov theorem (`gir-thm-9.1.8`) is **adapted** (path
dependent), so the Doléans density `exp(∫θ dB − ½∫θ² ds)` has a *random* multiplier in
each partition cell. The constant-θ Wald exponential (`waldExponential_isMartingale`)
freezes each increment against a **deterministic** function of the past
(`condExp_func_increment` via `condExp_indep_eq`); the adapted case needs the same
freezing against an `𝓕_r`-measurable **random** multiplier `c`.

This file proves that genuinely new estimate:

* `MathFin.condExp_exp_adapted_mul_increment` —
  `𝔼[exp(c·(X_t − X_r)) | 𝓕_r] = exp(½ c² (t − r))` a.e., for `c` `𝓕_r`-measurable and
  bounded, `r ≤ t`.

The mechanism is the **freezing lemma**: the increment `Δ = X_t − X_r` is independent of
`𝓕_r` (`hX.indep`), so the joint law of the `𝓕_r`-measurable pair `(c, ·)` and `Δ`
factorizes (`indepFun_iff_map_prod_eq_prod_map_map`), and Fubini (`integral_prod`) freezes
`c` while the inner Gaussian MGF `∫ exp(c·z) d𝒩(0,t−r) = exp(½c²(t−r))`
(`integral_exp_mul_gaussianReal_zero`) collapses the increment.

Everything else in Track α (the running exponential's martingale property α2, the simple-θ
Girsanov α3) reuses the constant-θ apparatus in `GirsanovConstantTheta.lean` once this
brick lands.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The freezing set-integral identity.** For a bounded `𝓕_r`-measurable multiplier `c`
and an increment `Δ` with law `𝒩(0,v)` independent of `𝓕_r`, and any `A ∈ 𝓕_r`,
`∫_A exp(c·Δ) = ∫_A exp(½ c² v)`. The `𝓕_r`-measurable `(c, 𝟙_A)` is independent of `Δ`, so
the joint law factorizes (`indepFun_iff_map_prod_eq_prod_map_map`) and Fubini
(`integral_prod`) freezes `c`, leaving the inner Gaussian MGF `∫ exp(c·z) d𝒩(0,v) =
exp(½c²v)` (`integral_exp_mul_gaussianReal_zero`). -/
private lemma condExp_exp_adapted_freeze_setIntegral
    {c : Ω → ℝ} {r : ℝ≥0} (hc_frf : Measurable[(𝓕 r : MeasurableSpace Ω)] c)
    {K : ℝ} (hK : ∀ ω, |c ω| ≤ K)
    {Δ : Ω → ℝ} (hΔ_meas : Measurable Δ) {v : ℝ≥0} (hΔlaw : HasLaw Δ (gaussianReal 0 v) P)
    (hindep0 : Indep (MeasurableSpace.comap Δ (borel ℝ)) (𝓕 r) P)
    {A : Set Ω} (hA : MeasurableSet[(𝓕 r : MeasurableSpace Ω)] A) :
    ∫ ω in A, Real.exp (c ω * Δ ω) ∂P = ∫ ω in A, Real.exp ((c ω) ^ 2 * (v : ℝ) / 2) ∂P := by
  classical
  have hc_meas : Measurable c := hc_frf.mono (𝓕.le r) le_rfl
  have hA_mΩ : MeasurableSet A := (𝓕.le r) A hA
  -- Pointwise domination of `exp(c·Δ)` by two Gaussian-MGF terms (no `0 ≤ K` needed).
  have hbound : ∀ ω, Real.exp (c ω * Δ ω)
      ≤ Real.exp (K * Δ ω) + Real.exp (-K * Δ ω) := by
    intro ω
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hK ω)
    rcases le_total 0 (Δ ω) with hΔ | hΔ
    · exact le_add_of_le_of_nonneg (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hΔ))
        (Real.exp_nonneg _)
    · exact le_add_of_nonneg_of_le (Real.exp_nonneg _)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlo hΔ))
  have hbnd_int : Integrable (fun ω ↦ Real.exp (K * Δ ω) + Real.exp (-K * Δ ω)) P :=
    (integrable_exp_mul_of_hasLaw hΔlaw K).add (integrable_exp_mul_of_hasLaw hΔlaw (-K))
  -- The `𝓕_r`-measurable pair `Y = (c, 𝟙_A)` and the coupling `F ((cc,ind),z) = ind·exp(cc·z)`.
  set Y : Ω → ℝ × ℝ := fun ω ↦ (c ω, A.indicator (fun _ ↦ (1 : ℝ)) ω) with hYdef
  set F : (ℝ × ℝ) × ℝ → ℝ := fun p ↦ p.1.2 * Real.exp (p.1.1 * p.2) with hFdef
  have hY_meas : Measurable Y := hc_meas.prodMk (measurable_const.indicator hA_mΩ)
  have hY_frf : Measurable[(𝓕 r : MeasurableSpace Ω)] Y :=
    hc_frf.prodMk (measurable_const.indicator hA)
  have hF_meas : Measurable F :=
    (measurable_fst.snd).mul ((measurable_fst.fst.mul measurable_snd).exp)
  -- Independence of `Y` and `Δ`, hence the joint law factorizes.
  have hindepYΔ : IndepFun Y Δ P :=
    Indep.symm (indep_of_indep_of_le_right hindep0 hY_frf.comap_le)
  have hjoint : P.map (fun ω ↦ (Y ω, Δ ω)) = (P.map Y).prod (P.map Δ) :=
    (indepFun_iff_map_prod_eq_prod_map_map hY_meas.aemeasurable hΔ_meas.aemeasurable).mp hindepYΔ
  have hYΔ_aem : AEMeasurable (fun ω ↦ (Y ω, Δ ω)) P := (hY_meas.prodMk hΔ_meas).aemeasurable
  -- `F` is integrable against the joint law (dominated by the two Gaussian-MGF terms).
  have hFcomp_le : ∀ ω, ‖F (Y ω, Δ ω)‖ ≤ Real.exp (K * Δ ω) + Real.exp (-K * Δ ω) := by
    intro ω
    have hval : F (Y ω, Δ ω) = A.indicator (fun _ ↦ (1 : ℝ)) ω * Real.exp (c ω * Δ ω) := by
      simp only [hFdef, hYdef]
    rw [hval, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]; simp only [abs_one, one_mul]; exact hbound ω
    · rw [Set.indicator_apply, if_neg hω, abs_zero, zero_mul]; positivity
  have hFcomp_int : Integrable (fun ω ↦ F (Y ω, Δ ω)) P :=
    Integrable.mono' hbnd_int (hF_meas.comp (hY_meas.prodMk hΔ_meas)).aestronglyMeasurable
      (Filter.Eventually.of_forall hFcomp_le)
  have hF_int_prod : Integrable F ((P.map Y).prod (P.map Δ)) := by
    rw [← hjoint, integrable_map_measure hF_meas.aestronglyMeasurable hYΔ_aem]
    exact hFcomp_int
  -- Compute the inner integral (freeze `y`, evaluate the Gaussian MGF).
  have hinner : ∀ y : ℝ × ℝ, ∫ z, F (y, z) ∂(P.map Δ)
      = y.2 * Real.exp (y.1 ^ 2 * (v : ℝ) / 2) := by
    intro y
    rw [hΔlaw.map_eq]
    have : (fun z ↦ F (y, z)) = fun z ↦ y.2 * Real.exp (y.1 * z) := by funext z; rw [hFdef]
    rw [this, integral_const_mul, integral_exp_mul_gaussianReal_zero]
  -- Chain: setIntegral → integral of `F∘(Y,Δ)` → joint law → Fubini → back.
  rw [← integral_indicator hA_mΩ, ← integral_indicator hA_mΩ]
  have hLHS : (fun ω ↦ A.indicator (fun ω ↦ Real.exp (c ω * Δ ω)) ω)
      = fun ω ↦ F (Y ω, Δ ω) := by
    funext ω; rw [hFdef, hYdef]
    by_cases hω : ω ∈ A <;> simp [hω]
  have hRHS : (fun ω ↦ A.indicator (fun ω ↦ Real.exp ((c ω) ^ 2 * (v : ℝ) / 2)) ω)
      = fun ω ↦ (Y ω).2 * Real.exp ((Y ω).1 ^ 2 * (v : ℝ) / 2) := by
    funext ω; rw [hYdef]
    by_cases hω : ω ∈ A <;> simp [hω]
  rw [hLHS, hRHS]
  rw [← integral_map hYΔ_aem hF_meas.aestronglyMeasurable, hjoint,
    integral_prod F hF_int_prod]
  rw [← integral_map hY_meas.aemeasurable
        (by fun_prop : AEStronglyMeasurable
          (fun y : ℝ × ℝ ↦ y.2 * Real.exp (y.1 ^ 2 * (v : ℝ) / 2)) (P.map Y))]
  exact integral_congr_ae (Filter.Eventually.of_forall hinner)

variable [SigmaFiniteFiltration P 𝓕] {X : ℝ≥0 → Ω → ℝ}
  [hX : IsFilteredPreBrownian X 𝓕 P] in
/-- **Conditional MGF of a Brownian increment against a random adapted multiplier.**
For `c` `𝓕_r`-measurable and bounded, and `r ≤ t`,
`𝔼[exp(c·(X_t − X_r)) | 𝓕_r] = exp(½ c² (t − r))` a.e.

The `𝓕_r`-measurable `c` is *frozen*: `Δ = X_t − X_r` is independent of `𝓕_r`, so the joint
law factorizes and Fubini evaluates the inner Gaussian MGF `∫ exp(c·z) d𝒩(0,t−r)`. This is
the adapted-multiplier generalization of the constant-`α` freezing inside
`waldExponential_isMartingale`. -/
theorem condExp_exp_adapted_mul_increment
    {c : Ω → ℝ} {r : ℝ≥0} (hc : StronglyMeasurable[(𝓕 r : MeasurableSpace Ω)] c)
    {K : ℝ} (hK : ∀ ω, |c ω| ≤ K) {t : ℝ≥0} (hrt : r ≤ t) :
    P[fun ω ↦ Real.exp (c ω * (X t ω - X r ω)) | (𝓕 r : MeasurableSpace Ω)]
      =ᵐ[P] fun ω ↦ Real.exp ((c ω) ^ 2 * ((t : ℝ) - (r : ℝ)) / 2) := by
  have hc_meas : Measurable c := (hc.mono (𝓕.le r)).measurable
  have h_meas_diff : Measurable (fun ω ↦ X t ω - X r ω) :=
    (((hX.stronglyAdapted t).mono (𝓕.le t)).measurable).sub
      (((hX.stronglyAdapted r).mono (𝓕.le r)).measurable)
  -- The increment law and the variance identity `nndist = t − r`.
  set v : ℝ≥0 := nndist (t : ℝ) (r : ℝ) with hvdef
  have hΔlaw : HasLaw (fun ω ↦ X t ω - X r ω) (gaussianReal 0 v) P := hX.hasLaw_sub t r
  have hv : (v : ℝ) = (t : ℝ) - (r : ℝ) := by
    rw [hvdef, coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrt))]
  have hindep0 : Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X r ω) (borel ℝ)) (𝓕 r) P :=
    hX.indep r t hrt
  -- The candidate conditional expectation `g = exp(½ c² (t−r))` is `𝓕_r`-measurable.
  have hg_sm : StronglyMeasurable[(𝓕 r : MeasurableSpace Ω)]
      (fun ω ↦ Real.exp ((c ω) ^ 2 * ((t : ℝ) - (r : ℝ)) / 2)) :=
    Real.continuous_exp.comp_stronglyMeasurable
      ((((continuous_pow 2).comp_stronglyMeasurable hc).mul stronglyMeasurable_const).div
        stronglyMeasurable_const)
  -- Integrability of `f = exp(c·Δ)` and `g`.
  have hf_int : Integrable (fun ω ↦ Real.exp (c ω * (X t ω - X r ω))) P := by
    refine Integrable.mono'
      ((integrable_exp_mul_of_hasLaw hΔlaw K).add (integrable_exp_mul_of_hasLaw hΔlaw (-K)))
      (hc_meas.mul h_meas_diff).exp.aestronglyMeasurable (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hK ω)
    rcases le_total 0 (X t ω - X r ω) with hΔ | hΔ
    · exact le_add_of_le_of_nonneg (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hΔ))
        (Real.exp_nonneg _)
    · exact le_add_of_nonneg_of_le (Real.exp_nonneg _)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlo hΔ))
  have hg_int : Integrable (fun ω ↦ Real.exp ((c ω) ^ 2 * ((t : ℝ) - (r : ℝ)) / 2)) P := by
    refine Integrable.mono' (integrable_const (Real.exp (K ^ 2 * ((t : ℝ) - (r : ℝ)) / 2)))
      (hg_sm.mono (𝓕.le r)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    refine Real.exp_le_exp.mpr ?_
    have hsq : (c ω) ^ 2 ≤ K ^ 2 := by
      obtain ⟨hlo, hhi⟩ := abs_le.mp (hK ω); nlinarith [abs_nonneg (c ω), hK ω]
    have hnn : (0 : ℝ) ≤ (t : ℝ) - (r : ℝ) := sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrt)
    have := mul_le_mul_of_nonneg_right hsq hnn
    linarith
  -- Assemble via the set-integral characterization of conditional expectation.
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le r) hf_int
    (fun A _ _ ↦ hg_int.integrableOn) (fun A hA _ ↦ ?_) hg_sm.aestronglyMeasurable).symm
  have hfreeze := condExp_exp_adapted_freeze_setIntegral (P := P) (𝓕 := 𝓕) hc.measurable hK
    h_meas_diff hΔlaw hindep0 hA
  rw [hv] at hfreeze
  exact hfreeze.symm

end MathFin
