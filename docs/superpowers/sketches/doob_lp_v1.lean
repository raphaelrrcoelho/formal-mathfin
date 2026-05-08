/-
  Doob's L^p maximal inequality (textbook Theorem 2.4.6, Tier A.2).

  Goal: for `p > 1` and a non-negative submartingale `(M_n)`,
        ‖max_{k ≤ n} M_k‖_p ≤ (p / (p − 1)) · ‖M_n‖_p.

  Strategy follows the standard layer-cake + maximal-inequality + Fubini +
  Hölder argument; see `docs/superpowers/specs/2026-05-06-real-proof-tiers.md`
  §A.2 for the high-level outline.

  Status (2026-05-08): 8 lemmas verified locally against Mathlib v4.18.0
  (lean-interact, with the standard `~/.cache/mathlib/` ltar cache):

  | # | Name                          | Content                                  |
  |---|-------------------------------|------------------------------------------|
  | 1 | runMax                        | Definition (running max)                 |
  | 2 | runMax_nonneg                 | non-negativity                           |
  | 3 | runMax_measurable             | via `Finset.measurable_range_sup''`      |
  | 4 | runMax_stronglyMeasurable     | upgrade from Measurable                  |
  | 5 | layer_meas_bound              | maximal_ineq at fixed t > 0              |
  | 6 | lintegral_runMax_rpow_eq_layer| layer cake                               |
  | 7 | layer_integrand_bound         | pointwise (in t) integrand bound         |
  | 8 | A_le_layer_integral           | A ≤ ofReal p ⋅ ∫⁻ t in Ioi 0, …         |

  Remaining (each non-trivial):
  - Inner integral: ∫⁻ t in Ioc 0 M, ofReal(t^(p-2)) = ofReal(M^(p-1)/(p-1))
  - Fubini swap (the dominant cost): convert
      ∫⁻ t in Ioi 0, ofReal(t^(p-2)) ⋅ ofReal(∫_{Mstar≥t} M_n)
    into
      (1/(p-1)) ⋅ ∫⁻ ω, ofReal(M_n ω) ⋅ ofReal(Mstar^(p-1))
    via `lintegral_lintegral_swap` on the joint indicator of
    `{(t, ω) | 0 < t ∧ t ≤ Mstar M n ω}`.
  - Hölder via `ENNReal.lintegral_mul_le_Lp_mul_Lq` with conjugate `p, p/(p-1)`.
  - ENNReal algebra to extract A^(1/p) ≤ ofReal(p/(p-1)) ⋅ B^(1/p).
  - Convert eLpNorm = (∫⁻ rpow)^(1/p) for the final form.

  These stay multi-day work as the spec already documents.
-/

import Mathlib

open MeasureTheory ProbabilityTheory ENNReal Filter Set
open scoped BigOperators

noncomputable section

namespace HybridVerify.DoobLp

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω}

/-- Running maximum of `M` over `0..n`. -/
def runMax (M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_succ (fun k => M k ω)

lemma runMax_nonneg {M : ℕ → Ω → ℝ} (hnn : ∀ n ω, 0 ≤ M n ω) (n : ℕ) (ω : Ω) :
    0 ≤ runMax M n ω :=
  le_trans (hnn 0 ω)
    (Finset.le_sup' (f := fun k => M k ω) (Finset.mem_range.mpr (Nat.succ_pos n)))

lemma runMax_measurable {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsub : Submartingale M 𝓕 μ) (n : ℕ) :
    Measurable (runMax M n) := by
  unfold runMax
  exact Finset.measurable_range_sup''
    (fun k _ => ((hsub.adapted k).mono (𝓕.le k)).measurable)

lemma runMax_stronglyMeasurable {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ m0}
    (hsub : Submartingale M 𝓕 μ) (n : ℕ) :
    StronglyMeasurable (runMax M n) :=
  (runMax_measurable hsub n).stronglyMeasurable

/-- Maximum-inequality at a fixed positive level `t`. Direct rephrasing of
    `MeasureTheory.maximal_ineq` with `ε := t.toNNReal`. -/
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

/-- Layer-cake step: rewrite `∫⁻ ofReal (Mstar^p)` as a layer integral.
    Direct application of `MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul`. -/
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

/-- Pointwise (in `t > 0`) integrand bound combining the layer-measure
    bound with the algebraic identity `t^(p-1) = t^(p-2) ⋅ t`. -/
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

/-- Combining steps: `∫⁻ ofReal((Mstar)^p) ≤ ofReal p ⋅ ∫⁻ t in Ioi 0,
    ofReal(t^(p-2)) ⋅ ofReal(∫_{Mstar ≥ t} M_n)`. -/
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

/-- Doob's L^p maximal inequality for non-negative submartingales.

    PROOF SKELETON — main theorem still pending the Fubini swap and
    subsequent algebra (see TODO list below). The verified building blocks
    above (`A_le_layer_integral`, `layer_integrand_bound`, `layer_meas_bound`,
    `lintegral_runMax_rpow_eq_layer`) reduce the problem to:

      Fubini swap:
        ∫⁻ t in Ioi 0, ofReal(t^(p-2)) ⋅ ofReal(∫_{Mstar≥t} M_n) ∂t
        = (1/(p-1)) ⋅ ∫⁻ ω, ofReal(M_n ω ⋅ Mstar^(p-1)) ∂μ
      via `MeasureTheory.lintegral_lintegral_swap` and the inner integral
      `∫⁻ t in Ioc 0 M, ofReal(t^(p-2)) = ofReal(M^(p-1)/(p-1))`.

      Hölder: `ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p.HolderConjugate (p/(p-1))`.

      Solve for `A^(1/p)`: standard ENNReal manipulation, case-splitting on
      `A ∈ {0, ⊤, finite}`.

      Convert: `eLpNorm f (ofReal p) μ = (∫⁻ ofReal(f^p))^(1/p)` for non-neg f.
-/
theorem doob_lp_maximal_inequality
    [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0} {M : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale M 𝓕 μ) (hnn : ∀ n ω, 0 ≤ M n ω)
    (hp : 1 < p) (n : ℕ) :
    eLpNorm (runMax M n) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) *
          eLpNorm (M n) (ENNReal.ofReal p) μ := by
  sorry

end HybridVerify.DoobLp
