/-
  Doob's L^p maximal inequality (textbook Theorem 2.4.6, Tier A.2).

  Goal: for `p > 1` and a non-negative submartingale `(M_n)`,
        ‖max_{k ≤ n} M_k‖_p ≤ (p / (p − 1)) · ‖M_n‖_p.

  Strategy follows the standard layer-cake + maximal-inequality + Fubini +
  Hölder argument; see `docs/superpowers/specs/2026-05-06-real-proof-tiers.md`
  §A.2 for the high-level outline.

  Status: 6 helper lemmas verified locally against Mathlib v4.18.0
  (lean-interact, 2026-05-08). Main theorem is still the multi-day work
  (Fubini swap is the dominant remaining cost).
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

/-- A non-negative submartingale's running max is non-negative. -/
lemma runMax_nonneg {M : ℕ → Ω → ℝ} (hnn : ∀ n ω, 0 ≤ M n ω) (n : ℕ) (ω : Ω) :
    0 ≤ runMax M n ω :=
  le_trans (hnn 0 ω)
    (Finset.le_sup' (f := fun k => M k ω) (Finset.mem_range.mpr (Nat.succ_pos n)))

/-- The running max of an adapted process is measurable (uses
    `Finset.measurable_range_sup''` from Mathlib). -/
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

/-- Doob's L^p maximal inequality for non-negative submartingales.

    Status: NOT YET PROVED. The remaining steps (after the lemmas above):

    1. Combine `lintegral_runMax_rpow_eq_layer` and `layer_meas_bound`:
       for each `t > 0`, `μ {Mstar ≥ t} ≤ (1/t) · ENNReal.ofReal (∫_{...} M_n)`,
       so the layer integrand is bounded by `t^(p-2) · ENNReal.ofReal (∫_{...} M_n)`.

    2. Fubini swap (THE DELICATE STEP — joint measurability of the
       indicator `Set.indicator {(t, ω) | t ≤ Mstar M n ω} fun (t, _) => t`
       in the product space `Ioi 0 × Ω` is the technical hurdle):

       `∫⁻ t in Ioi 0, t^(p-2) · ofReal (∫_{Mstar ≥ t} M_n)`
       `= ∫⁻ ω, ofReal (M_n ω) · (∫⁻ t in Ioo 0 (runMax M n ω), t^(p-2)) ∂μ`
       `= 1/(p-1) · ∫⁻ ω, ofReal (M_n ω · runMax^(p-1))`.

    3. Apply Hölder (`ENNReal.lintegral_mul_le_Lp_mul_Lq`) with conjugate
       exponent `q = p/(p-1)`:

       `∫⁻ ω, ofReal (M_n ω) · ofReal (runMax^(p-1))`
       `≤ (∫⁻ ω, ofReal (M_n ω)^p)^(1/p) · (∫⁻ ω, ofReal (runMax^(p-1))^q)^(1/q)`
       `= (∫⁻ M_n^p)^(1/p) · (∫⁻ runMax^p)^((p-1)/p)`.

    4. Set `A := ∫⁻ runMax^p`, `B := ∫⁻ M_n^p`. Steps 1-3 give:
       `A ≤ ofReal (p/(p-1)) · B^(1/p) · A^((p-1)/p)`.

    5. Case split on `A`:
       - `A = 0` ⟹ `eLpNorm runMax = 0`, conclusion immediate.
       - `A = ⊤` ⟹ if `B < ⊤` (from `M_n ∈ L^p` hypothesis, currently NOT in our
         signature so we'd need to add it), then 4 forces `A < ⊤`, contradiction.
       - `0 < A < ⊤` ⟹ divide both sides by `A^((p-1)/p)` to get
         `A^(1/p) ≤ ofReal (p/(p-1)) · B^(1/p)`, i.e., the goal after rewriting
         `eLpNorm = (∫⁻ rpow)^(1/p)` (uses
         `MemLp.eLpNorm_eq_integral_rpow_norm` or unfolding `eLpNorm`).

    Estimated remaining effort: 1-3 focused days (matches the spec).
    The hardest remaining step is the Fubini swap; everything else is ENNReal
    algebra plus citing existing Mathlib lemmas.
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
