/-
  HybridVerify.FTAP
  Theorem 2.6.7: First Fundamental Theorem of Asset Pricing (⇒ direction).
  EMM existence ⇒ no arbitrage. Uses HybridVerify.MartingaleTransform.
-/
import Mathlib
import HybridVerify.MartingaleTransform

namespace HybridVerify

open MeasureTheory ProbabilityTheory

/-- A discrete-time, finite-horizon market specification with an equivalent
    martingale measure (EMM). Theorem 2.6.7 (⇒ direction of FTAP) is
    **derived** from this data plus a bounded predictable strategy `φ`, by
    applying `MartingaleTransform.transform_is_martingale` to the discounted
    price `S` under `Q`. -/
structure FundamentalTheoremOfAssetPricing {Ω : Type*} [m0 : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (𝓕 : Filtration ℕ m0)
    (S : ℕ → Ω → ℝ) where
  S_adapted : StronglyAdapted 𝓕 S
  Q : Measure Ω
  Q_isProbability : IsProbabilityMeasure Q
  Q_abs_P : Q ≪ P
  P_abs_Q : P ≪ Q
  S_Q_martingale : Martingale S 𝓕 Q

namespace FundamentalTheoremOfAssetPricing

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {𝓕 : Filtration ℕ m0} {S : ℕ → Ω → ℝ}

/-- **Theorem 2.6.7 (FTAP, ⇒ direction)**: existence of an equivalent martingale
    measure precludes arbitrage. Given a bounded predictable strategy `φ`, the
    discounted P&L `V_T = ∑ φ_{t+1} (S_{t+1} − S_t)` cannot be nonnegative
    `P`-a.s. and strictly positive on a `P`-non-null set. -/
theorem emm_implies_no_arbitrage
    (FTAP : FundamentalTheoremOfAssetPricing P T 𝓕 S)
    (φ : ℕ → Ω → ℝ)
    (hφ_pred : StronglyAdapted 𝓕 (fun n => φ (n + 1)))
    (hφ_bdd : ∃ K : ℝ, ∀ n ω, |φ n ω| ≤ K)
    (hV_nonneg : ∀ᵐ ω ∂P,
      0 ≤ ∑ t ∈ Finset.range T, φ (t + 1) ω * (S (t + 1) ω - S t ω)) :
    P {ω | 0 < ∑ t ∈ Finset.range T, φ (t + 1) ω * (S (t + 1) ω - S t ω)} = 0 := by
  haveI : IsProbabilityMeasure FTAP.Q := FTAP.Q_isProbability
  set V : ℕ → Ω → ℝ := fun n ω =>
    ∑ t ∈ Finset.range n, φ (t + 1) ω * (S (t + 1) ω - S t ω)
  have hMT : MartingaleTransform FTAP.Q 𝓕 S φ V :=
    { martingale_M := FTAP.S_Q_martingale
      predictable_A := hφ_pred
      A_bounded := hφ_bdd
      transform_def := fun n ω => rfl }
  have hV_mart : Martingale V 𝓕 FTAP.Q := hMT.transform_is_martingale
  have hV_T_int : Integrable (V T) FTAP.Q := hV_mart.integrable T
  have hV_T_eq_condExp_V0 : FTAP.Q[V T | 𝓕 0] =ᵐ[FTAP.Q] V 0 :=
    hV_mart.condExp_ae_eq (Nat.zero_le T)
  have hV0_zero : V 0 = 0 := by funext ω; simp [V]
  have hV_T_integral : ∫ ω, V T ω ∂FTAP.Q = 0 := by
    have h_int_V0 : ∫ ω, V 0 ω ∂FTAP.Q = 0 := by rw [hV0_zero]; simp
    rw [← h_int_V0]
    have hcondInt : ∫ ω, V T ω ∂FTAP.Q = ∫ ω, (FTAP.Q[V T | 𝓕 0]) ω ∂FTAP.Q :=
      (integral_condExp (𝓕.le 0)).symm
    rw [hcondInt]
    refine integral_congr_ae ?_
    exact hV_T_eq_condExp_V0
  have hV_T_nonneg_Q : 0 ≤ᵐ[FTAP.Q] V T :=
    FTAP.Q_abs_P.ae_le hV_nonneg
  have hV_T_zero_Q : V T =ᵐ[FTAP.Q] 0 := by
    have h_eq := (integral_eq_zero_iff_of_nonneg_ae hV_T_nonneg_Q hV_T_int).mp hV_T_integral
    filter_upwards [h_eq] with ω hω
    simpa using hω
  have h_ne_zero_Q : FTAP.Q {ω | V T ω ≠ 0} = 0 := by
    rw [← MeasureTheory.ae_iff]
    filter_upwards [hV_T_zero_Q] with ω hω
    show V T ω = 0
    simpa using hω
  have hsub : {ω | 0 < V T ω} ⊆ {ω | V T ω ≠ 0} := fun ω hω => ne_of_gt hω
  have h_pos_Q_zero : FTAP.Q {ω | 0 < V T ω} = 0 :=
    measure_mono_null hsub h_ne_zero_Q
  have h_pos_P_zero : P {ω | 0 < V T ω} = 0 :=
    FTAP.P_abs_Q h_pos_Q_zero
  have h_eq_set : {ω | 0 < ∑ t ∈ Finset.range T, φ (t + 1) ω * (S (t + 1) ω - S t ω)} =
                  {ω | 0 < V T ω} := by
    ext ω; rfl
  rw [h_eq_set]
  exact h_pos_P_zero

end FundamentalTheoremOfAssetPricing

end HybridVerify
