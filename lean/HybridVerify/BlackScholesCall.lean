/-
  HybridVerify.BlackScholesCall

  Derivation of the Black-Scholes European call pricing formula from the
  risk-neutral lognormal hypothesis:

    C(S_0, K, r, σ, T) = S_0 · Φ(d_1) − K · e^{-rT} · Φ(d_2)

  where
    d_1 = (log(S_0/K) + (r + σ²/2)T) / (σ√T)
    d_2 = d_1 − σ√T = (log(S_0/K) + (r − σ²/2)T) / (σ√T)
    Φ(x) = standard normal CDF = (gaussianReal 0 1 (Set.Iic x)).toReal

  Hypothesis: under the risk-neutral measure Q, log(S_T/S_0) is Gaussian with
  mean (r − σ²/2)T and variance σ²T.

  No upstream BS or Itô calculus required; this is pure Gaussian integration.

  Mathlib leverage: `gaussianReal`, `gaussianPDFReal`,
  `gaussianReal_map_const_mul`, `gaussianReal_map_add_const`,
  `gaussianReal_map_neg`, `integral_gaussianReal_eq_integral_smul`,
  `integral_map`, `MeasureTheory.HasLaw`, `MeasureTheory.NoAtoms`.

  ## Current status

  Built primitives (this file):
  - `Phi`, `Phi_neg`, `Phi_add_Phi_neg`: standard normal CDF + symmetry.
  - `gaussianReal_Ioi_toReal`: `(gaussianReal 0 1 (Set.Ioi a)).toReal = Phi(-a)`.
  - `exp_mul_gaussianPDFReal_zero_one`: completing-the-square identity
    `exp(c·z) · pdf(0,1,z) = exp(c²/2) · pdf(c,1,z)`.
  - `integral_exp_mul_gaussianPDFReal_Ioi`: the **core BS computational primitive**
    `∫ z in Ioi a, exp(c·z) · pdf(0,1,z) dz = exp(c²/2) · Phi(c − a)`.

  Pending (planned for a follow-on session, ~100-150 lines):
  - `BSCallHyp` structure bundling: `S_0 > 0`, `K > 0`, `σ > 0`, `T > 0`,
    `HasLaw Z (gaussianReal 0 1) Q`.
  - `bsd1`, `bsd2`, `terminalPrice` definitions.
  - `bs_call_formula` main theorem: assembles the existing primitives via
    `HasLaw.integral_comp` (transfer ∫ω → ∫_gaussianReal),
    `integral_gaussianReal_eq_integral_smul` (gaussian integral → pdf form),
    region identification `{z : S_T(z) > K} = Set.Ioi (-d_2)`,
    `setIntegral_indicator` split, `integral_exp_mul_gaussianPDFReal_Ioi`
    for the S_0 term, `gaussianReal_Ioi_toReal` for the K term, and the
    final algebraic identity `(r - σ²/2)T + σ²T/2 = rT`.
-/
import Mathlib

namespace HybridVerify

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-! ### Standard normal CDF -/

/-- The standard normal cumulative distribution function `Φ(x) = P(Z ≤ x)`
where `Z ~ N(0, 1)`. -/
noncomputable def Phi (x : ℝ) : ℝ :=
  (gaussianReal 0 1 (Set.Iic x)).toReal

lemma Phi_def (x : ℝ) : Phi x = (gaussianReal 0 1 (Set.Iic x)).toReal := rfl

lemma Phi_nonneg (x : ℝ) : 0 ≤ Phi x := ENNReal.toReal_nonneg

lemma Phi_eq_integral (x : ℝ) :
    Phi x = ∫ z in Set.Iic x, gaussianPDFReal 0 1 z := by
  have h1 : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [Phi_def, gaussianReal_apply_eq_integral _ h1]
  exact ENNReal.toReal_ofReal <| setIntegral_nonneg measurableSet_Iic
    (fun _ _ => gaussianPDFReal_nonneg _ _ _)

/-- `Φ(-x) = 1 − Φ(x)`. Symmetry of the standard normal around 0. -/
lemma Phi_neg (x : ℝ) : Phi (-x) = 1 - Phi x := by
  -- Standard normal is symmetric: gaussianReal 0 1 is invariant under negation
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun y => -y) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  -- Iic(-x) under negation pulls back to Ici x
  have h_preimage : (fun y : ℝ => -y) ⁻¹' Set.Iic (-x) = Set.Ici x := by
    ext y; simp [Set.mem_Ici]
  -- gaussianReal 0 1 (Iic(-x)) = gaussianReal 0 1 (Ici x)
  have h_eq : gaussianReal (0 : ℝ) 1 (Set.Iic (-x)) = gaussianReal 0 1 (Set.Ici x) := by
    conv_lhs => rw [← hmap]
    rw [Measure.map_apply measurable_neg measurableSet_Iic, h_preimage]
  -- Ici x and Iio x partition univ; under NoAtoms, Q(Iio x) = Q(Iic x)
  have h_one_nz : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  haveI : NoAtoms (gaussianReal (0 : ℝ) 1) := noAtoms_gaussianReal h_one_nz
  have h_iio_iic : gaussianReal (0 : ℝ) 1 (Set.Iic x) = gaussianReal 0 1 (Set.Iio x) := by
    have h_decomp : Set.Iic x = Set.Iio x ∪ {x} := by
      ext y; simp [Set.mem_Iic, le_iff_lt_or_eq, eq_comm]
    have h_disj : Disjoint (Set.Iio x) ({x} : Set ℝ) :=
      Set.disjoint_singleton_right.mpr (lt_irrefl x)
    rw [h_decomp, measure_union h_disj (measurableSet_singleton _),
        measure_singleton, add_zero]
  have h_total : gaussianReal (0 : ℝ) 1 (Set.Iio x) + gaussianReal 0 1 (Set.Ici x)
      = 1 := by
    rw [← measure_union (Set.Iio_disjoint_Ici le_rfl) measurableSet_Ici,
        Set.Iio_union_Ici, measure_univ]
  -- gaussianReal 0 1 (Iic(-x)) = gaussianReal 0 1 (Ici x) = 1 - gaussianReal 0 1 (Iic x)
  rw [Phi_def, h_eq, Phi_def]
  have h_iic_finite : gaussianReal (0 : ℝ) 1 (Set.Iic x) ≠ ⊤ := (measure_lt_top _ _).ne
  have h_sum : gaussianReal (0 : ℝ) 1 (Set.Iic x) + gaussianReal 0 1 (Set.Ici x) = 1 := by
    rw [h_iio_iic]; exact h_total
  have h_eq_sub : gaussianReal (0 : ℝ) 1 (Set.Ici x) = 1 - gaussianReal 0 1 (Set.Iic x) := by
    refine ENNReal.eq_sub_of_add_eq h_iic_finite ?_
    rw [add_comm]; exact h_sum
  rw [h_eq_sub, ENNReal.toReal_sub_of_le (by
        rw [show (1 : ℝ≥0∞) = gaussianReal (0 : ℝ) 1 Set.univ from measure_univ.symm]
        exact measure_mono (Set.subset_univ _)) (by simp)]
  rfl

/-- `Φ(x) + Φ(-x) = 1`. -/
lemma Phi_add_Phi_neg (x : ℝ) : Phi x + Phi (-x) = 1 := by
  rw [Phi_neg]; ring

/-! ### Completing the square -/

/-! ### Tail probabilities of the standard normal -/

/-- `Q(Ioi a) = 1 − Φ(a) = Φ(-a)`. The right tail of the standard normal. -/
lemma gaussianReal_Ioi_toReal (a : ℝ) :
    (gaussianReal 0 1 (Set.Ioi a)).toReal = Phi (-a) := by
  have h_compl : Set.Ioi a = (Set.Iic a)ᶜ := by ext y; simp
  rw [h_compl, prob_compl_eq_one_sub measurableSet_Iic]
  rw [ENNReal.toReal_sub_of_le (by
        rw [show (1 : ℝ≥0∞) = gaussianReal (0 : ℝ) 1 Set.univ from measure_univ.symm]
        exact measure_mono (Set.subset_univ _)) (by simp)]
  rw [Phi_neg, ENNReal.toReal_one, Phi_def]

/-! ### Completing the square -/

/-- The exponential shift identity: `exp(c·z) · gaussianPDFReal 0 1 z =
exp(c²/2) · gaussianPDFReal c 1 z`. This is the algebraic content of
"completing the square" `c·z − z²/2 = c²/2 − (z − c)²/2`. -/
lemma exp_mul_gaussianPDFReal_zero_one (c z : ℝ) :
    Real.exp (c * z) * gaussianPDFReal 0 1 z =
      Real.exp (c^2 / 2) * gaussianPDFReal c 1 z := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one]
  have key : c * z + -(z - 0)^2 / 2 = c^2 / 2 + -(z - c)^2 / 2 := by ring
  set P : ℝ := (Real.sqrt (2 * π))⁻¹ with P_def
  calc Real.exp (c * z) * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-(z - 0)^2 / 2))
      = P * (Real.exp (c * z) * Real.exp (-(z - 0)^2 / 2)) := by rw [P_def]; ring
    _ = P * Real.exp (c * z + -(z - 0)^2 / 2) := by rw [Real.exp_add]
    _ = P * Real.exp (c^2 / 2 + -(z - c)^2 / 2) := by rw [key]
    _ = P * (Real.exp (c^2 / 2) * Real.exp (-(z - c)^2 / 2)) := by rw [Real.exp_add]
    _ = Real.exp (c^2 / 2) * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-(z - c)^2 / 2)) := by
        rw [P_def]; ring

/-- The shifted Gaussian tail integral — the core BS computational primitive:
  `∫ z in Ioi a, exp(c·z) · gaussianPDFReal 0 1 z dz = exp(c²/2) · Φ(c − a)`.

Combines `exp_mul_gaussianPDFReal_zero_one` (algebraic completing-the-square)
with `gaussianReal_map_add_const` (push forward via shift). -/
lemma integral_exp_mul_gaussianPDFReal_Ioi (a c : ℝ) :
    ∫ z in Set.Ioi a, Real.exp (c * z) * gaussianPDFReal 0 1 z
      = Real.exp (c^2 / 2) * Phi (c - a) := by
  rw [setIntegral_congr_fun measurableSet_Ioi
        (fun z _ => exp_mul_gaussianPDFReal_zero_one c z), integral_const_mul]
  congr 1
  have h_int_eq : ∫ z in Set.Ioi a, gaussianPDFReal c 1 z
      = (gaussianReal c (1 : ℝ≥0) (Set.Ioi a)).toReal := by
    rw [gaussianReal_apply_eq_integral c (one_ne_zero : (1 : ℝ≥0) ≠ 0) (Set.Ioi a)]
    exact (ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi
      (fun _ _ => gaussianPDFReal_nonneg _ _ _))).symm
  have h_shift : gaussianReal c (1 : ℝ≥0) (Set.Ioi a) =
                 gaussianReal 0 1 (Set.Ioi (a - c)) := by
    have hmap : (gaussianReal (0 : ℝ) 1).map (fun y => y + c) = gaussianReal c 1 := by
      rw [gaussianReal_map_add_const, zero_add]
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Ioi]
    congr 1; ext y; simp [Set.mem_Ioi, sub_lt_iff_lt_add, add_comm]
  rw [h_int_eq, h_shift, gaussianReal_Ioi_toReal, neg_sub]

/-! ### Risk-neutral lognormal hypothesis -/

/-- The risk-neutral lognormal hypothesis for the Black-Scholes model.
Under the risk-neutral measure `Q`, `S_T = S_0 · exp((r − σ²/2)T + σ√T · Z)`
with `Z ~ N(0, 1)`. -/
structure BSCallHyp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (S_0 K r σ T : ℝ) (Z : Ω → ℝ) : Prop where
  S_0_pos : 0 < S_0
  K_pos : 0 < K
  σ_pos : 0 < σ
  T_pos : 0 < T
  Z_law : HasLaw Z (gaussianReal 0 1) Q

/-- `d₁` parameter in the BS formula. -/
noncomputable def bsd1 (S_0 K r σ T : ℝ) : ℝ :=
  (Real.log (S_0 / K) + (r + σ^2 / 2) * T) / (σ * Real.sqrt T)

/-- `d₂ = d₁ − σ√T`. -/
noncomputable def bsd2 (S_0 K r σ T : ℝ) : ℝ :=
  bsd1 S_0 K r σ T - σ * Real.sqrt T

/-- Terminal price `S_T(z) = S_0 · exp((r − σ²/2)T + σ√T · z)` viewed as a
function of the standard-normal sample. -/
noncomputable def bsTerminal (S_0 r σ T z : ℝ) : ℝ :=
  S_0 * Real.exp ((r - σ^2 / 2) * T + σ * Real.sqrt T * z)

/-- Alternative form for `d₂`: `bsd2 = (log(S_0/K) + (r − σ²/2)T) / (σ√T)`. -/
private lemma bsd2_eq {S_0 K r σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    bsd2 S_0 K r σ T = (Real.log (S_0 / K) + (r - σ^2 / 2) * T) / (σ * Real.sqrt T) := by
  have hσsqT_pos : 0 < σ * Real.sqrt T := mul_pos hσ (Real.sqrt_pos.mpr hT)
  have h_sqT_sq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  unfold bsd2 bsd1
  field_simp
  nlinarith [h_sqT_sq, sq_nonneg (σ * Real.sqrt T)]

/-- Exercise-region identification: `S_T(z) > K ↔ z > −d_2`. -/
private lemma bsTerminal_gt_K_iff {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (z : ℝ) :
    bsTerminal S_0 r σ T z > K ↔ z > -bsd2 S_0 K r σ T := by
  have hσsqT_pos : 0 < σ * Real.sqrt T := mul_pos hσ (Real.sqrt_pos.mpr hT)
  have h_KS_pos : 0 < K / S_0 := div_pos hK hS_0
  have h_log_div : Real.log (K / S_0) = -Real.log (S_0 / K) := by
    rw [Real.log_div hK.ne' hS_0.ne', Real.log_div hS_0.ne' hK.ne']; ring
  -- core: S_T(z) > K ↔ log(K/S_0) < (r - σ²/2)T + σ√T·z
  have h_core_iff : bsTerminal S_0 r σ T z > K ↔
      Real.log (K / S_0) < (r - σ^2 / 2) * T + σ * Real.sqrt T * z := by
    unfold bsTerminal
    rw [gt_iff_lt, mul_comm S_0, ← div_lt_iff₀ hS_0]
    exact (Real.log_lt_iff_lt_exp h_KS_pos).symm
  rw [h_core_iff, bsd2_eq hσ hT, gt_iff_lt]
  rw [show -((Real.log (S_0 / K) + (r - σ^2 / 2) * T) / (σ * Real.sqrt T))
        = (-(Real.log (S_0 / K) + (r - σ^2 / 2) * T)) / (σ * Real.sqrt T) from
      (neg_div _ _).symm]
  rw [div_lt_iff₀ hσsqT_pos]
  rw [h_log_div]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- `max(S_T(z) − K, 0)` as an indicator on the exercise region. -/
private lemma max_payoff_eq_indicator {S_0 K r σ T : ℝ}
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) (z : ℝ) :
    max (bsTerminal S_0 r σ T z - K) 0 =
      (Set.Ioi (-bsd2 S_0 K r σ T)).indicator
        (fun z' => bsTerminal S_0 r σ T z' - K) z := by
  by_cases h : z ∈ Set.Ioi (-bsd2 S_0 K r σ T)
  · rw [Set.indicator_of_mem h]
    have hST : bsTerminal S_0 r σ T z > K :=
      (bsTerminal_gt_K_iff hS_0 hK hσ hT z).mpr h
    exact max_eq_left (sub_nonneg.mpr hST.le)
  · rw [Set.indicator_of_notMem h]
    have hz_le : z ≤ -bsd2 S_0 K r σ T := not_lt.mp h
    have hST_le : bsTerminal S_0 r σ T z ≤ K := by
      by_contra hcontra
      exact h ((bsTerminal_gt_K_iff hS_0 hK hσ hT z).mp (not_le.mp hcontra))
    exact max_eq_right (sub_nonpos.mpr hST_le)

end HybridVerify
