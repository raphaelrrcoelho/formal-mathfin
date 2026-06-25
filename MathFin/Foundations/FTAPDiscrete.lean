/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.ConvexSeparation
public import MathFin.Foundations.MartingaleTransform

/-!
# Discrete-time FTAP on a finite probability space (scalar, finite horizon)

The finite-Ω, finite-horizon, single-asset **Fundamental Theorem of Asset
Pricing** (Harrison–Pliska / the finite case of Dalang–Morton–Willinger): a
market has **no arbitrage** iff it admits an **equivalent martingale measure**.

The discounted price `S : ℕ → Ω → ℝ` is adapted to a filtration `𝓕` on a finite
probability space `(Ω, P)` with full support; a trading strategy `φ` is
predictable (`φ (n+1)` is `𝓕 n`-measurable) and its discounted gains are the
martingale transform `martingaleTransform φ S`.

The backward direction is the geometric heart of the theorem: the attainable
gains span a subspace of `Ω → ℝ` that, under no arbitrage, misses the standard
simplex, so the separating-dual kernel `exists_pos_dual_of_disjoint_stdSimplex`
(`Foundations/ConvexSeparation.lean`) produces a strictly-positive pricing
functional — the EMM. The forward direction is martingale-transform telescoping.

## Scope

Finite Ω, one scalar discounted asset, finite horizon `T`. The general-Ω DMW
theorem (which needs L⁰-closedness under no arbitrage and measurable selection)
and the `d`-asset generalisation are out of scope here.

## Main definitions / results (assembled across this file)

* `MathFin.NoArbitrage`, `MathFin.IsEMM`
* `MathFin.ftap_discrete` — the biconditional `NoArbitrage ↔ ∃ Q, IsEMM Q`
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- The lemmas below intentionally share one rich `variable` context; individual
-- lemmas use different subsets, so silence the unused-section-variable linter.
set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {mΩ : MeasurableSpace Ω}
  [MeasurableSingletonClass Ω] (𝓕 : Filtration ℕ mΩ)
  (P : Measure Ω) [IsProbabilityMeasure P] (S : ℕ → Ω → ℝ) (T : ℕ)

/-- **No arbitrage**: no predictable strategy turns zero initial wealth into a
sure non-loss (`0 ≤ᵐ[P]` discounted gains) with a positive chance of gain. On a
full-support finite space the `ᵐ[P]` form coincides with the pointwise one. -/
def NoArbitrage : Prop :=
  ∀ φ : ℕ → Ω → ℝ, StronglyAdapted 𝓕 (fun n => φ (n + 1)) →
    0 ≤ᵐ[P] martingaleTransform φ S T → martingaleTransform φ S T =ᵐ[P] 0

/-- **Equivalent martingale measure** for the finite horizon. The martingale
property is the one-step form up to `T` (the honest finite-horizon object: `S`
need not be a `Q`-martingale past the horizon). -/
structure IsEMM (Q : Measure Ω) : Prop where
  prob : IsProbabilityMeasure Q
  absP : Q ≪ P
  Pabs : P ≪ Q
  mart : ∀ t, t < T → S t =ᵐ[Q] Q[S (t + 1) | 𝓕 t]

/-- `𝟙_A · (S_{t+1} − S_t)` — the discounted gain of holding one unit on the
event `A` over period `t+1`. -/
noncomputable def incrementIndicator (t : ℕ) (A : Set Ω) : Ω → ℝ :=
  fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (S (t + 1) ω - S t ω)

/-- The **attainable-gains subspace**: the span of the single-period
increment-indicators `𝟙_A · (S_{t+1} − S_t)` over `t < T` and `𝓕_t`-measurable
events `A`. Every element is the discounted gains of some predictable strategy
(see `mem_gains_imp_predictable`). -/
noncomputable def gainsSubspace : Submodule ℝ (Ω → ℝ) :=
  Submodule.span ℝ
    { g | ∃ t, t < T ∧ ∃ A : Set Ω, MeasurableSet[𝓕 t] A ∧ g = incrementIndicator S t A }

/-- The martingale transform is additive in the strategy. -/
private lemma martingaleTransform_add (φ ψ : ℕ → Ω → ℝ) (n : ℕ) :
    martingaleTransform (φ + ψ) S n
      = martingaleTransform φ S n + martingaleTransform ψ S n := by
  funext ω
  simp only [martingaleTransform, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The martingale transform is homogeneous in the strategy. -/
private lemma martingaleTransform_smul (c : ℝ) (φ : ℕ → Ω → ℝ) (n : ℕ) :
    martingaleTransform (c • φ) S n = c • martingaleTransform φ S n := by
  funext ω
  simp only [martingaleTransform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Every element of the attainable-gains subspace is the discounted gains of a
predictable strategy. (`span`-induction: the generators are the gains of the
single-period indicator strategies, and predictable gains are closed under the
vector-space operations.) -/
theorem mem_gains_imp_predictable {g : Ω → ℝ} (hg : g ∈ gainsSubspace 𝓕 S T) :
    ∃ φ : ℕ → Ω → ℝ,
      StronglyAdapted 𝓕 (fun n => φ (n + 1)) ∧ martingaleTransform φ S T = g := by
  classical
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, htT, A, hA, rfl⟩ := hx
    refine ⟨fun s => if s = t + 1 then A.indicator (fun _ => (1 : ℝ)) else 0, ?_, ?_⟩
    · intro n
      dsimp only
      split_ifs with h
      · have hnt : n = t := by omega
        subst hnt
        exact stronglyMeasurable_const.indicator hA
      · exact stronglyMeasurable_const
    · funext ω
      simp only [martingaleTransform]
      rw [Finset.sum_eq_single t]
      · simp [incrementIndicator]
      · intro k _ hk
        rw [if_neg (by omega : ¬ k + 1 = t + 1)]
        simp
      · intro ht
        exact absurd (Finset.mem_range.mpr htT) ht
  | zero => exact ⟨0, fun _ => stronglyMeasurable_const, by funext ω; simp [martingaleTransform]⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨φ, hφ, hφeq⟩ := ihx
    obtain ⟨ψ, hψ, hψeq⟩ := ihy
    exact ⟨φ + ψ, fun n => (hφ n).add (hψ n),
      by rw [martingaleTransform_add, hφeq, hψeq]⟩
  | smul c x _ ih =>
    obtain ⟨φ, hφ, hφeq⟩ := ih
    exact ⟨c • φ, fun n => (hφ n).const_smul c, by rw [martingaleTransform_smul, hφeq]⟩

/-- Under no arbitrage, the attainable-gains subspace is disjoint from the
standard simplex: a non-negative, non-zero gains vector would be an arbitrage. -/
theorem gains_disjoint_stdSimplex (hP : ∀ ω, 0 < P {ω}) (hNA : NoArbitrage 𝓕 P S T) :
    ∀ v ∈ gainsSubspace 𝓕 S T, v ∉ stdSimplex ℝ Ω := by
  intro v hv hsimplex
  obtain ⟨φ, hφ, hφeq⟩ := mem_gains_imp_predictable 𝓕 S T hv
  -- The gains are `≥ 0` (`v` is in the simplex), so no arbitrage forces them `= 0`.
  have hge : 0 ≤ᵐ[P] martingaleTransform φ S T := by
    rw [hφeq]; exact Filter.Eventually.of_forall fun ω => hsimplex.1 ω
  have hzero : v =ᵐ[P] 0 := by rw [← hφeq]; exact hNA φ hφ hge
  -- But `∑ v = 1`, so some `v ω₀ > 0`, contradicting `v = 0` a.e. on full support.
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀, 0 < v ω₀ := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hle : ∑ ω, v ω ≤ 0 := Finset.sum_nonpos fun ω _ => hcon ω
    rw [hsimplex.2] at hle; linarith
  have hnull : P {ω | v ω ≠ 0} = 0 := by simpa using ae_iff.mp hzero
  have hsub : ({ω₀} : Set Ω) ⊆ {ω | v ω ≠ 0} := by
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact ne_of_gt hω₀
  exact absurd (hnull ▸ measure_mono hsub : P {ω₀} ≤ 0) (not_le.mpr (hP ω₀))

/-- **Backward direction**: no arbitrage ⟹ an equivalent martingale measure
exists. The separating-dual `q` of the gains subspace, normalised to a
probability `Q`, is the EMM: strict positivity gives `Q ~ P`, and the
annihilation of every increment-indicator gives the martingale property via the
conditional-expectation characterisation. -/
theorem exists_isEMM_of_noArbitrage (hS : StronglyAdapted 𝓕 S)
    (hP : ∀ ω, 0 < P {ω}) (hNA : NoArbitrage 𝓕 P S T) :
    ∃ Q, IsEMM 𝓕 P S T Q := by
  classical
  obtain ⟨q, hq_pos, hq_dual⟩ :=
    exists_pos_dual_of_disjoint_stdSimplex (gainsSubspace 𝓕 S T)
      (gains_disjoint_stdSimplex 𝓕 P S T hP hNA)
  set Z : ℝ := ∑ ω, q ω with hZ
  have hZpos : 0 < Z := Finset.sum_pos (fun ω _ => hq_pos ω) Finset.univ_nonempty
  have hmnn : ∀ ω, (0 : ℝ) ≤ q ω / Z := fun ω => (div_pos (hq_pos ω) hZpos).le
  have hsum1 : ∑ ω, ENNReal.ofReal (q ω / Z) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => hmnn ω), ← Finset.sum_div, ← hZ,
      div_self hZpos.ne', ENNReal.ofReal_one]
  set Q : Measure Ω := (PMF.ofFintype (fun ω => ENNReal.ofReal (q ω / Z)) hsum1).toMeasure
    with hQdef
  haveI hQprob : IsProbabilityMeasure Q := by rw [hQdef]; infer_instance
  have hQsingle : ∀ ω, Q {ω} = ENNReal.ofReal (q ω / Z) := fun ω => by
    rw [hQdef, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton ω), PMF.ofFintype_apply]
  have hQpos : ∀ ω, 0 < Q {ω} := fun ω => by
    rw [hQsingle ω]; exact ENNReal.ofReal_pos.mpr (div_pos (hq_pos ω) hZpos)
  have hQint : ∀ h : Ω → ℝ, ∫ ω, h ω ∂Q = ∑ ω, (q ω / Z) * h ω := by
    intro h
    rw [hQdef, PMF.integral_eq_sum]
    exact Finset.sum_congr rfl fun ω _ => by
      rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hmnn ω), smul_eq_mul]
  -- Both `P` and `Q` have full support, so a null set is empty: they are equivalent.
  have hnull : ∀ (μ : Measure Ω), (∀ ω, 0 < μ {ω}) → ∀ s : Set Ω, μ s = 0 → s = ∅ := by
    intro μ hμ s hs
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨ω, hω⟩
    have hle : μ {ω} ≤ 0 := hs ▸ measure_mono (Set.singleton_subset_iff.mpr hω)
    exact absurd hle (not_le.mpr (hμ ω))
  have hQP : Q ≪ P := by intro s hs; rw [hnull P hP s hs]; exact measure_empty
  have hPQ : P ≪ Q := by intro s hs; rw [hnull Q hQpos s hs]; exact measure_empty
  refine ⟨Q, hQprob, hQP, hPQ, fun t htT => ?_⟩
  -- Martingale property via the conditional-expectation characterisation.
  refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le t) Integrable.of_finite
    (fun s _ _ => Integrable.of_finite.integrableOn) (fun s hs _ => ?_)
    (hS t).aestronglyMeasurable
  -- Key: `∫_s (S_{t+1} − S_t) dQ = 0` because the increment-indicator is annihilated.
  have hsm : MeasurableSet s := 𝓕.le t s hs
  have hinc_eq : s.indicator (fun ω => S (t + 1) ω - S t ω) = incrementIndicator S t s := by
    funext ω; simp only [incrementIndicator, Set.indicator_apply]; split_ifs <;> ring
  have hkey : ∫ ω, s.indicator (fun ω => S (t + 1) ω - S t ω) ω ∂Q = 0 := by
    rw [hinc_eq, hQint]
    have hdual := hq_dual (incrementIndicator S t s)
      (Submodule.subset_span ⟨t, htT, s, hs, rfl⟩)
    calc ∑ ω, (q ω / Z) * incrementIndicator S t s ω
        = (∑ ω, q ω * incrementIndicator S t s ω) / Z := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl fun ω _ => by ring
      _ = 0 := by rw [hdual, zero_div]
  rw [integral_indicator hsm,
    integral_sub Integrable.of_finite.integrableOn Integrable.of_finite.integrableOn] at hkey
  linarith [hkey]

/-- **Forward direction**: an equivalent martingale measure precludes arbitrage.
Under the EMM `Q`, the discounted gains telescope to `∫ G_T dQ = 0`; a
non-negative integrand with zero integral is `0` a.e., and equivalence transports
this back to `P`. -/
theorem noArbitrage_of_isEMM (hS : StronglyAdapted 𝓕 S)
    {Q : Measure Ω} (hQ : IsEMM 𝓕 P S T Q) : NoArbitrage 𝓕 P S T := by
  haveI := hQ.prob
  intro φ hφ hpos
  -- Each one-step gain integrates to zero under `Q` (the pull-out + martingale step).
  have hstep : ∀ k, k < T → ∫ ω, (φ (k + 1) * (S (k + 1) - S k)) ω ∂Q = 0 := by
    intro k hk
    have hcondS : Q[S (k + 1) - S k | 𝓕 k] =ᵐ[Q] 0 := by
      have h1 := condExp_sub (μ := Q) (Integrable.of_finite (f := S (k + 1)))
        (Integrable.of_finite (f := S k)) (𝓕 k)
      have h2 : Q[S (k + 1) | 𝓕 k] =ᵐ[Q] S k := (hQ.mart k hk).symm
      have h3 : Q[S k | 𝓕 k] = S k :=
        condExp_of_stronglyMeasurable (𝓕.le k) (hS k) (Integrable.of_finite (μ := Q))
      filter_upwards [h1, h2] with ω e1 e2
      rw [Pi.zero_apply, e1, Pi.sub_apply, e2, congrFun h3 ω, sub_self]
    have hpull0 : Q[φ (k + 1) * (S (k + 1) - S k) | 𝓕 k] =ᵐ[Q] 0 := by
      have hpull := condExp_mul_of_stronglyMeasurable_left (μ := Q) (m := 𝓕 k)
        (f := φ (k + 1)) (g := S (k + 1) - S k) (hφ k) Integrable.of_finite Integrable.of_finite
      filter_upwards [hpull, hcondS] with ω ep ec
      rw [Pi.zero_apply] at ec ⊢
      rw [ep, Pi.mul_apply, ec, mul_zero]
    rw [← integral_condExp (𝓕.le k), integral_congr_ae hpull0]; simp
  -- Sum the steps: `∫ G_T dQ = 0`.
  have hGint : ∫ ω, martingaleTransform φ S T ω ∂Q = 0 := by
    have hsplit : ∀ ω, martingaleTransform φ S T ω
        = ∑ k ∈ Finset.range T, φ (k + 1) ω * (S (k + 1) ω - S k ω) := fun ω => by
      rw [martingaleTransform]
    simp_rw [hsplit]
    rw [integral_finsetSum _ (fun k _ => Integrable.of_finite)]
    exact Finset.sum_eq_zero fun k hk => hstep k (Finset.mem_range.mp hk)
  -- `G_T ≥ 0` `Q`-a.e. (equivalence) and `∫ G_T = 0` give `G_T = 0` a.e.
  have hposQ : 0 ≤ᵐ[Q] martingaleTransform φ S T := hQ.absP.ae_le hpos
  have hzeroQ : martingaleTransform φ S T =ᵐ[Q] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hposQ Integrable.of_finite).mp hGint
  exact hQ.Pabs.ae_eq hzeroQ

/-- **Finite-Ω Fundamental Theorem of Asset Pricing** (Harrison–Pliska; the
finite case of Dalang–Morton–Willinger): a finite-horizon, single-asset market
on a finite full-support probability space has no arbitrage **iff** it admits an
equivalent martingale measure. -/
theorem ftap_discrete (hS : StronglyAdapted 𝓕 S) (hP : ∀ ω, 0 < P {ω}) :
    NoArbitrage 𝓕 P S T ↔ ∃ Q, IsEMM 𝓕 P S T Q :=
  ⟨fun hNA => exists_isEMM_of_noArbitrage 𝓕 P S T hS hP hNA,
   fun ⟨_, hQ⟩ => noArbitrage_of_isEMM 𝓕 P S T hS hQ⟩

end MathFin
