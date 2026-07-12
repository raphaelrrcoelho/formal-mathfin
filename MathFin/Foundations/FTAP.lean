/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.MartingaleTransform
public import MathFin.Foundations.NoArbitrageCore

/-!
# FTAP (Theorem 2.6.7), forward (⇒) direction: EMM ⇒ no arbitrage

The abstract discrete-time **forward** direction only: existence of an
equivalent martingale measure precludes arbitrage, via the martingale-transform
argument. This is the narrowest of the FTAP files — for the *both-directions*
explicit two-state theorem (with the backward EMM construction) see
`FTAPTwoState.lean`, and for the finite-state forward direction see
`FTAPMultiState.lean`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

/-- **Theorem 2.6.7 (FTAP, ⇒ direction)**: existence of an equivalent martingale
measure precludes arbitrage.

Given a discounted-price process `S` adapted to a filtration `𝓕`, an equivalent
probability measure `Q ≪≫ P` under which `S` is a martingale, and a bounded
predictable strategy `φ`, the discounted P&L
`V_T = ∑_{t<T} φ_{t+1}(ω) · (S_{t+1} − S_t)`
cannot be `P`-a.s. nonnegative and strictly positive on a `P`-non-null set. -/
theorem emm_implies_no_arbitrage
    {Ω : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℕ} {𝓕 : Filtration ℕ m0} {S : ℕ → Ω → ℝ}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (hSQ : Martingale S 𝓕 Q)
    (φ : ℕ → Ω → ℝ)
    (hφ_pred : StronglyAdapted 𝓕 (fun n ↦ φ (n + 1)))
    (hφ_bdd : ∃ K : ℝ, ∀ n ω, |φ n ω| ≤ K)
    (hV_nonneg : ∀ᵐ ω ∂P,
      0 ≤ ∑ t ∈ Finset.range T, φ (t + 1) ω * (S (t + 1) ω - S t ω)) :
    P {ω | 0 < ∑ t ∈ Finset.range T, φ (t + 1) ω * (S (t + 1) ω - S t ω)} = 0 := by
  set V : ℕ → Ω → ℝ := martingaleTransform φ S
  have hV_mart : Martingale V 𝓕 Q := by
    obtain ⟨K, hK⟩ := hφ_bdd
    -- `martingaleTransform_isMartingale` now takes an a.e. boundedness
    -- hypothesis; our everywhere bound supplies it via `Eventually.of_forall`.
    exact martingaleTransform_isMartingale hSQ hφ_pred
      ⟨K, Filter.Eventually.of_forall fun ω n ↦ hK n ω⟩
  have hV0_zero : V 0 = 0 := by simp [V]
  exact hPQ (martingale_nonneg_terminal_ae_zero hV_mart hV0_zero (hQP.ae_le hV_nonneg))

end MathFin
