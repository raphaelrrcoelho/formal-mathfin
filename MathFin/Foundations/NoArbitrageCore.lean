/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# No-arbitrage core: a nonnegative zero-mean payoff vanishes

The shared analytic heart of the forward FTAP, discrete and continuous alike. A `Q`-integrable
`f` that is `Q`-a.s. nonnegative with `∫ f dQ = 0` is `Q`-a.s. zero, so its positive set is
`Q`-null (`ae_zero_of_nonneg_of_integral_zero`). Each forward-FTAP setting supplies the
zero-integral its own way: the discrete `FTAP.emm_implies_no_arbitrage` gets it from a
martingale transform started at `0` (`martingale_nonneg_terminal_ae_zero`, below), while the
continuous `ContinuousMarket.isEMM_noArbitrageSimple` gets it term-by-term from the pull-out
property. Both then close through `ae_zero_of_nonneg_of_integral_zero`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

/-- **A nonnegative payoff with zero mean vanishes a.s.** If `f` is `Q`-integrable, `Q`-a.s.
nonnegative, and has `∫ f dQ = 0`, then `{f > 0}` is `Q`-null. The common closing step of the
forward FTAP in every setting. -/
theorem ae_zero_of_nonneg_of_integral_zero
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {f : Ω → ℝ}
    (hf_int : Integrable f Q) (hf_nonneg : 0 ≤ᵐ[Q] f) (hf0 : ∫ ω, f ω ∂Q = 0) :
    Q {ω | 0 < f ω} = 0 := by
  have hf_zero : f =ᵐ[Q] 0 := (integral_eq_zero_iff_of_nonneg_ae hf_nonneg hf_int).mp hf0
  exact measure_mono_null (fun ω hω ↦ ne_of_gt hω) (ae_iff.mp hf_zero)

/-- **A nonnegative martingale started at `0` vanishes at the terminal time.** The discrete
forward FTAP's route to zero mean: `∫ V_T dQ = ∫ V_0 dQ = 0`, then
`ae_zero_of_nonneg_of_integral_zero`. -/
theorem martingale_nonneg_terminal_ae_zero
    {Ω : Type*} [m0 : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓕 : Filtration ℕ m0} {V : ℕ → Ω → ℝ}
    (hV : Martingale V 𝓕 Q) (hV0 : V 0 = 0) {T : ℕ} (hVT : 0 ≤ᵐ[Q] V T) :
    Q {ω | 0 < V T ω} = 0 := by
  have hVT_int : ∫ ω, V T ω ∂Q = 0 := by
    have : ∫ ω, V T ω ∂Q = ∫ ω, V 0 ω ∂Q := by
      rw [(integral_condExp (𝓕.le 0)).symm]
      exact integral_congr_ae (hV.condExp_ae_eq (Nat.zero_le T))
    rw [this, hV0]; simp
  exact ae_zero_of_nonneg_of_integral_zero (hV.integrable T) hVT hVT_int

end MathFin
