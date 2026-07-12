/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# No-arbitrage core: a nonnegative martingale from 0 vanishes at the terminal time

The shared analytic heart of the forward FTAP, discrete and continuous alike: a
`Q`-martingale `V` started at `0` that is `Q`-a.s. nonnegative at time `T` is in fact
`Q`-a.s. zero there (its terminal integral is `E_Q[V_0] = 0`, and a nonnegative integrand
with zero integral vanishes a.e.). Both `FTAP.emm_implies_no_arbitrage` (discrete) and
`ContinuousMarket.isEMM_noArbitrageSimple` (continuous, after time-sampling) consume this.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

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
  have hVT_zero : V T =ᵐ[Q] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hVT (hV.integrable T)).mp hVT_int
  exact measure_mono_null (fun ω hω ↦ ne_of_gt hω) (ae_iff.mp hVT_zero)

end MathFin
