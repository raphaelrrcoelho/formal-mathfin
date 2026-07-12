/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.BrownianMartingale
public import MathFin.Foundations.ContinuousMarket

/-!
# Continuous-time first fundamental theorem of asset pricing (martingale property)

Under the risk-neutral measure, the **discounted Black–Scholes price process is a
martingale** w.r.t. the Brownian filtration — the defining property of the equivalent
martingale measure (EMM), and the operational content of the first fundamental theorem
of asset pricing in continuous time. This is the continuous-time analogue of the
discrete binomial EMM (`Binomial/SecondFTAP.lean`, `Binomial/BinomialFromFTAP.lean`).

The risk-neutral geometric Brownian motion is `S_t = S_0 exp((r − σ²/2)t + σ X_t)`,
driven by a filtered pre-Brownian motion `X`. Its discounted value is

  `e^{−rt} S_t = S_0 · exp(σ X_t − σ² t / 2)`,

i.e. `S_0` times the **Wald exponential** `exp(σ X_t − σ² t / 2)`, which is a martingale
(`ProbabilityTheory.IsFilteredPreBrownian.waldExponential_isMartingale`). Hence the
discounted price is a martingale — directly, with no further stochastic-calculus
machinery.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
  [hX : IsFilteredPreBrownian X 𝓕 P] [IsFiniteMeasure P]

/-- **Continuous-time first FTAP — martingale property of the discounted price.**
For the risk-neutral geometric Brownian motion `S_t = S_0 exp((r − σ²/2)t + σ X_t)`
driven by a filtered pre-Brownian motion `X`, the discounted price process
`t ↦ e^{−rt} S_t` is a martingale w.r.t. the Brownian filtration `𝓕` under `P` — the
defining property of the equivalent martingale measure (the discounted price is a
"fair game" under the risk-neutral measure).

Immediate from the Wald exponential martingale, since `e^{−rt} S_t = S_0 · exp(σ X_t −
σ² t / 2)`. -/
theorem discountedGBM_isMartingale (S_0 r σ : ℝ) :
    Martingale (fun (t : ℝ≥0) ω ↦ Real.exp (-r * t) *
        (S_0 * Real.exp ((r - σ ^ 2 / 2) * t + σ * X t ω))) 𝓕 P := by
  have heq : (fun (t : ℝ≥0) ω ↦ Real.exp (-r * t) *
        (S_0 * Real.exp ((r - σ ^ 2 / 2) * t + σ * X t ω)))
      = (S_0 • fun (t : ℝ≥0) ω ↦ Real.exp (σ * X t ω - σ ^ 2 * (t : ℝ) / 2)) := by
    funext t ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [heq]
  exact (IsFilteredPreBrownian.waldExponential_isMartingale σ).smul S_0

/-- **The discounted GBM is an equivalent martingale measure — with `Q = P`.** When `P` is the
risk-neutral measure (the driver `X` is a `P`-pre-Brownian), the discounted price `e^{−rt} S_t` is
already a `P`-martingale, so `P` is trivially its own EMM for it: an instance of the model-agnostic
`ContinuousMarket.IsEMM` frame at `F = ℝ`. (The physical-measure Girsanov EMM `Q ≠ P` is
intrinsically bounded-horizon — `Q = withDensity Z_T` is a martingale measure only on `[0,T]`, cf.
`bs_discounted_isQMartingale` — so it fits a horizon-aware EMM, tracked as follow-up, not this
full-horizon `IsEMM`.) -/
theorem discountedGBM_isEMM [IsProbabilityMeasure P] (S_0 r σ : ℝ) :
    ContinuousMarket.IsEMM (P := P) (𝓕 := 𝓕)
      (fun (t : ℝ≥0) ω ↦ Real.exp (-r * t) *
        (S_0 * Real.exp ((r - σ ^ 2 / 2) * t + σ * X t ω))) P where
  isProb := inferInstance
  ac := Measure.AbsolutelyContinuous.rfl
  ac' := Measure.AbsolutelyContinuous.rfl
  martingale := discountedGBM_isMartingale S_0 r σ

/-- **No simple-strategy arbitrage for the discounted GBM under its risk-neutral measure.** The
frame's forward FTAP (`isEMM_noArbitrageSimple`) applied to the EMM `discountedGBM_isEMM`: no simple
(piecewise-constant, predictable, bounded) strategy trading the discounted GBM has gains that are
`P`-a.s. nonnegative and strictly positive on a `P`-non-null set. -/
theorem discountedGBM_noArbitrageSimple [IsProbabilityMeasure P] (S_0 r σ : ℝ) :
    ContinuousMarket.NoArbitrageSimple (P := P) (𝓕 := 𝓕)
      (fun (t : ℝ≥0) ω ↦ Real.exp (-r * t) *
        (S_0 * Real.exp ((r - σ ^ 2 / 2) * t + σ * X t ω))) :=
  ContinuousMarket.isEMM_noArbitrageSimple (discountedGBM_isEMM S_0 r σ)

end MathFin
