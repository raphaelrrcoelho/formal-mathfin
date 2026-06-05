/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.BrownianMartingale

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

end MathFin
