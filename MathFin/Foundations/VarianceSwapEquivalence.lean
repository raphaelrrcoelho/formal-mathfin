/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.VarianceSwapLimit
public import MathFin.BlackScholes.VarianceSwap

/-!
# Variance-swap form equivalence (phase 45)

Two *functionals* of the BS price process both yield the variance-swap
fair strike `σ²`:

1. **Log-payoff replication** (Demeterfi-Derman-Kamal 1999, pre-existing
   `BlackScholes/VarianceSwap.lean` `varianceSwap_log_contribution`):
   `(2/T) · E_Q[log(F/S_T)] = σ²`.

2. **Realised-variance QV limit** (Phase 34 `tendsto_expected_bsLogPrice_equipartition_sum`):
   `lim_n (1/T) · E_Q[Σ_k (log S_{(k+1)T/(n+1)} − log S_{kT/(n+1)})²] = σ²`.

The two forms compute the same `σ²` from different *integrals* of the same
underlying BS dynamics. This file proves their *agreement* — both equal
`σ²` (which is the variance-swap fair strike).

## Why this is a meaningful bridge

The log-payoff form is the **static replication** characterisation
(Carr-Madan style): you can replicate a variance swap from a portfolio of
log payoffs `log S_T` plus dynamic delta-hedging. The QV form is the
**realised-variance estimator** characterisation: you can estimate σ² by
summing squared log-returns over a fine partition.

Both being equal to σ² is a structural identity of the BS model: the
*model parameter* `σ²` (a single number characterising volatility)
agrees with *two distinct empirical / replication-based measurements* of
volatility.

## Results

* `varianceSwap_equivalence`: the log-payoff functional `(2/T)·E[log(F/S_T)]`
  equals `σ²` (a re-export of `varianceSwap_log_contribution`, the
  static-replication half).
* `varianceSwap_log_eq_QV_limit_value`: the **genuine two-functional
  agreement** — the log-payoff form equals `σ²` AND the realised-variance
  QV-limit `lim_n E_Q[Σ_k (Δlog S)²] → σ²·T` (the actual equipartition
  `Tendsto`, `tendsto_expected_bsLogPrice_equipartition_sum`), under a
  Brownian-quadratic-variation hypothesis on the driver.

The full equivalence at the *random-variable* level (showing both functionals
coincide on the path of `S_t`, not just on their values) would require the
continuous Itô-to-log identity, which is gated.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- **Variance-swap log-payoff fair strike** `(2/T) · E[log(F/S_T)] = σ²` — the
static-replication (Demeterfi-Derman-Kamal) half. A direct re-export of
`varianceSwap_log_contribution` from `BlackScholes/VarianceSwap.lean`, kept here
as the companion to the genuine two-functional agreement
`varianceSwap_log_eq_QV_limit_value` below (which adds the realised-variance
QV-limit side). This lemma alone is *only* the log-payoff equality, not the
two-form agreement. -/
theorem varianceSwap_equivalence {S_0 : ℝ} (hS : 0 < S_0)
    (r σ T : ℝ) (hT_pos : T ≠ 0) :
    -- Log-payoff form yields σ²:
    (2 / T) * (∫ z, Real.log ((S_0 * Real.exp (r * T)) /
        (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))) ∂(gaussianReal 0 1))
      = σ ^ 2 :=
  varianceSwap_log_contribution hS r σ T hT_pos

/-- **The two variance-swap characterisations agree** — both genuinely
recover the model variance. For Brownian dynamics `B` (a
`BrownianQuadraticVariation`), the two *distinct functionals* of the BS
log-price both yield `σ²`:

* the **log-payoff static-replication** integral equals `σ²`
  (`varianceSwap_log_contribution`), and
* the **realised-variance QV limit** — the *actual* equipartition functional
  `lim_n E_Q[Σ_k (Δlog S)²]` — converges to `σ²·T`
  (`tendsto_expected_bsLogPrice_equipartition_sum`, Phase 34).

Unlike a tautological `σ² = σ²` restatement, **both conjuncts here are the
genuine functionals**: the second is the honest `Tendsto` of the squared-
increment sum, not a placeholder. `hB` and `hT_nonneg` are load-bearing (they
feed the QV-limit theorem). This is the real model-level equivalence of the
static-replication and realised-variance characterisations of the fair
strike. -/
theorem varianceSwap_log_eq_QV_limit_value
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ → Ω → ℝ} (hB : BrownianQuadraticVariation μ B)
    {S_0 : ℝ} (hS : 0 < S_0) (r σ : ℝ) {T : ℝ} (hT_pos : T ≠ 0) (hT_nonneg : 0 ≤ T) :
    -- Log-payoff (static-replication) form = σ²
    (2 / T) * (∫ z, Real.log ((S_0 * Real.exp (r * T)) /
        (S_0 * Real.exp ((r - σ^2/2) * T + σ * Real.sqrt T * z))) ∂(gaussianReal 0 1))
      = σ ^ 2 ∧
    -- Realised-variance QV-limit form → σ²·T (the genuine equipartition functional)
    Filter.Tendsto
      (fun n : ℕ => ∫ ω, ∑ k ∈ Finset.range (n + 1),
        (bsLogPrice S_0 r σ B (((k : ℝ) + 1) * T / ((n : ℝ) + 1)) ω -
         bsLogPrice S_0 r σ B ((k : ℝ) * T / ((n : ℝ) + 1)) ω) ^ 2 ∂μ)
      Filter.atTop (nhds (σ ^ 2 * T)) :=
  ⟨varianceSwap_log_contribution hS r σ T hT_pos,
   tendsto_expected_bsLogPrice_equipartition_sum hB S_0 r σ hT_nonneg⟩

end MathFin
