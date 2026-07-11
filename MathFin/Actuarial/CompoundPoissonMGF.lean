/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.PoissonPgf

/-!
# The compound-Poisson aggregate-loss MGF

For a Poisson claim count `N ∼ Poisson(λ)` and i.i.d. claim sizes `Xᵢ` with common moment
generating function `M_X(t)`, the compound-Poisson aggregate loss `S = ∑_{i<N} Xᵢ` has MGF

  `𝔼[exp(tS)] = exp(λ·(M_X(t) − 1))`.

This composes two genuine theorems rather than positing the algebraic shell
`e^{−λ}·e^{λM} = e^{λ(M−1)}` (`Actuarial/Mortality.compoundPoisson_mgf_identity`):

* the **`n`-claim aggregate MGF** `𝔼[exp(t·∑_{i<n} Xᵢ)] = M_X(t)ⁿ` — the MGF of a sum of
  i.i.d. summands is the `n`-th power of the common MGF (Mathlib's `iIndepFun.mgf_sum`
  factorisation + `IdentDistrib` collapse), and
* the **Poisson probability generating function** `𝔼[xᴺ] = e^{λ(x−1)}`
  (`Foundations/PoissonPgf.integral_pow_poissonMeasure`), evaluated at `x = M_X(t)`.

Integrating the `n`-claim MGF against the Poisson claim-count law is the standard actuarial
mixed-distribution derivation `𝔼_N[𝔼_X[exp(t·S_N)]] = 𝔼[exp(tS)]` under `N ⟂ (Xᵢ)`.

## Main result

* `compoundPoisson_mgf` — `∫ n, mgf (∑_{i<n} Xᵢ) t ∂Poisson(λ) = exp(λ·(mgf X₀ t − 1))`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The `n`-claim aggregate MGF is the `n`-th power of the common claim MGF.** For i.i.d.
claim sizes `X` (independent, identically distributed), the MGF of the `n`-claim aggregate
`∑_{i<n} Xᵢ` is `M_X(t)ⁿ`. -/
lemma mgf_range_sum_of_iid (t : ℝ) (X : ℕ → Ω → ℝ)
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    mgf (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) μ t = (mgf (X 0) μ t) ^ n := by
  have hu : Measurable (fun x : ℝ ↦ Real.exp (t * x)) := by fun_prop
  have hmgf : ∀ i, mgf (X i) μ t = mgf (X 0) μ t := fun i ↦
    ((hident i).comp hu).integral_eq
  have hsum : (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) = ∑ i ∈ Finset.range n, X i := by
    funext ω; rw [Finset.sum_apply]
  rw [hsum, hindep.mgf_sum hmeas (Finset.range n),
    Finset.prod_congr rfl (fun i _ ↦ hmgf i), Finset.prod_const, Finset.card_range]

/-- **The compound-Poisson aggregate-loss MGF.** For a Poisson claim count `N ∼ Poisson(λ)`
and i.i.d. claim sizes `Xᵢ`, the aggregate loss `S = ∑_{i<N} Xᵢ` has moment generating
function `exp(λ·(M_X(t) − 1))` — the Poisson PGF evaluated at the common claim MGF. -/
theorem compoundPoisson_mgf (lam : ℝ≥0) (t : ℝ) (X : ℕ → Ω → ℝ)
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∫ n, mgf (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) μ t ∂(poissonMeasure lam)
      = Real.exp ((lam : ℝ) * (mgf (X 0) μ t - 1)) := by
  simp_rw [mgf_range_sum_of_iid t X hindep hmeas hident]
  exact PoissonPgf.integral_pow_poissonMeasure lam (mgf (X 0) μ t)

end MathFin
