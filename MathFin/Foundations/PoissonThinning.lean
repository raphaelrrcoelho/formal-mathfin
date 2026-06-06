/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# Thinning (splitting) of a Poisson count: the binomial-marking factorisation

Saporito, Theorem 3.3.10: mark each event of a `Poisson(r)` count
independently as type 1 with probability `p`, type 2 with probability `1 − p`.
Then the two type counts are **independent** Poissons with rates `p·r` and
`(1−p)·r`. The surprise is the conclusion — independence plus the thinned
marginal laws — and none of it is in Mathlib.

The textbook marking mechanism says: the joint pmf of the pair
`(type-1 count, type-2 count)` at `(j, k)` is

  `P(N = j+k) · C(j+k, j) pʲ (1−p)ᵏ  =  e^{−r} r^{j+k}/(j+k)! · C(j+k,j) pʲ (1−p)ᵏ`

(a Poisson count split by a conditional Binomial). This file takes exactly
that marking law as the hypothesis and **derives** the theorem: the marked
joint measure *is* the product `Poisson(p·r) × Poisson((1−p)·r)`. The heart is
the pointwise factorisation `C(j+k,j)/(j+k)! = 1/(j!·k!)` together with
`e^{−r} = e^{−p·r}·e^{−(1−p)·r}` — after which marginals fall out by
projection and independence by the joint-law-equals-product-law criterion.

## Main results

* `PoissonThinning.markedPoissonMeasure_eq_prod` — the marked joint measure
  factorises as `Poisson(p·r) ×ₘ Poisson((1−p)·r)`.
* `PoissonThinning.thinned_streams` — for counts `M, K` whose joint law is the
  binomial marking of `Poisson(r)`: `M ∼ Poisson(p·r)`, `K ∼ Poisson((1−p)·r)`,
  and `M ⟂ K` (Theorem 3.3.10, all three conclusions derived).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat

namespace PoissonThinning

/-! ### The marked joint measure -/

/-- Weight of the binomially-marked `Poisson(r)` pair law at `(j, k)`:
`e^{−r} r^{j+k}/(j+k)! · C(j+k, j) pʲ (1−p)ᵏ` — "`j+k` events arrived, and a
Binomial(`j+k`, `p`) draw sent `j` of them to stream 1". -/
noncomputable def markedWeight (r p : ℝ≥0) (jk : ℕ × ℕ) : ℝ :=
  rexp (-(r : ℝ)) * (r : ℝ) ^ (jk.1 + jk.2) / (jk.1 + jk.2)! *
    ((jk.1 + jk.2).choose jk.1) * (p : ℝ) ^ jk.1 * (1 - (p : ℝ)) ^ jk.2

/-- The joint law of the two thinned counts, as a measure on `ℕ × ℕ`. -/
noncomputable def markedPoissonMeasure (r p : ℝ≥0) : Measure (ℕ × ℕ) :=
  Measure.sum fun jk => ENNReal.ofReal (markedWeight r p jk) • Measure.dirac jk

lemma markedPoissonMeasure_singleton (r p : ℝ≥0) (jk : ℕ × ℕ) :
    markedPoissonMeasure r p {jk} = ENNReal.ofReal (markedWeight r p jk) := by
  rw [markedPoissonMeasure, Measure.sum_smul_dirac_singleton]

/-! ### The pointwise factorisation -/

/-- **Pointwise factorisation of the marked weight.** For `p ≤ 1`,
`e^{−r} r^{j+k}/(j+k)! · C(j+k,j) pʲ (1−p)ᵏ
  = [e^{−pr}(pr)ʲ/j!] · [e^{−(1−p)r}((1−p)r)ᵏ/k!]`. -/
private lemma markedWeight_eq {r p : ℝ≥0} (hp : p ≤ 1) (j k : ℕ) :
    markedWeight r p (j, k)
      = rexp (-((p * r : ℝ≥0) : ℝ)) * ((p * r : ℝ≥0) : ℝ) ^ j / j ! *
          (rexp (-(((1 - p) * r : ℝ≥0) : ℝ)) *
            (((1 - p) * r : ℝ≥0) : ℝ) ^ k / k !) := by
  have hq : (((1 : ℝ≥0) - p : ℝ≥0) : ℝ) = 1 - (p : ℝ) := by
    rw [NNReal.coe_sub hp, NNReal.coe_one]
  have hfact : ((j + k).choose j : ℝ) * (j ! : ℝ) * (k ! : ℝ) = ((j + k)! : ℝ) := by
    rw [show (j + k).choose j = (j + k).choose k from Nat.choose_symm_add]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ)
      (Nat.add_choose_mul_factorial_mul_factorial j k)
  have hsplit : rexp (-(r : ℝ))
      = rexp (-((p : ℝ) * r)) * rexp (-((1 - (p : ℝ)) * r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hj0 : (j ! : ℝ) ≠ 0 := by positivity
  have hk0 : (k ! : ℝ) ≠ 0 := by positivity
  have hjk0 : ((j + k)! : ℝ) ≠ 0 := by positivity
  rw [markedWeight]
  push_cast [hq]
  rw [hsplit]
  simp only [mul_pow]
  field_simp
  linear_combination (r : ℝ) ^ (j + k) * (p : ℝ) ^ j * (1 - (p : ℝ)) ^ k * hfact

/-! ### The measure-level factorisation -/

/-- **Thinning factorisation (Theorem 3.3.10, law level).** The binomially
marked `Poisson(r)` joint measure is the product
`Poisson(p·r) ×ₘ Poisson((1−p)·r)` — thinned streams are independent Poissons
at the thinned rates. -/
theorem markedPoissonMeasure_eq_prod (r : ℝ≥0) {p : ℝ≥0} (hp : p ≤ 1) :
    markedPoissonMeasure r p
      = (poissonMeasure (p * r)).prod (poissonMeasure ((1 - p) * r)) := by
  refine Measure.ext_of_singleton fun jk => ?_
  obtain ⟨j, k⟩ := jk
  rw [markedPoissonMeasure_singleton, markedWeight_eq hp,
    show ({(j, k)} : Set (ℕ × ℕ)) = {j} ×ˢ {k} from
      (Set.singleton_prod_singleton).symm,
    Measure.prod_prod, poissonMeasure_singleton, poissonMeasure_singleton,
    ENNReal.ofReal_mul (by positivity)]

/-! ### Thinned streams at random-variable level -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The marking hypothesis at event level determines the joint law. -/
theorem map_pair_eq_marked {M K : Ω → ℕ} (hM : Measurable M) (hK : Measurable K)
    {r p : ℝ≥0}
    (hjoint : ∀ j k : ℕ, μ {ω | M ω = j ∧ K ω = k}
        = ENNReal.ofReal (markedWeight r p (j, k))) :
    μ.map (fun ω => (M ω, K ω)) = markedPoissonMeasure r p := by
  refine Measure.ext_of_singleton fun jk => ?_
  obtain ⟨j, k⟩ := jk
  rw [Measure.map_apply (hM.prodMk hK) (measurableSet_singleton _),
    markedPoissonMeasure_singleton,
    show (fun ω => (M ω, K ω)) ⁻¹' {(j, k)} = {ω | M ω = j ∧ K ω = k} by
      ext ω; simp [Prod.ext_iff]]
  exact hjoint j k

/-- **Theorem 3.3.10 (thinning/splitting), all three conclusions.** If the
joint law of the type counts `(M, K)` is the binomial marking of `Poisson(r)`
with marking probability `p ≤ 1`, then `M ∼ Poisson(p·r)`,
`K ∼ Poisson((1−p)·r)`, and `M` and `K` are **independent**. -/
theorem thinned_streams {M K : Ω → ℕ} (hM : Measurable M) (hK : Measurable K)
    {r p : ℝ≥0} (hp : p ≤ 1)
    (hjoint : ∀ j k : ℕ, μ {ω | M ω = j ∧ K ω = k}
        = ENNReal.ofReal (markedWeight r p (j, k))) :
    μ.map M = poissonMeasure (p * r) ∧
      μ.map K = poissonMeasure ((1 - p) * r) ∧
      IndepFun M K μ := by
  have hpair : μ.map (fun ω => (M ω, K ω))
      = (poissonMeasure (p * r)).prod (poissonMeasure ((1 - p) * r)) := by
    rw [map_pair_eq_marked hM hK hjoint, markedPoissonMeasure_eq_prod r hp]
  have hMlaw : μ.map M = poissonMeasure (p * r) := by
    rw [← Measure.fst_map_prodMk hK, hpair, Measure.fst_prod]
  have hKlaw : μ.map K = poissonMeasure ((1 - p) * r) := by
    rw [← Measure.snd_map_prodMk hM, hpair, Measure.snd_prod]
  have σM : SigmaFinite (μ.map M) := by rw [hMlaw]; infer_instance
  have σK : SigmaFinite (μ.map K) := by rw [hKlaw]; infer_instance
  refine ⟨hMlaw, hKlaw, ?_⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map' hM.aemeasurable hK.aemeasurable σM σK,
    hMlaw, hKlaw]
  exact hpair

end PoissonThinning

end MathFin
