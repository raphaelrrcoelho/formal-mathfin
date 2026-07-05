/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ChangeOfMeasure
public import MathFin.Foundations.BrownianMartingale

/-!
# Constant-θ distributional Girsanov — the drift-corrected exponential is a Q-martingale

Route-α base case (`docs/specs/2026-07-05-adapted-ito-formula-design.md`, "Route
decision update"). For a **constant** market price of risk `θ`, the Girsanov measure
is `Q = P.withDensity Z_T` with the Wald density `Z_t = exp(−θ X_t − ½θ² t)`
(a `P`-martingale, `waldExponential_isMartingale (−θ)`), and the drift-corrected
process is `B^θ_t = X_t + θ t`.

The key exponential-characterization brick: for **every** `a : ℝ`,
`exp(a·B^θ_t − ½a² t)` is a `Q`-martingale on `[0,T]`. The mechanism is the reusable
Bayes change-of-measure engine (`changeOfMeasure_setIntegral_eq`) fed two Wald
exponentials —

  `Z_t   = exp(−θ X_t − ½θ² t)`            (Wald at `−θ`),
  `Z_t·D_t = exp((a−θ) X_t − ½(a−θ)² t)`   (Wald at `a−θ`, by the pointwise algebra
                                            `−θx − ½θ²u + a(x+θu) − ½a²u
                                             = (a−θ)x − ½(a−θ)²u`),

both `P`-martingales; the engine turns `D_t = exp(a·B^θ_t − ½a² t)` into a
`Q`-martingale. The one genuinely new estimate is the mixed-time integrability of
`D_u · Z_T`, by AM–GM (`exp(a X_u)·exp(−θ X_T) ≤ exp(2a X_u) + exp(−2θ X_T)`, each a
Gaussian-MGF term via `integrable_exp_mul_of_hasLaw`) — the same device as
`bs_discounted_isQMartingale`.

Since `E_Q[exp(a(B^θ_t − B^θ_s)) | 𝓕_s] = exp(½a²(t−s))` for all `a` characterizes
`B^θ` as a `Q`-Brownian motion, this is the constant-θ half of the distributional
Girsanov (`gir-thm-9.1.8`), reached with the existing tower — no adapted-integrand
Itô formula.

## Main result

* `MathFin.expBtheta_isQMartingale`
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- **Constant-θ Girsanov: the drift-corrected exponential is a `Q`-martingale.**
For constant `θ` and any `a : ℝ`, under `Q = P.withDensity (exp(−θ X_T − ½θ² T))`,
the exponential `exp(a·(X_t + θ t) − ½a² t)` of the drift-corrected process
`B^θ_t = X_t + θ t` is a martingale on `[0,T]`: for `s ≤ t ≤ T` and `A ∈ 𝓕_s`, the
`Q`-integrals over `A` at `t` and `s` agree. Proof: `Z = exp(−θX − ½θ²·)` and
`Z·D = exp((a−θ)X − ½(a−θ)²·)` are the Wald `P`-martingales at `−θ` and `a−θ`; the
Bayes engine `changeOfMeasure_setIntegral_eq` does the rest. -/
theorem expBtheta_isQMartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ a : ℝ) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, Real.exp (a * (X t ω + θ * (t : ℝ)) - a ^ 2 * (t : ℝ) / 2)
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal
          (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2)))
      = ∫ ω in A, Real.exp (a * (X s ω + θ * (s : ℝ)) - a ^ 2 * (s : ℝ) / 2)
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal
          (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) := by
  set Z : ℝ≥0 → Ω → ℝ := fun u ω ↦ Real.exp (-θ * X u ω - θ ^ 2 * (u : ℝ) / 2) with hZdef
  set D : ℝ≥0 → Ω → ℝ :=
    fun u ω ↦ Real.exp (a * (X u ω + θ * (u : ℝ)) - a ^ 2 * (u : ℝ) / 2) with hDdef
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦
    ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  -- Density `Z_T` is measurable and nonnegative.
  have hZmeasT : Measurable (Z T) := by
    rw [hZdef]; exact Real.measurable_exp.comp (((hmeasX T).const_mul (-θ)).sub_const _)
  have hZpos : ∀ ω, 0 ≤ Z T ω := fun ω ↦ (Real.exp_pos _).le
  -- `D` is adapted (continuous function of the adapted `X_u`).
  have hDsm : ∀ u, StronglyMeasurable[𝓕 u] (D u) := by
    intro u
    have hcont : Continuous fun x : ℝ => a * (x + θ * (u : ℝ)) - a ^ 2 * (u : ℝ) / 2 := by
      fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable
      (hcont.comp_stronglyMeasurable (hX.stronglyAdapted u))
  -- `Z` is a `P`-martingale: the Wald exponential at `α = −θ`.
  have hZ : Martingale Z 𝓕 P := by
    have key : Z = fun u ω ↦ Real.exp (-θ * X u ω - (-θ) ^ 2 * (u : ℝ) / 2) := by
      funext u ω; rw [hZdef, neg_sq]
    rw [key]; exact IsFilteredPreBrownian.waldExponential_isMartingale (-θ)
  -- `Z · D = Wald(a − θ)` is a `P`-martingale.
  have hZD : Martingale (fun u ω ↦ Z u ω * D u ω) 𝓕 P := by
    have key : (fun u ω ↦ Z u ω * D u ω)
        = fun u ω ↦ Real.exp ((a - θ) * X u ω - (a - θ) ^ 2 * (u : ℝ) / 2) := by
      funext u ω
      simp only [hZdef, hDdef]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [key]; exact IsFilteredPreBrownian.waldExponential_isMartingale (a - θ)
  -- Mixed-time integrability of `D_u · Z_T` via AM–GM.
  have hmix : ∀ u, u ≤ T → Integrable (fun ω ↦ D u ω * Z T ω) P := by
    intro u _
    simp only [hZdef, hDdef]
    have hcore : Integrable (fun ω ↦ Real.exp (a * X u ω) * Real.exp (-θ * X T ω)) P := by
      have hbnd : Integrable
          (fun ω ↦ Real.exp (2 * a * X u ω) + Real.exp (-2 * θ * X T ω)) P :=
        (integrable_exp_mul_of_hasLaw (hX.hasLaw_eval u) (2 * a)).add
          (integrable_exp_mul_of_hasLaw (hX.hasLaw_eval T) (-2 * θ))
      refine Integrable.mono' hbnd ?_ ?_
      · exact ((Real.measurable_exp.comp ((hmeasX u).const_mul a)).mul
          (Real.measurable_exp.comp ((hmeasX T).const_mul (-θ)))).aestronglyMeasurable
      · filter_upwards with ω
        rw [Real.norm_of_nonneg (by positivity)]
        have ea : Real.exp (2 * a * X u ω) = Real.exp (a * X u ω) ^ 2 := by
          rw [pow_two, ← Real.exp_add]; congr 1; ring
        have eb : Real.exp (-2 * θ * X T ω) = Real.exp (-θ * X T ω) ^ 2 := by
          rw [pow_two, ← Real.exp_add]; congr 1; ring
        rw [ea, eb]
        nlinarith [sq_nonneg (Real.exp (a * X u ω) - Real.exp (-θ * X T ω)),
          (Real.exp_pos (a * X u ω)).le, (Real.exp_pos (-θ * X T ω)).le,
          mul_pos (Real.exp_pos (a * X u ω)) (Real.exp_pos (-θ * X T ω))]
    have hrw : (fun ω ↦
        Real.exp (a * (X u ω + θ * (u : ℝ)) - a ^ 2 * (u : ℝ) / 2) *
        Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
        = fun ω ↦ (Real.exp (a * θ * (u : ℝ) - a ^ 2 * (u : ℝ) / 2
            - θ ^ 2 * (T : ℝ) / 2)) *
            (Real.exp (a * X u ω) * Real.exp (-θ * X T ω)) := by
      funext ω
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hrw]; exact hcore.const_mul _
  exact changeOfMeasure_setIntegral_eq T hZmeasT hZpos hDsm hZ hZD hmix hst htT hA

end MathFin
