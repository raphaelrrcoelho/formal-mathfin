/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ChangeOfMeasure
public import MathFin.Foundations.BrownianMartingale
public import MathFin.Foundations.EquivMeasure

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

/-- **The constant-θ Girsanov measure is a probability measure.** `Q = P.withDensity Z_T`
with the Wald density `Z_T = exp(−θ X_T − ½θ² T)`: the density is measurable, strictly
positive, `P`-integrable (Gaussian MGF), and has unit `P`-mean — the Wald exponential is a
`P`-martingale started at `Z_0 = exp(−θ X_0) = 1` (since `X_0 = 0` a.s.), so `∫ Z_T dP =
∫ Z_0 dP = 1`. -/
theorem girsanovMeasure_isProbabilityMeasure
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ : ℝ) (T : ℝ≥0) :
    IsProbabilityMeasure
      (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) := by
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦
    ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  set g : Ω → ℝ := fun ω ↦ Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2) with hgdef
  have hgmeas : Measurable g := Real.measurable_exp.comp (((hmeasX T).const_mul (-θ)).sub_const _)
  have hgpos : ∀ ω, 0 < g ω := fun ω ↦ Real.exp_pos _
  have hgfactor : g = fun ω ↦ Real.exp (-(θ ^ 2 * (T : ℝ) / 2)) * Real.exp (-θ * X T ω) := by
    funext ω
    show Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2)
        = Real.exp (-(θ ^ 2 * (T : ℝ) / 2)) * Real.exp (-θ * X T ω)
    rw [show -θ * X T ω - θ ^ 2 * (T : ℝ) / 2
          = -(θ ^ 2 * (T : ℝ) / 2) + -θ * X T ω from by ring, Real.exp_add]
  have hgint : Integrable g P := by
    rw [hgfactor]; exact (integrable_exp_mul_of_hasLaw (hX.hasLaw_eval T) (-θ)).const_mul _
  -- The Wald exponential `Z_u = exp(−θ X_u − ½θ² u)` is a `P`-martingale.
  have hZmart : Martingale (fun u ω ↦ Real.exp (-θ * X u ω - θ ^ 2 * (u : ℝ) / 2)) 𝓕 P := by
    have key : (fun u ω ↦ Real.exp (-θ * X u ω - θ ^ 2 * (u : ℝ) / 2))
        = fun u ω ↦ Real.exp (-θ * X u ω - (-θ) ^ 2 * (u : ℝ) / 2) := by
      funext u ω; rw [neg_sq]
    rw [key]; exact IsFilteredPreBrownian.waldExponential_isMartingale (-θ)
  -- `X_0 = 0` a.s. (its law is `gaussianReal 0 0 = dirac 0`).
  have hX0 : P {ω | X 0 ω ≠ 0} = 0 := by
    have hmap := Measure.map_apply (μ := P) (hmeasX 0) (measurableSet_singleton (0 : ℝ)).compl
    rw [(hX.hasLaw_eval 0).map_eq, gaussianReal_zero_var,
        Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl] at hmap
    have hpre : X 0 ⁻¹' {(0 : ℝ)}ᶜ = {ω | X 0 ω ≠ 0} := by
      ext ω; simp [Set.mem_preimage]
    rw [hpre] at hmap
    simpa using hmap.symm
  -- `∫ Z_0 dP = 1`, hence `∫ g dP = ∫ Z_T dP = ∫ Z_0 dP = 1`.
  have hgsum : ∫ ω, g ω ∂P = 1 := by
    have hmean := hZmart.setIntegral_eq (i := 0) (j := T) zero_le (s := Set.univ)
      MeasurableSet.univ
    simp only [Measure.restrict_univ] at hmean
    have hZ0 : ∫ ω, Real.exp (-θ * X 0 ω - θ ^ 2 * ((0 : ℝ≥0) : ℝ) / 2) ∂P = 1 := by
      have hae : (fun ω ↦ Real.exp (-θ * X 0 ω - θ ^ 2 * ((0 : ℝ≥0) : ℝ) / 2))
          =ᵐ[P] fun _ ↦ (1 : ℝ) := by
        filter_upwards [ae_iff.mpr hX0] with ω hω
        simp [hω]
      rw [integral_congr_ae hae]; simp
    calc ∫ ω, g ω ∂P
        = ∫ ω, Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2) ∂P := rfl
      _ = ∫ ω, Real.exp (-θ * X 0 ω - θ ^ 2 * ((0 : ℝ≥0) : ℝ) / 2) ∂P := hmean.symm
      _ = 1 := hZ0
  exact (isEquivProbMeasure_withDensity P hgmeas hgpos hgint hgsum).1

/-- **The `Q`-moment-generating function of the drift-corrected process is the standard
Brownian one.** `𝔼_Q[exp(a·(X_t + θ t))] = exp(½ t a²)` for every `a`, i.e. `B^θ_t = X_t +
θ t` has the MGF of `N(0, t)` under the constant-θ Girsanov measure `Q`. Read off from
`expBtheta_isQMartingale` at `s = 0`: the `Q`-integral of `exp(a·B^θ_t − ½a² t)` equals its
value at `t = 0`, which is `exp(a·X_0) = 1` a.s. (since `X_0 = 0`), so
`𝔼_Q[exp(a·B^θ_t)] = exp(½a² t)`. -/
theorem mgf_Btheta_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ : ℝ) (T : ℝ≥0) {t : ℝ≥0} (htT : t ≤ T) (a : ℝ) :
    ∫ ω, Real.exp (a * (X t ω + θ * (t : ℝ)))
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2)))
      = Real.exp ((t : ℝ) * a ^ 2 / 2) := by
  set Q := P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
    with hQdef
  haveI hQprob : IsProbabilityMeasure Q :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦
    ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  -- `X_0 = 0` a.s. `P`, hence a.s. `Q` (`Q ≪ P`).
  have hX0P : P {ω | X 0 ω ≠ 0} = 0 := by
    have hmap := Measure.map_apply (μ := P) (hmeasX 0) (measurableSet_singleton (0 : ℝ)).compl
    rw [(hX.hasLaw_eval 0).map_eq, gaussianReal_zero_var,
        Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl] at hmap
    have hpre : X 0 ⁻¹' {(0 : ℝ)}ᶜ = {ω | X 0 ω ≠ 0} := by ext ω; simp [Set.mem_preimage]
    rw [hpre] at hmap
    simpa using hmap.symm
  have hQP : Q ≪ P := by rw [hQdef]; exact withDensity_absolutelyContinuous _ _
  have hX0Q : ∀ᵐ ω ∂Q, X 0 ω = 0 := hQP.ae_le (ae_iff.mpr hX0P)
  -- The martingale identity at `s = 0`, `A = univ`.
  have hbrick := expBtheta_isQMartingale (P := P) (𝓕 := 𝓕) (X := X) θ a T (s := 0) zero_le htT
    (A := Set.univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at hbrick
  rw [← hQdef] at hbrick
  -- RHS collapses: `exp(a(X_0 + 0) − 0) = 1` a.s. `Q`, so `∫ = 1`.
  have hRHS : ∫ ω, Real.exp (a * (X 0 ω + θ * ((0 : ℝ≥0) : ℝ)) - a ^ 2 * ((0 : ℝ≥0) : ℝ) / 2) ∂Q
      = 1 := by
    have hae : (fun ω ↦ Real.exp (a * (X 0 ω + θ * ((0 : ℝ≥0) : ℝ)) - a ^ 2 * ((0 : ℝ≥0) : ℝ) / 2))
        =ᵐ[Q] fun _ ↦ (1 : ℝ) := by
      filter_upwards [hX0Q] with ω hω; simp [hω]
    rw [integral_congr_ae hae]; simp
  rw [hRHS] at hbrick
  -- LHS: pull out the deterministic `exp(−½a² t)` factor.
  have hLHS : ∫ ω, Real.exp (a * (X t ω + θ * (t : ℝ)) - a ^ 2 * (t : ℝ) / 2) ∂Q
      = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) *
        ∫ ω, Real.exp (a * (X t ω + θ * (t : ℝ))) ∂Q := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    show Real.exp (a * (X t ω + θ * (t : ℝ)) - a ^ 2 * (t : ℝ) / 2)
        = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * Real.exp (a * (X t ω + θ * (t : ℝ)))
    rw [show a * (X t ω + θ * (t : ℝ)) - a ^ 2 * (t : ℝ) / 2
          = -(a ^ 2 * (t : ℝ) / 2) + a * (X t ω + θ * (t : ℝ)) from by ring, Real.exp_add]
  rw [hLHS, mul_comm] at hbrick
  -- Solve for the target MGF.
  have hfac : Real.exp (-(a ^ 2 * (t : ℝ) / 2)) ≠ 0 := (Real.exp_pos _).ne'
  rw [(mul_eq_one_iff_eq_inv₀ hfac).mp hbrick, ← Real.exp_neg]
  congr 1
  ring

/-- **Constant-θ distributional Girsanov (marginal law).** Under the Girsanov measure
`Q = P.withDensity(exp(−θ X_T − ½θ² T))`, the drift-corrected marginal `B^θ_t = X_t + θ t`
has law `N(0, t)`:
`Q.map (X_· + θ t) = gaussianReal 0 t`. The `Q`-MGF is the `N(0,t)` MGF (`mgf_Btheta_eq`);
`integrableExpSet_eq_of_mgf` transfers the (full-line) integrable-exponential set from the
Gaussian, so `eqOn_complexMGF_of_mgf` upgrades the MGF match to a full complex-MGF match on
all of `ℂ`, and `Measure.ext_of_complexMGF_eq` reads off the law. This is the constant-θ
half of the distributional Girsanov (`gir-thm-9.1.8`), at the marginal level, reached with
the existing tower — no adapted-integrand Itô formula. -/
theorem Btheta_map_eq_gaussianReal
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ : ℝ) (T : ℝ≥0) {t : ℝ≥0} (htT : t ≤ T) :
    (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))).map
        (fun ω ↦ X t ω + θ * (t : ℝ))
      = gaussianReal 0 t := by
  set Q := P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
    with hQdef
  haveI hQprob : IsProbabilityMeasure Q :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦
    ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  have hbθmeas : Measurable (fun ω ↦ X t ω + θ * (t : ℝ)) := (hmeasX t).add_const _
  -- The `Q`-MGF equals the `N(0,t)` MGF.
  have hmgf : mgf (fun ω ↦ X t ω + θ * (t : ℝ)) Q = mgf id (gaussianReal 0 t) := by
    rw [mgf_id_gaussianReal]
    funext a
    show ∫ ω, Real.exp (a * (X t ω + θ * (t : ℝ))) ∂Q = Real.exp (0 * a + (t : ℝ) * a ^ 2 / 2)
    rw [mgf_Btheta_eq (P := P) (𝓕 := 𝓕) (X := X) θ T htT a, zero_mul, zero_add]
  -- The integrable-exponential set is all of `ℝ` (transferred from the Gaussian).
  have hIESgauss : integrableExpSet id (gaussianReal 0 t) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro a
    show Integrable (fun x ↦ Real.exp (a * x)) (gaussianReal 0 t)
    exact integrable_exp_mul_gaussianReal a
  have hIES : integrableExpSet (fun ω ↦ X t ω + θ * (t : ℝ)) Q = Set.univ := by
    rw [integrableExpSet_eq_of_mgf hmgf, hIESgauss]
  -- Upgrade the MGF match to a full complex-MGF match on all of `ℂ`.
  have hset : {z : ℂ | z.re ∈ interior (integrableExpSet (fun ω ↦ X t ω + θ * (t : ℝ)) Q)}
      = Set.univ := by
    rw [hIES, interior_univ]; ext z; simp
  have hcomplexeq :
      complexMGF (fun ω ↦ X t ω + θ * (t : ℝ)) Q = complexMGF id (gaussianReal 0 t) := by
    funext z
    exact eqOn_complexMGF_of_mgf hmgf (hset ▸ Set.mem_univ z)
  have hmap := Measure.ext_of_complexMGF_eq (μ := Q) (μ' := gaussianReal 0 t)
    hbθmeas.aemeasurable aemeasurable_id hcomplexeq
  rwa [Measure.map_id] at hmap

/-- **`Q`-integrability of the drift-corrected exponential.** For `u ≤ T` and any `a`,
`exp(a·(X_u + θ u))` is `Q`-integrable — its `Q`-law is `N(0,u)` (`Btheta_map_eq_gaussianReal`)
and the Gaussian MGF is finite. -/
theorem integrable_expBtheta
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ a : ℝ) (T : ℝ≥0) {u : ℝ≥0} (huT : u ≤ T) :
    Integrable (fun ω ↦ Real.exp (a * (X u ω + θ * (u : ℝ))))
      (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) := by
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦
    ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  have hbθmeas : Measurable (fun ω ↦ X u ω + θ * (u : ℝ)) := (hmeasX u).add_const _
  rw [show (fun ω ↦ Real.exp (a * (X u ω + θ * (u : ℝ))))
        = (fun x ↦ Real.exp (a * x)) ∘ (fun ω ↦ X u ω + θ * (u : ℝ)) from rfl,
      ← integrable_map_measure (by fun_prop) hbθmeas.aemeasurable,
      Btheta_map_eq_gaussianReal (X := X) (𝓕 := 𝓕) θ T huT]
  exact integrable_exp_mul_gaussianReal a

/-- **Conditional constant-θ Girsanov martingale.** `𝔼_Q[exp(a·B^θ_t − ½a² t) | 𝓕_s] =
exp(a·B^θ_s − ½a² s)` a.e., the conditional form of `expBtheta_isQMartingale` (its set-integral
identity over `𝓕_s` sets, converted via `ae_eq_condExp_of_forall_setIntegral_eq`). Rearranged,
this is the conditional `Q`-MGF `𝔼_Q[exp(a·(B^θ_t − B^θ_s)) | 𝓕_s] = exp(½a²(t−s))` — the
increment law and independence engine for `B^θ` being `Q`-Brownian. -/
theorem condExp_expBtheta
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ a : ℝ) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) :
    (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2)))[
        fun ω ↦ Real.exp (a * (X t ω + θ * (t : ℝ)) - a ^ 2 * (t : ℝ) / 2) | 𝓕 s]
      =ᵐ[P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))]
        fun ω ↦ Real.exp (a * (X s ω + θ * (s : ℝ)) - a ^ 2 * (s : ℝ) / 2) := by
  set Q := P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
    with hQdef
  haveI hQprob : IsProbabilityMeasure Q :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦
    ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  -- `f_u := exp(a·B^θ_u − ½a² u)` is `Q`-integrable and (at `s`) `𝓕_s`-measurable.
  have hfint : ∀ u : ℝ≥0, u ≤ T →
      Integrable (fun ω ↦ Real.exp (a * (X u ω + θ * (u : ℝ)) - a ^ 2 * (u : ℝ) / 2)) Q := by
    intro u huT
    have hfac : (fun ω ↦ Real.exp (a * (X u ω + θ * (u : ℝ)) - a ^ 2 * (u : ℝ) / 2))
        = fun ω ↦ Real.exp (-(a ^ 2 * (u : ℝ) / 2)) * Real.exp (a * (X u ω + θ * (u : ℝ))) := by
      funext ω
      rw [show a * (X u ω + θ * (u : ℝ)) - a ^ 2 * (u : ℝ) / 2
            = -(a ^ 2 * (u : ℝ) / 2) + a * (X u ω + θ * (u : ℝ)) from by ring, Real.exp_add]
    rw [hfac]
    exact (integrable_expBtheta (X := X) (𝓕 := 𝓕) θ a T huT).const_mul _
  have hsm : StronglyMeasurable[𝓕 s]
      (fun ω ↦ Real.exp (a * (X s ω + θ * (s : ℝ)) - a ^ 2 * (s : ℝ) / 2)) := by
    have hcont : Continuous fun x : ℝ ↦ a * (x + θ * (s : ℝ)) - a ^ 2 * (s : ℝ) / 2 := by fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable
      (hcont.comp_stronglyMeasurable (hX.stronglyAdapted s))
  -- Convert the set-integral martingale identity to a conditional expectation.
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hfint t htT)
    (fun A _ _ ↦ (hfint s (hst.trans htT)).integrableOn) (fun A hA _ ↦ ?_)
    hsm.aestronglyMeasurable).symm
  exact (expBtheta_isQMartingale (P := P) (𝓕 := 𝓕) (X := X) θ a T hst htT hA).symm

end MathFin
