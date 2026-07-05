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
open scoped NNReal ENNReal RealInnerProductSpace

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

/-- **Conditional `Q`-MGF of the increment.** `𝔼_Q[exp(a·(B^θ_t − B^θ_s)) | 𝓕_s] =
exp(½a²(t−s))` a.e. — deterministic. Rearranges `condExp_expBtheta` by pulling the
`𝓕_s`-measurable factor `exp(½a² t − a·B^θ_s)` out of the conditional expectation
(`condExp_mul_of_stronglyMeasurable_left`), so `exp(a·(B^θ_t−B^θ_s)) =
exp(½a² t − a·B^θ_s)·exp(a·B^θ_t − ½a² t)` collapses to `exp(½a²(t−s))`. Taking `𝔼_Q`
gives the increment `N(0,t−s)` MGF; the *deterministic* conditional value is the
increment-independence witness (once a conditional-MGF ⟹ independence result is available). -/
theorem condExp_Btheta_increment
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ a : ℝ) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) :
    (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2)))[
        fun ω ↦ Real.exp (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))) | 𝓕 s]
      =ᵐ[P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))]
        fun _ ↦ Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
  set Q := P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
    with hQdef
  haveI hQprob : IsProbabilityMeasure Q :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦
    ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  -- `f_t := exp(a·B^θ_t − ½a² t)` and the `𝓕_s`-measurable factor `g := exp(½a² t − a·B^θ_s)`.
  set ft : Ω → ℝ := fun ω ↦ Real.exp (a * (X t ω + θ * (t : ℝ)) - a ^ 2 * (t : ℝ) / 2) with hftdef
  set gs : Ω → ℝ := fun ω ↦ Real.exp (a ^ 2 * (t : ℝ) / 2 - a * (X s ω + θ * (s : ℝ))) with hgsdef
  have hgs_sm : StronglyMeasurable[𝓕 s] gs := by
    have hcont : Continuous fun x : ℝ ↦ a ^ 2 * (t : ℝ) / 2 - a * (x + θ * (s : ℝ)) := by fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable
      (hcont.comp_stronglyMeasurable (hX.stronglyAdapted s))
  have hft_int : Integrable ft Q := by
    have hfac : ft = fun ω ↦ Real.exp (-(a ^ 2 * (t : ℝ) / 2)) *
        Real.exp (a * (X t ω + θ * (t : ℝ))) := by
      funext ω
      show Real.exp (a * (X t ω + θ * (t : ℝ)) - a ^ 2 * (t : ℝ) / 2)
          = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * Real.exp (a * (X t ω + θ * (t : ℝ)))
      rw [show a * (X t ω + θ * (t : ℝ)) - a ^ 2 * (t : ℝ) / 2
            = -(a ^ 2 * (t : ℝ) / 2) + a * (X t ω + θ * (t : ℝ)) from by ring, Real.exp_add]
    rw [hfac]; exact (integrable_expBtheta (X := X) (𝓕 := 𝓕) θ a T htT).const_mul _
  -- `gs · ft = exp(a·(B^θ_t − B^θ_s))` pointwise.
  have hprod : (fun ω ↦ gs ω * ft ω)
      = fun ω ↦ Real.exp (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))) := by
    funext ω
    rw [hgsdef, hftdef, ← Real.exp_add]
    congr 1; ring
  -- Integrability of the increment exponential, by AM–GM against two Gaussian-MGF terms.
  have hprod_int : Integrable (fun ω ↦ gs ω * ft ω) Q := by
    rw [hprod]
    have hbnd : Integrable (fun ω ↦ Real.exp (2 * a * (X t ω + θ * (t : ℝ)))
        + Real.exp (-2 * a * (X s ω + θ * (s : ℝ)))) Q :=
      (integrable_expBtheta (X := X) (𝓕 := 𝓕) θ (2 * a) T htT).add
        (integrable_expBtheta (X := X) (𝓕 := 𝓕) θ (-2 * a) T (hst.trans htT))
    refine Integrable.mono' hbnd (by fun_prop) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    have ep : Real.exp (2 * a * (X t ω + θ * (t : ℝ)))
        = Real.exp (a * (X t ω + θ * (t : ℝ))) ^ 2 := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have eq' : Real.exp (-2 * a * (X s ω + θ * (s : ℝ)))
        = Real.exp (-a * (X s ω + θ * (s : ℝ))) ^ 2 := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have eprod : Real.exp (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))))
        = Real.exp (a * (X t ω + θ * (t : ℝ))) * Real.exp (-a * (X s ω + θ * (s : ℝ))) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [ep, eq', eprod]
    nlinarith [sq_nonneg (Real.exp (a * (X t ω + θ * (t : ℝ)))
        - Real.exp (-a * (X s ω + θ * (s : ℝ)))),
      (Real.exp_pos (a * (X t ω + θ * (t : ℝ)))).le,
      (Real.exp_pos (-a * (X s ω + θ * (s : ℝ)))).le]
  -- Pull the `𝓕_s`-measurable `gs` out and apply the conditional martingale.
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := (𝓕 s : MeasurableSpace Ω))
    hgs_sm hprod_int hft_int
  have hcond := condExp_expBtheta (P := P) (𝓕 := 𝓕) (X := X) θ a T hst htT
  rw [← hQdef] at hcond
  have hint_eq : (fun ω ↦ Real.exp (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))))
      = gs * ft := hprod.symm
  rw [hint_eq]
  filter_upwards [hpull, hcond] with ω hp hc
  rw [hp, Pi.mul_apply,
    show (Q[ft | 𝓕 s]) ω = Real.exp (a * (X s ω + θ * (s : ℝ)) - a ^ 2 * (s : ℝ) / 2) from hc,
    hgsdef, ← Real.exp_add]
  congr 1; ring

/-- **Unconditional `Q`-MGF of the increment.** `𝔼_Q[exp(a·(B^θ_t − B^θ_s))] = exp(½ a²(t−s))`
— the tower property `𝔼_Q[exp(a·incr)] = 𝔼_Q[𝔼_Q[exp(a·incr)|𝓕_s]]` (`integral_condExp`) on the
deterministic conditional MGF `condExp_Btheta_increment`, integrated against the unit-mass `Q`. -/
theorem Btheta_increment_mgf
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ a : ℝ) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) :
    ∫ ω, Real.exp (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))))
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2)))
      = Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
  set Q := P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
    with hQdef
  haveI hQprob : IsProbabilityMeasure Q :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  have hcond := condExp_Btheta_increment (P := P) (𝓕 := 𝓕) (X := X) θ a T hst htT
  rw [← hQdef] at hcond
  rw [← integral_condExp (𝓕.le s), integral_congr_ae hcond, integral_const,
      show Q.real Set.univ = 1 from by simp, one_smul]

/-- **Constant-θ distributional Girsanov (increment law).** Under the Girsanov measure
`Q`, the increment `B^θ_t − B^θ_s = (X_t + θ t) − (X_s + θ s)` has law `N(0, t−s)`. Its
unconditional `Q`-MGF is `exp(½ (t−s) a²)` — the tower property `𝔼_Q[exp(a·incr)] =
𝔼_Q[𝔼_Q[exp(a·incr)|𝓕_s]] = exp(½ a²(t−s))` on the deterministic conditional MGF
(`condExp_Btheta_increment`, via `integral_condExp`) — and Mathlib's complex-MGF machinery
reads off the Gaussian law. Together with `Btheta_map_eq_gaussianReal` this gives the
Gaussian-increments half of "`B^θ` is a `Q`-Brownian motion"; increment *independence*
still needs a conditional-MGF ⟹ independence result absent from Mathlib. -/
theorem Btheta_increment_map_eq_gaussianReal
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ : ℝ) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) :
    (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))).map
        (fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
      = gaussianReal 0 (t - s) := by
  set Q := P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
    with hQdef
  haveI hQprob : IsProbabilityMeasure Q :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦
    ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  have hincmeas : Measurable (fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))) :=
    ((hmeasX t).add_const _).sub ((hmeasX s).add_const _)
  -- Unconditional increment MGF `= exp(½ (t−s) a²)`, from the deterministic conditional MGF.
  have hmgf : mgf (fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))) Q
      = mgf id (gaussianReal 0 (t - s)) := by
    rw [mgf_id_gaussianReal]
    funext a
    show ∫ ω, Real.exp (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))) ∂Q
        = Real.exp (0 * a + ((t - s : ℝ≥0) : ℝ) * a ^ 2 / 2)
    rw [hQdef, Btheta_increment_mgf (P := P) (𝓕 := 𝓕) (X := X) θ a T hst htT, NNReal.coe_sub hst]
    congr 1; ring
  -- Integrable-exponential set is all of `ℝ` (transferred from the Gaussian).
  have hIESgauss : integrableExpSet id (gaussianReal 0 (t - s)) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro a
    show Integrable (fun x ↦ Real.exp (a * x)) (gaussianReal 0 (t - s))
    exact integrable_exp_mul_gaussianReal a
  have hIES : integrableExpSet (fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))) Q
      = Set.univ := by rw [integrableExpSet_eq_of_mgf hmgf, hIESgauss]
  have hset : {z : ℂ | z.re ∈
      interior (integrableExpSet (fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))) Q)}
      = Set.univ := by rw [hIES, interior_univ]; ext z; simp
  have hcomplexeq :
      complexMGF (fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))) Q
        = complexMGF id (gaussianReal 0 (t - s)) := by
    funext z
    exact eqOn_complexMGF_of_mgf hmgf (hset ▸ Set.mem_univ z)
  have hmap := Measure.ext_of_complexMGF_eq (μ := Q) (μ' := gaussianReal 0 (t - s))
    hincmeas.aemeasurable aemeasurable_id hcomplexeq
  rwa [Measure.map_id] at hmap

/-- **`Q`-integrability of the increment exponential.** For `s ≤ t ≤ T` and any `c`,
`exp(c·(B^θ_t − B^θ_s))` is `Q`-integrable — its `Q`-law is `N(0,t−s)`
(`Btheta_increment_map_eq_gaussianReal`) and the Gaussian MGF is finite. The increment analogue
of `integrable_expBtheta`, feeding the AM–GM product bounds of the joint-MGF factorisation. -/
theorem integrable_exp_Btheta_increment
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ c : ℝ) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) :
    Integrable (fun ω ↦ Real.exp (c * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))))
      (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) := by
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦
    ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  have hincmeas : Measurable (fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))) :=
    ((hmeasX t).add_const _).sub ((hmeasX s).add_const _)
  rw [show (fun ω ↦ Real.exp (c * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))))
        = (fun x ↦ Real.exp (c * x)) ∘ (fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
        from rfl,
      ← integrable_map_measure (by fun_prop) hincmeas.aemeasurable,
      Btheta_increment_map_eq_gaussianReal (X := X) (𝓕 := 𝓕) θ T hst htT]
  exact integrable_exp_mul_gaussianReal c

/-- **Joint `Q`-MGF of two disjoint increments factorises.** For `s ≤ t ≤ u ≤ v ≤ T`,
`𝔼_Q[exp(a·(B^θ_t − B^θ_s) + b·(B^θ_v − B^θ_u))] = exp(½a²(t−s))·exp(½b²(v−u))`. The earlier
increment `I₁ = B^θ_t − B^θ_s` is `𝓕_u`-measurable (`t ≤ u`), so it factors out of the
conditional expectation `𝔼_Q[·|𝓕_u]` (`condExp_mul_of_stronglyMeasurable_left`); the later
increment's conditional MGF is the deterministic `exp(½b²(v−u))` (`condExp_Btheta_increment`),
leaving `exp(½b²(v−u))·𝔼_Q[exp(a·I₁)] = exp(½b²(v−u))·exp(½a²(t−s))` (`Btheta_increment_mgf`).
The product structure of the joint MGF is the analytic heart of increment independence. -/
theorem Btheta_increments_joint_mgf
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ a b : ℝ) (T : ℝ≥0) {s t u v : ℝ≥0}
    (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ ω, Real.exp (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
        + b * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ))))
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2)))
      = Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2)
        * Real.exp (b ^ 2 * ((v : ℝ) - (u : ℝ)) / 2) := by
  set Q := P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
    with hQdef
  haveI hQprob : IsProbabilityMeasure Q :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  have hmeasX : ∀ w, Measurable (X w) := fun w ↦
    ((hX.stronglyAdapted w).mono (𝓕.le w)).measurable
  -- `e1 = exp(a·I₁)` is `𝓕_u`-measurable (`I₁` lives at time `t ≤ u`); `e2 = exp(b·I₂)`.
  set e1 : Ω → ℝ := fun ω ↦ Real.exp (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))))
    with he1def
  set e2 : Ω → ℝ := fun ω ↦ Real.exp (b * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ))))
    with he2def
  have he1meas : Measurable e1 := by
    rw [he1def]
    exact Real.measurable_exp.comp
      ((((hmeasX t).add_const _).sub ((hmeasX s).add_const _)).const_mul a)
  have he2meas : Measurable e2 := by
    rw [he2def]
    exact Real.measurable_exp.comp
      ((((hmeasX v).add_const _).sub ((hmeasX u).add_const _)).const_mul b)
  have he1_sm : StronglyMeasurable[𝓕 u] e1 := by
    have hpair : StronglyMeasurable[𝓕 u] (fun ω ↦ (X t ω, X s ω)) :=
      ((hX.stronglyAdapted t).mono (𝓕.mono htu)).prodMk
        ((hX.stronglyAdapted s).mono (𝓕.mono (hst.trans htu)))
    have hcont : Continuous fun p : ℝ × ℝ ↦
        Real.exp (a * ((p.1 + θ * (t : ℝ)) - (p.2 + θ * (s : ℝ)))) := by fun_prop
    exact hcont.comp_stronglyMeasurable hpair
  have he2_int : Integrable e2 Q := by
    rw [he2def]
    exact integrable_exp_Btheta_increment (X := X) (𝓕 := 𝓕) θ b T huv hvT
  -- `e1 · e2 = exp(a·I₁ + b·I₂)` is `Q`-integrable, by AM–GM against two increment-MGF terms.
  have hprod_int : Integrable (e1 * e2) Q := by
    have hbnd : Integrable (fun ω ↦
        Real.exp (2 * a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))))
        + Real.exp (2 * b * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ))))) Q :=
      (integrable_exp_Btheta_increment (X := X) (𝓕 := 𝓕) θ (2 * a) T hst
          (htu.trans (huv.trans hvT))).add
        (integrable_exp_Btheta_increment (X := X) (𝓕 := 𝓕) θ (2 * b) T huv hvT)
    refine Integrable.mono' hbnd (he1meas.mul he2meas).aestronglyMeasurable ?_
    filter_upwards with ω
    simp only [Pi.mul_apply, he1def, he2def]
    rw [Real.norm_of_nonneg (by positivity)]
    have ep1 : Real.exp (2 * a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))))
        = Real.exp (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))) ^ 2 := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have ep2 : Real.exp (2 * b * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ))))
        = Real.exp (b * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ)))) ^ 2 := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    rw [ep1, ep2]
    nlinarith [sq_nonneg (Real.exp (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))))
        - Real.exp (b * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ))))),
      (Real.exp_pos (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))))).le,
      (Real.exp_pos (b * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ))))).le]
  -- Pull `e1` out of `𝔼_Q[e1·e2|𝓕_u]` and collapse `𝔼_Q[e2|𝓕_u] = exp(½b²(v−u))`.
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := (𝓕 u : MeasurableSpace Ω))
    he1_sm hprod_int he2_int
  have hcond2 := condExp_Btheta_increment (P := P) (𝓕 := 𝓕) (X := X) θ b T huv hvT
  rw [← hQdef, ← he2def] at hcond2
  have hsum_eq : (fun ω ↦ Real.exp (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
      + b * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ))))) = e1 * e2 := by
    funext ω
    simp only [he1def, he2def, Pi.mul_apply]
    rw [← Real.exp_add]
  calc ∫ ω, Real.exp (a * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
        + b * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ)))) ∂Q
      = ∫ ω, (e1 * e2) ω ∂Q := by rw [hsum_eq]
    _ = ∫ ω, (Q[e1 * e2 | 𝓕 u]) ω ∂Q := (integral_condExp (𝓕.le u)).symm
    _ = ∫ ω, e1 ω * Real.exp (b ^ 2 * ((v : ℝ) - (u : ℝ)) / 2) ∂Q := by
        refine integral_congr_ae ?_
        filter_upwards [hpull, hcond2] with ω hp hc
        rw [hp, Pi.mul_apply, hc]
    _ = (∫ ω, e1 ω ∂Q) * Real.exp (b ^ 2 * ((v : ℝ) - (u : ℝ)) / 2) := integral_mul_const _ _
    _ = Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2)
          * Real.exp (b ^ 2 * ((v : ℝ) - (u : ℝ)) / 2) := by
        have he1int : ∫ ω, e1 ω ∂Q = Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
          simp only [he1def]
          rw [hQdef, Btheta_increment_mgf (P := P) (𝓕 := 𝓕) (X := X) θ a T hst
            (htu.trans (huv.trans hvT))]
        rw [he1int]

/-- **Any linear combination of two disjoint increments is Gaussian under `Q`.** For
`s ≤ t ≤ u ≤ v ≤ T` and reals `c, d`, the combination `c·(B^θ_t − B^θ_s) + d·(B^θ_v − B^θ_u)`
has law `N(0, c²(t−s) + d²(v−u))` under the Girsanov measure `Q`. Its `Q`-MGF at `r` is
`𝔼_Q[exp((rc)·I₁ + (rd)·I₂)] = exp(½(rc)²(t−s))·exp(½(rd)²(v−u)) = exp(½r²·(c²(t−s)+d²(v−u)))`
(`Btheta_increments_joint_mgf`), the `N(0,·)` MGF; Mathlib's complex-MGF machinery reads off the
Gaussian law. This packages the diagonal-covariance structure that makes the two increments
independent — the joint characteristic function factorises through every 1-D projection. -/
theorem Btheta_linComb_map_eq_gaussianReal
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ c d : ℝ) (T : ℝ≥0) {s t u v : ℝ≥0}
    (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))).map
        (fun ω ↦ c * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
              + d * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ))))
      = gaussianReal 0 (Real.toNNReal
          (c ^ 2 * ((t : ℝ) - (s : ℝ)) + d ^ 2 * ((v : ℝ) - (u : ℝ)))) := by
  set Q := P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
    with hQdef
  haveI hQprob : IsProbabilityMeasure Q :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  have hmeasX : ∀ w, Measurable (X w) := fun w ↦
    ((hX.stronglyAdapted w).mono (𝓕.le w)).measurable
  set σ2 : ℝ := c ^ 2 * ((t : ℝ) - (s : ℝ)) + d ^ 2 * ((v : ℝ) - (u : ℝ)) with hσ2def
  have hσ2nonneg : 0 ≤ σ2 :=
    add_nonneg (mul_nonneg (sq_nonneg c) (sub_nonneg.mpr (by exact_mod_cast hst)))
      (mul_nonneg (sq_nonneg d) (sub_nonneg.mpr (by exact_mod_cast huv)))
  have hlcmeas : Measurable (fun ω ↦ c * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
      + d * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ)))) :=
    ((((hmeasX t).add_const _).sub ((hmeasX s).add_const _)).const_mul c).add
      ((((hmeasX v).add_const _).sub ((hmeasX u).add_const _)).const_mul d)
  -- The `Q`-MGF of the combination equals the `N(0, σ²)` MGF.
  have hmgf : mgf (fun ω ↦ c * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
        + d * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ)))) Q
      = mgf id (gaussianReal 0 σ2.toNNReal) := by
    rw [mgf_id_gaussianReal]
    funext r
    show ∫ ω, Real.exp (r * (c * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
          + d * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ))))) ∂Q
        = Real.exp (0 * r + (σ2.toNNReal : ℝ) * r ^ 2 / 2)
    have hjoint := Btheta_increments_joint_mgf (P := P) (𝓕 := 𝓕) (X := X)
      θ (r * c) (r * d) T hst htu huv hvT
    rw [← hQdef] at hjoint
    rw [show (∫ ω, Real.exp (r * (c * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
              + d * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ))))) ∂Q)
          = ∫ ω, Real.exp ((r * c) * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
              + (r * d) * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ)))) ∂Q from by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_); ring_nf,
      hjoint, Real.coe_toNNReal σ2 hσ2nonneg, ← Real.exp_add]
    congr 1
    rw [hσ2def]; ring
  -- Integrable-exponential set is all of `ℝ` (transferred from the Gaussian).
  have hIESgauss : integrableExpSet id (gaussianReal 0 σ2.toNNReal) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro r
    show Integrable (fun x ↦ Real.exp (r * x)) (gaussianReal 0 σ2.toNNReal)
    exact integrable_exp_mul_gaussianReal r
  have hIES : integrableExpSet (fun ω ↦ c * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
        + d * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ)))) Q = Set.univ := by
    rw [integrableExpSet_eq_of_mgf hmgf, hIESgauss]
  have hset : {z : ℂ | z.re ∈ interior (integrableExpSet
      (fun ω ↦ c * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
        + d * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ)))) Q)} = Set.univ := by
    rw [hIES, interior_univ]; ext z; simp
  have hcomplexeq : complexMGF (fun ω ↦ c * ((X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
        + d * ((X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ)))) Q
      = complexMGF id (gaussianReal 0 σ2.toNNReal) := by
    funext z
    exact eqOn_complexMGF_of_mgf hmgf (hset ▸ Set.mem_univ z)
  have hmap := Measure.ext_of_complexMGF_eq (μ := Q) (μ' := gaussianReal 0 σ2.toNNReal)
    hlcmeas.aemeasurable aemeasurable_id hcomplexeq
  rwa [Measure.map_id] at hmap

/-- **Constant-θ distributional Girsanov: increments are `Q`-independent.** For
`s ≤ t ≤ u ≤ v ≤ T`, the disjoint increments `B^θ_t − B^θ_s` and `B^θ_v − B^θ_u` of the
drift-corrected process are independent under the Girsanov measure `Q`. By
`indepFun_iff_charFun_prod`, independence is equivalent to the joint characteristic function
factorising; the joint charFun at `w = (w₁, w₂)` is the characteristic function at `1` of the
linear combination `w₁·I₁ + w₂·I₂`, which is Gaussian `N(0, w₁²(t−s) + w₂²(v−u))`
(`Btheta_linComb_map_eq_gaussianReal`), so it equals `exp(−½(w₁²(t−s) + w₂²(v−u)))` — exactly the
product of the two marginal Gaussian characteristic functions
(`Btheta_increment_map_eq_gaussianReal` + `charFun_gaussianReal`). Together with the Gaussian
increment law, this completes "`B^θ` is a `Q`-Brownian motion" (`gir-thm-9.1.8`) for constant `θ`,
reached on the existing tower — no adapted-integrand Itô formula. -/
theorem Btheta_increments_indepFun
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ : ℝ) (T : ℝ≥0) {s t u v : ℝ≥0}
    (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    IndepFun (fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
        (fun ω ↦ (X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ)))
      (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) := by
  set Q := P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
    with hQdef
  haveI hQprob : IsProbabilityMeasure Q :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  have hmeasX : ∀ w, Measurable (X w) := fun w ↦
    ((hX.stronglyAdapted w).mono (𝓕.le w)).measurable
  set I₁ : Ω → ℝ := fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)) with hI₁def
  set I₂ : Ω → ℝ := fun ω ↦ (X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ)) with hI₂def
  have hI₁meas : Measurable I₁ := ((hmeasX t).add_const _).sub ((hmeasX s).add_const _)
  have hI₂meas : Measurable I₂ := ((hmeasX v).add_const _).sub ((hmeasX u).add_const _)
  -- The two marginal increment laws.
  have hlaw1 : Q.map I₁ = gaussianReal 0 (t - s) :=
    Btheta_increment_map_eq_gaussianReal (X := X) (𝓕 := 𝓕) θ T hst (htu.trans (huv.trans hvT))
  have hlaw2 : Q.map I₂ = gaussianReal 0 (v - u) :=
    Btheta_increment_map_eq_gaussianReal (X := X) (𝓕 := 𝓕) θ T huv hvT
  -- Reduce independence to the factorisation of the joint characteristic function.
  rw [indepFun_iff_charFun_prod hI₁meas.aemeasurable hI₂meas.aemeasurable]
  intro w
  have hlin_meas : Measurable (fun ω ↦ w.ofLp.1 * I₁ ω + w.ofLp.2 * I₂ ω) :=
    (hI₁meas.const_mul _).add (hI₂meas.const_mul _)
  have hpair_meas : Measurable (fun ω ↦ (WithLp.toLp 2 (I₁ ω, I₂ ω) : WithLp 2 (ℝ × ℝ))) := by
    fun_prop
  -- LHS: the joint charFun is the charFun-at-1 of the Gaussian linear combination.
  have hLHS : charFun (Q.map (fun ω ↦ (WithLp.toLp 2 (I₁ ω, I₂ ω) : WithLp 2 (ℝ × ℝ)))) w
      = charFun (gaussianReal 0 (Real.toNNReal
          (w.ofLp.1 ^ 2 * ((t : ℝ) - (s : ℝ)) + w.ofLp.2 ^ 2 * ((v : ℝ) - (u : ℝ))))) 1 := by
    rw [← Btheta_linComb_map_eq_gaussianReal (P := P) (𝓕 := 𝓕) (X := X)
        θ w.ofLp.1 w.ofLp.2 T hst htu huv hvT]
    rw [charFun_apply, charFun_apply_real,
        integral_map hpair_meas.aemeasurable (by fun_prop),
        integral_map hlin_meas.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    simp only [WithLp.prod_inner_apply, RCLike.inner_apply, conj_trivial]
    congr 1
    push_cast
    ring
  have hσ2nn : (0 : ℝ) ≤ w.ofLp.1 ^ 2 * ((t : ℝ) - (s : ℝ)) + w.ofLp.2 ^ 2 * ((v : ℝ) - (u : ℝ)) :=
    add_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hst)))
      (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (by exact_mod_cast huv)))
  rw [hlaw1, hlaw2, charFun_gaussianReal, charFun_gaussianReal, hLHS, charFun_gaussianReal,
      Real.coe_toNNReal _ hσ2nn, NNReal.coe_sub hst, NNReal.coe_sub huv, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Constant-θ distributional Girsanov: `B^θ` is a `Q`-Brownian motion.** Packaging the three
defining properties under the Girsanov measure `Q = P.withDensity(exp(−θ X_T − ½θ² T))`:

* **zero start** — `B^θ_0 = X_0 + θ·0 = 0` a.e. `Q` (`X_0 ~ N(0,0) = δ₀` under `P`, and `Q ≪ P`);
* **Gaussian increments** — `B^θ_t − B^θ_s ~ N(0, t−s)` (`Btheta_increment_map_eq_gaussianReal`);
* **independent increments** — disjoint increments are `Q`-independent (`Btheta_increments_indepFun`).

This is the constant-θ half of Girsanov (`gir-thm-9.1.8`) in full — including the increment
independence that the marginal/increment laws alone do not give — reached on the existing tower
(Bayes engine + Wald exponentials + Mathlib's characteristic-function machinery), with no
adapted-integrand Itô formula. The general bounded-*adapted*-θ statement remains open (it needs
the adapted Itô formula, Route β). -/
theorem Btheta_isQBrownianMotion
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ : ℝ) (T : ℝ≥0) :
    (∀ᵐ ω ∂(P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))),
        X 0 ω + θ * ((0 : ℝ≥0) : ℝ) = 0)
      ∧ (∀ ⦃s t : ℝ≥0⦄, s ≤ t → t ≤ T →
          (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))).map
              (fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ))) = gaussianReal 0 (t - s))
      ∧ (∀ ⦃s t u v : ℝ≥0⦄, s ≤ t → t ≤ u → u ≤ v → v ≤ T →
          IndepFun (fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
              (fun ω ↦ (X v ω + θ * (v : ℝ)) - (X u ω + θ * (u : ℝ)))
            (P.withDensity fun ω ↦ ENNReal.ofReal
              (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2)))) := by
  set Q := P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
    with hQdef
  have hmeasX : ∀ w, Measurable (X w) := fun w ↦
    ((hX.stronglyAdapted w).mono (𝓕.le w)).measurable
  refine ⟨?_, fun s t hst htT ↦ Btheta_increment_map_eq_gaussianReal (X := X) (𝓕 := 𝓕) θ T hst htT,
    fun s t u v hst htu huv hvT ↦
      Btheta_increments_indepFun (X := X) (𝓕 := 𝓕) θ T hst htu huv hvT⟩
  -- Zero start: `X_0 = 0` a.e. `P` (its law is `N(0,0) = δ₀`), transported to `Q ≪ P`.
  have hX0P : P {ω | X 0 ω ≠ 0} = 0 := by
    have hmap := Measure.map_apply (μ := P) (hmeasX 0) (measurableSet_singleton (0 : ℝ)).compl
    rw [(hX.hasLaw_eval 0).map_eq, gaussianReal_zero_var,
        Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl] at hmap
    have hpre : X 0 ⁻¹' {(0 : ℝ)}ᶜ = {ω | X 0 ω ≠ 0} := by ext ω; simp [Set.mem_preimage]
    rw [hpre] at hmap
    simpa using hmap.symm
  have hQP : Q ≪ P := by rw [hQdef]; exact withDensity_absolutelyContinuous _ _
  filter_upwards [hQP.ae_le (ae_iff.mpr hX0P)] with ω hω
  simp [hω]

end MathFin
