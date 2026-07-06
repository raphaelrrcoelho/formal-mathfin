/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.BrownianMartingale

/-!
# The exponential characterization of a `Q`-Brownian motion

A process-agnostic packaging of the argument that turns an **exponential-martingale
hypothesis** into a full Brownian motion under a probability measure `Q`. Fix a
probability space `(Ω, Q)`, a filtration `𝓕`, a horizon `T`, and a real process
`Y : ℝ≥0 → Ω → ℝ` that is `𝓕`-adapted, starts at `0` (a.e. `Q`), and satisfies

  `for every a : ℝ, the process t ↦ exp(a·Y_t − ½a² t) is a Q-martingale on [0,T]`.

These three data are bundled as `IsExpQMartingale Q 𝓕 Y T`. The single theorem
`isQBrownianMotion_of_expMartingale` then reads off the three defining properties of a
`Q`-Brownian motion — zero start, `N(0,t−s)` increments, and independence of disjoint
increments — via Mathlib's characteristic-function machinery, *without* any reference to
the specific construction of `Y` or `Q`.

The mechanism is exactly the one that powered the constant-`θ` Girsanov file: the
exponential martingale at `s = 0` fixes the marginal moment-generating function
`𝔼_Q[exp(a·Y_t)] = exp(½a²t)`, hence the marginal law; the conditional form
`𝔼_Q[exp(a·(Y_t − Y_s))|𝓕_s] = exp(½a²(t−s))` is deterministic, giving Gaussian increments;
and freezing an earlier increment out of a later conditional expectation factorises the
joint moment-generating function, giving increment independence through
`indepFun_iff_charFun_prod`.

The value of the abstraction is coherence: the constant-`θ`, simple-`θ`, and (eventually)
continuous-`θ` Girsanov drift-corrected processes each need only supply their own
exponential martingale (via the Bayes change-of-measure engine) and then instantiate this
one theorem — no re-derivation of the ten-lemma characteristic-function chain.

## Main definitions and results

* `MathFin.IsExpQMartingale` — the hypothesis bundle (adapted, zero-start, exp-martingale).
* `MathFin.map_eq_gaussianReal_of_expMartingale` — the marginal law `Q.map Y_t = N(0,t)`.
* `MathFin.increment_map_eq_gaussianReal_of_expMartingale` — the increment law `N(0,t−s)`.
* `MathFin.increments_indepFun_of_expMartingale` — disjoint increments are `Q`-independent.
* `MathFin.isQBrownianMotion_of_expMartingale` — the three defining properties packaged.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The exponential-martingale characterization data.** A real process `Y` on the filtered
probability space `(Ω, 𝓕, Q)` that is `𝓕`-adapted, starts at `0` a.e. `Q`, and for which every
`t ↦ exp(a·Y_t − ½a² t)` is a `Q`-martingale on `[0,T]` (stated as the set-integral identity over
`𝓕_s`-sets). These are exactly the data output by the Bayes change-of-measure engine for a
drift-corrected process, and exactly the data consumed by `isQBrownianMotion_of_expMartingale`. -/
structure IsExpQMartingale (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    Prop where
  /-- `Y` is adapted to the filtration. -/
  adapted : ∀ u, StronglyMeasurable[(𝓕 u : MeasurableSpace Ω)] (Y u)
  /-- `Y` starts at `0` (a.e. `Q`). -/
  zero_start : Y 0 =ᵐ[Q] 0
  /-- For every `a`, `exp(a·Y_· − ½a²·)` is a `Q`-martingale on `[0,T]`. -/
  martingale : ∀ (a : ℝ) {s t : ℝ≥0}, s ≤ t → t ≤ T → ∀ {A : Set Ω},
    MeasurableSet[(𝓕 s : MeasurableSpace Ω)] A →
      ∫ ω in A, Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) ∂Q
        = ∫ ω in A, Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2) ∂Q

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ}
  {Y : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- **Marginal `Q`-MGF.** `𝔼_Q[exp(a·Y_t)] = exp(½ t a²)`: read off from the exponential
martingale at `s = 0` (the `Q`-integral of `exp(a·Y_t − ½a²t)` equals its value at `0`, which is
`exp(a·Y_0) = 1` a.e. since `Y_0 = 0`). -/
private theorem mgf_expY_eq (h : IsExpQMartingale Q 𝓕 Y T) {t : ℝ≥0} (htT : t ≤ T) (a : ℝ) :
    ∫ ω, Real.exp (a * Y t ω) ∂Q = Real.exp ((t : ℝ) * a ^ 2 / 2) := by
  have hbrick := h.martingale a (zero_le : (0 : ℝ≥0) ≤ t) htT (A := Set.univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at hbrick
  have hRHS : ∫ ω, Real.exp (a * Y 0 ω - a ^ 2 * ((0 : ℝ≥0) : ℝ) / 2) ∂Q = 1 := by
    have hae : (fun ω ↦ Real.exp (a * Y 0 ω - a ^ 2 * ((0 : ℝ≥0) : ℝ) / 2))
        =ᵐ[Q] fun _ ↦ (1 : ℝ) := by
      filter_upwards [h.zero_start] with ω hω; simp [hω]
    rw [integral_congr_ae hae]; simp
  rw [hRHS] at hbrick
  have hLHS : ∫ ω, Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) ∂Q
      = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * ∫ ω, Real.exp (a * Y t ω) ∂Q := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    show Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2)
        = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * Real.exp (a * Y t ω)
    rw [show a * Y t ω - a ^ 2 * (t : ℝ) / 2 = -(a ^ 2 * (t : ℝ) / 2) + a * Y t ω from by ring,
      Real.exp_add]
  rw [hLHS, mul_comm] at hbrick
  have hfac : Real.exp (-(a ^ 2 * (t : ℝ) / 2)) ≠ 0 := (Real.exp_pos _).ne'
  rw [(mul_eq_one_iff_eq_inv₀ hfac).mp hbrick, ← Real.exp_neg]
  congr 1; ring

/-- **Marginal law.** `Q.map Y_t = N(0, t)`: the `Q`-MGF matches the Gaussian MGF
(`mgf_expY_eq`), the integrable-exponential set is all of `ℝ` (transferred from the Gaussian), so
the complex-MGF machinery reads off the law. -/
theorem map_eq_gaussianReal_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {t : ℝ≥0}
    (htT : t ≤ T) : Q.map (Y t) = gaussianReal 0 t := by
  have hmeasY : Measurable (Y t) := ((h.adapted t).mono (𝓕.le t)).measurable
  have hmgf : mgf (Y t) Q = mgf id (gaussianReal 0 t) := by
    rw [mgf_id_gaussianReal]
    funext a
    show ∫ ω, Real.exp (a * Y t ω) ∂Q = Real.exp (0 * a + (t : ℝ) * a ^ 2 / 2)
    rw [mgf_expY_eq h htT a, zero_mul, zero_add]
  have hIESgauss : integrableExpSet id (gaussianReal 0 t) = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro a
    exact integrable_exp_mul_gaussianReal a
  have hIES : integrableExpSet (Y t) Q = Set.univ := by
    rw [integrableExpSet_eq_of_mgf hmgf, hIESgauss]
  have hset : {z : ℂ | z.re ∈ interior (integrableExpSet (Y t) Q)} = Set.univ := by
    rw [hIES, interior_univ]; ext z; simp
  have hcomplexeq : complexMGF (Y t) Q = complexMGF id (gaussianReal 0 t) := by
    funext z; exact eqOn_complexMGF_of_mgf hmgf (hset ▸ Set.mem_univ z)
  have hmap := Measure.ext_of_complexMGF_eq (μ := Q) (μ' := gaussianReal 0 t)
    hmeasY.aemeasurable aemeasurable_id hcomplexeq
  rwa [Measure.map_id] at hmap

/-- **Marginal `Q`-integrability.** `exp(a·Y_u)` is `Q`-integrable for `u ≤ T` — its law is
`N(0,u)` and the Gaussian MGF is finite. -/
private theorem integrable_expY (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {u : ℝ≥0} (huT : u ≤ T) :
    Integrable (fun ω ↦ Real.exp (a * Y u ω)) Q := by
  have hmeasY : Measurable (Y u) := ((h.adapted u).mono (𝓕.le u)).measurable
  rw [show (fun ω ↦ Real.exp (a * Y u ω)) = (fun x ↦ Real.exp (a * x)) ∘ (Y u) from rfl,
      ← integrable_map_measure (by fun_prop) hmeasY.aemeasurable,
      map_eq_gaussianReal_of_expMartingale h huT]
  exact integrable_exp_mul_gaussianReal a

/-- **Conditional exponential martingale.** `𝔼_Q[exp(a·Y_t − ½a² t)|𝓕_s] = exp(a·Y_s − ½a² s)`
a.e., the conditional form of the `martingale` field (its set-integral identity converted via
`ae_eq_condExp_of_forall_setIntegral_eq`). -/
private theorem condExp_expY (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t)
    (htT : t ≤ T) :
    Q[fun ω ↦ Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) | 𝓕 s]
      =ᵐ[Q] fun ω ↦ Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2) := by
  have hfint : ∀ u : ℝ≥0, u ≤ T →
      Integrable (fun ω ↦ Real.exp (a * Y u ω - a ^ 2 * (u : ℝ) / 2)) Q := by
    intro u huT
    have hfac : (fun ω ↦ Real.exp (a * Y u ω - a ^ 2 * (u : ℝ) / 2))
        = fun ω ↦ Real.exp (-(a ^ 2 * (u : ℝ) / 2)) * Real.exp (a * Y u ω) := by
      funext ω
      rw [show a * Y u ω - a ^ 2 * (u : ℝ) / 2 = -(a ^ 2 * (u : ℝ) / 2) + a * Y u ω from by ring,
        Real.exp_add]
    rw [hfac]; exact (integrable_expY h a huT).const_mul _
  have hsm : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)]
      (fun ω ↦ Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2)) := by
    have hcont : Continuous fun x : ℝ ↦ a * x - a ^ 2 * (s : ℝ) / 2 := by fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable (hcont.comp_stronglyMeasurable (h.adapted s))
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hfint t htT)
    (fun A _ _ ↦ (hfint s (hst.trans htT)).integrableOn) (fun A hA _ ↦ ?_)
    hsm.aestronglyMeasurable).symm
  exact (h.martingale a hst htT hA).symm

/-- **Conditional `Q`-MGF of the increment.** `𝔼_Q[exp(a·(Y_t − Y_s))|𝓕_s] = exp(½a²(t−s))` a.e.,
deterministic. Pull the `𝓕_s`-measurable factor `exp(½a²t − a·Y_s)` out of `condExp_expY`. -/
private theorem condExp_Y_increment (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Q[fun ω ↦ Real.exp (a * (Y t ω - Y s ω)) | 𝓕 s]
      =ᵐ[Q] fun _ ↦ Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
  have hmeasY : ∀ v, Measurable (Y v) := fun v ↦ ((h.adapted v).mono (𝓕.le v)).measurable
  set ft : Ω → ℝ := fun ω ↦ Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) with hftdef
  set gs : Ω → ℝ := fun ω ↦ Real.exp (a ^ 2 * (t : ℝ) / 2 - a * Y s ω) with hgsdef
  have hgs_sm : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)] gs := by
    have hcont : Continuous fun x : ℝ ↦ a ^ 2 * (t : ℝ) / 2 - a * x := by fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable (hcont.comp_stronglyMeasurable (h.adapted s))
  have hft_int : Integrable ft Q := by
    have hfac : ft = fun ω ↦ Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * Real.exp (a * Y t ω) := by
      funext ω
      show Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2)
          = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * Real.exp (a * Y t ω)
      rw [show a * Y t ω - a ^ 2 * (t : ℝ) / 2 = -(a ^ 2 * (t : ℝ) / 2) + a * Y t ω from by ring,
        Real.exp_add]
    rw [hfac]; exact (integrable_expY h a htT).const_mul _
  have hprod : (fun ω ↦ gs ω * ft ω) = fun ω ↦ Real.exp (a * (Y t ω - Y s ω)) := by
    funext ω; rw [hgsdef, hftdef, ← Real.exp_add]; congr 1; ring
  have hprod_int : Integrable (fun ω ↦ gs ω * ft ω) Q := by
    rw [hprod]
    have hbnd : Integrable (fun ω ↦ Real.exp (2 * a * Y t ω) + Real.exp (-2 * a * Y s ω)) Q :=
      (integrable_expY h (2 * a) htT).add (integrable_expY h (-2 * a) (hst.trans htT))
    refine Integrable.mono' hbnd
      (Real.measurable_exp.comp (((hmeasY t).sub (hmeasY s)).const_mul a)).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    have ep : Real.exp (2 * a * Y t ω) = Real.exp (a * Y t ω) ^ 2 := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have eq' : Real.exp (-2 * a * Y s ω) = Real.exp (-a * Y s ω) ^ 2 := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have eprod : Real.exp (a * (Y t ω - Y s ω))
        = Real.exp (a * Y t ω) * Real.exp (-a * Y s ω) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [ep, eq', eprod]
    nlinarith [sq_nonneg (Real.exp (a * Y t ω) - Real.exp (-a * Y s ω)),
      (Real.exp_pos (a * Y t ω)).le, (Real.exp_pos (-a * Y s ω)).le]
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := (𝓕 s : MeasurableSpace Ω))
    hgs_sm hprod_int hft_int
  have hcond := condExp_expY h a hst htT
  have hint_eq : (fun ω ↦ Real.exp (a * (Y t ω - Y s ω))) = gs * ft := hprod.symm
  rw [hint_eq]
  filter_upwards [hpull, hcond] with ω hp hc
  rw [hp, Pi.mul_apply,
    show (Q[ft | 𝓕 s]) ω = Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2) from hc,
    hgsdef, ← Real.exp_add]
  congr 1; ring

/-- **Unconditional `Q`-MGF of the increment.** `𝔼_Q[exp(a·(Y_t − Y_s))] = exp(½a²(t−s))` — the
tower property on the deterministic conditional MGF `condExp_Y_increment`. -/
private theorem Y_increment_mgf (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t)
    (htT : t ≤ T) :
    ∫ ω, Real.exp (a * (Y t ω - Y s ω)) ∂Q = Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
  rw [← integral_condExp (𝓕.le s), integral_congr_ae (condExp_Y_increment h a hst htT),
    integral_const, show Q.real Set.univ = 1 from by simp, one_smul]

/-- **Increment law.** `Q.map (Y_t − Y_s) = N(0, t−s)`, from the unconditional increment MGF
via the complex-MGF machinery. -/
theorem increment_map_eq_gaussianReal_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Q.map (fun ω ↦ Y t ω - Y s ω) = gaussianReal 0 (t - s) := by
  have hmeasY : ∀ v, Measurable (Y v) := fun v ↦ ((h.adapted v).mono (𝓕.le v)).measurable
  have hincmeas : Measurable (fun ω ↦ Y t ω - Y s ω) := (hmeasY t).sub (hmeasY s)
  have hmgf : mgf (fun ω ↦ Y t ω - Y s ω) Q = mgf id (gaussianReal 0 (t - s)) := by
    rw [mgf_id_gaussianReal]
    funext a
    show ∫ ω, Real.exp (a * (Y t ω - Y s ω)) ∂Q = Real.exp (0 * a + ((t - s : ℝ≥0) : ℝ) * a ^ 2 / 2)
    rw [Y_increment_mgf h a hst htT, NNReal.coe_sub hst]; congr 1; ring
  have hIESgauss : integrableExpSet id (gaussianReal 0 (t - s)) = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro a
    exact integrable_exp_mul_gaussianReal a
  have hIES : integrableExpSet (fun ω ↦ Y t ω - Y s ω) Q = Set.univ := by
    rw [integrableExpSet_eq_of_mgf hmgf, hIESgauss]
  have hset : {z : ℂ | z.re ∈ interior (integrableExpSet (fun ω ↦ Y t ω - Y s ω) Q)}
      = Set.univ := by rw [hIES, interior_univ]; ext z; simp
  have hcomplexeq :
      complexMGF (fun ω ↦ Y t ω - Y s ω) Q = complexMGF id (gaussianReal 0 (t - s)) := by
    funext z; exact eqOn_complexMGF_of_mgf hmgf (hset ▸ Set.mem_univ z)
  have hmap := Measure.ext_of_complexMGF_eq (μ := Q) (μ' := gaussianReal 0 (t - s))
    hincmeas.aemeasurable aemeasurable_id hcomplexeq
  rwa [Measure.map_id] at hmap

/-- **`Q`-integrability of the increment exponential.** `exp(c·(Y_t − Y_s))` is `Q`-integrable —
its law is `N(0,t−s)`. -/
private theorem integrable_exp_Y_increment (h : IsExpQMartingale Q 𝓕 Y T) (c : ℝ) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Integrable (fun ω ↦ Real.exp (c * (Y t ω - Y s ω))) Q := by
  have hmeasY : ∀ v, Measurable (Y v) := fun v ↦ ((h.adapted v).mono (𝓕.le v)).measurable
  have hincmeas : Measurable (fun ω ↦ Y t ω - Y s ω) := (hmeasY t).sub (hmeasY s)
  rw [show (fun ω ↦ Real.exp (c * (Y t ω - Y s ω)))
        = (fun x ↦ Real.exp (c * x)) ∘ (fun ω ↦ Y t ω - Y s ω) from rfl,
      ← integrable_map_measure (by fun_prop) hincmeas.aemeasurable,
      increment_map_eq_gaussianReal_of_expMartingale h hst htT]
  exact integrable_exp_mul_gaussianReal c

/-- **Joint `Q`-MGF of two disjoint increments factorises.** For `s ≤ t ≤ u ≤ v ≤ T`,
`𝔼_Q[exp(a·(Y_t − Y_s) + b·(Y_v − Y_u))] = exp(½a²(t−s))·exp(½b²(v−u))`. The earlier increment is
`𝓕_u`-measurable, so it factors out of `𝔼_Q[·|𝓕_u]`; the later increment's conditional MGF is the
deterministic `exp(½b²(v−u))`. -/
private theorem Y_increments_joint_mgf (h : IsExpQMartingale Q 𝓕 Y T) (a b : ℝ) {s t u v : ℝ≥0}
    (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ∫ ω, Real.exp (a * (Y t ω - Y s ω) + b * (Y v ω - Y u ω)) ∂Q
      = Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) * Real.exp (b ^ 2 * ((v : ℝ) - (u : ℝ)) / 2) := by
  have hmeasY : ∀ w, Measurable (Y w) := fun w ↦ ((h.adapted w).mono (𝓕.le w)).measurable
  set e1 : Ω → ℝ := fun ω ↦ Real.exp (a * (Y t ω - Y s ω)) with he1def
  set e2 : Ω → ℝ := fun ω ↦ Real.exp (b * (Y v ω - Y u ω)) with he2def
  have he1meas : Measurable e1 := by
    rw [he1def]; exact Real.measurable_exp.comp (((hmeasY t).sub (hmeasY s)).const_mul a)
  have he2meas : Measurable e2 := by
    rw [he2def]; exact Real.measurable_exp.comp (((hmeasY v).sub (hmeasY u)).const_mul b)
  have he1_sm : StronglyMeasurable[(𝓕 u : MeasurableSpace Ω)] e1 := by
    have hpair : StronglyMeasurable[(𝓕 u : MeasurableSpace Ω)] (fun ω ↦ (Y t ω, Y s ω)) :=
      ((h.adapted t).mono (𝓕.mono htu)).prodMk ((h.adapted s).mono (𝓕.mono (hst.trans htu)))
    have hcont : Continuous fun p : ℝ × ℝ ↦ Real.exp (a * (p.1 - p.2)) := by fun_prop
    exact hcont.comp_stronglyMeasurable hpair
  have he2_int : Integrable e2 Q := by
    rw [he2def]; exact integrable_exp_Y_increment h b huv hvT
  have hprod_int : Integrable (e1 * e2) Q := by
    have hbnd : Integrable (fun ω ↦ Real.exp (2 * a * (Y t ω - Y s ω))
        + Real.exp (2 * b * (Y v ω - Y u ω))) Q :=
      (integrable_exp_Y_increment h (2 * a) hst (htu.trans (huv.trans hvT))).add
        (integrable_exp_Y_increment h (2 * b) huv hvT)
    refine Integrable.mono' hbnd (he1meas.mul he2meas).aestronglyMeasurable ?_
    filter_upwards with ω
    simp only [Pi.mul_apply, he1def, he2def]
    rw [Real.norm_of_nonneg (by positivity)]
    have ep1 : Real.exp (2 * a * (Y t ω - Y s ω)) = Real.exp (a * (Y t ω - Y s ω)) ^ 2 := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have ep2 : Real.exp (2 * b * (Y v ω - Y u ω)) = Real.exp (b * (Y v ω - Y u ω)) ^ 2 := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    rw [ep1, ep2]
    nlinarith [sq_nonneg (Real.exp (a * (Y t ω - Y s ω)) - Real.exp (b * (Y v ω - Y u ω))),
      (Real.exp_pos (a * (Y t ω - Y s ω))).le, (Real.exp_pos (b * (Y v ω - Y u ω))).le]
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := (𝓕 u : MeasurableSpace Ω))
    he1_sm hprod_int he2_int
  have hcond2 := condExp_Y_increment h b huv hvT
  rw [← he2def] at hcond2
  have hsum_eq : (fun ω ↦ Real.exp (a * (Y t ω - Y s ω) + b * (Y v ω - Y u ω))) = e1 * e2 := by
    funext ω; simp only [he1def, he2def, Pi.mul_apply]; rw [← Real.exp_add]
  calc ∫ ω, Real.exp (a * (Y t ω - Y s ω) + b * (Y v ω - Y u ω)) ∂Q
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
          simp only [he1def]; rw [Y_increment_mgf h a hst (htu.trans (huv.trans hvT))]
        rw [he1int]

/-- **Any linear combination of two disjoint increments is Gaussian under `Q`.** For
`s ≤ t ≤ u ≤ v ≤ T` and reals `c, d`, the combination `c·(Y_t − Y_s) + d·(Y_v − Y_u)` has law
`N(0, c²(t−s) + d²(v−u))` under `Q`. Its `Q`-MGF is the `N(0,·)` MGF (`Y_increments_joint_mgf`);
the complex-MGF machinery reads off the law. -/
private theorem Y_linComb_map_eq_gaussianReal (h : IsExpQMartingale Q 𝓕 Y T) (c d : ℝ)
    {s t u v : ℝ≥0} (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    Q.map (fun ω ↦ c * (Y t ω - Y s ω) + d * (Y v ω - Y u ω))
      = gaussianReal 0
          (Real.toNNReal (c ^ 2 * ((t : ℝ) - (s : ℝ)) + d ^ 2 * ((v : ℝ) - (u : ℝ)))) := by
  have hmeasY : ∀ w, Measurable (Y w) := fun w ↦ ((h.adapted w).mono (𝓕.le w)).measurable
  set σ2 : ℝ := c ^ 2 * ((t : ℝ) - (s : ℝ)) + d ^ 2 * ((v : ℝ) - (u : ℝ)) with hσ2def
  have hσ2nonneg : 0 ≤ σ2 :=
    add_nonneg (mul_nonneg (sq_nonneg c) (sub_nonneg.mpr (by exact_mod_cast hst)))
      (mul_nonneg (sq_nonneg d) (sub_nonneg.mpr (by exact_mod_cast huv)))
  have hlcmeas : Measurable (fun ω ↦ c * (Y t ω - Y s ω) + d * (Y v ω - Y u ω)) :=
    (((hmeasY t).sub (hmeasY s)).const_mul c).add (((hmeasY v).sub (hmeasY u)).const_mul d)
  have hmgf : mgf (fun ω ↦ c * (Y t ω - Y s ω) + d * (Y v ω - Y u ω)) Q
      = mgf id (gaussianReal 0 σ2.toNNReal) := by
    rw [mgf_id_gaussianReal]
    funext r
    show ∫ ω, Real.exp (r * (c * (Y t ω - Y s ω) + d * (Y v ω - Y u ω))) ∂Q
        = Real.exp (0 * r + (σ2.toNNReal : ℝ) * r ^ 2 / 2)
    have hjoint := Y_increments_joint_mgf h (r * c) (r * d) hst htu huv hvT
    rw [show (∫ ω, Real.exp (r * (c * (Y t ω - Y s ω) + d * (Y v ω - Y u ω))) ∂Q)
          = ∫ ω, Real.exp ((r * c) * (Y t ω - Y s ω) + (r * d) * (Y v ω - Y u ω)) ∂Q from by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_); ring_nf,
      hjoint, Real.coe_toNNReal σ2 hσ2nonneg, ← Real.exp_add]
    congr 1; rw [hσ2def]; ring
  have hIESgauss : integrableExpSet id (gaussianReal 0 σ2.toNNReal) = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro r
    exact integrable_exp_mul_gaussianReal r
  have hIES : integrableExpSet (fun ω ↦ c * (Y t ω - Y s ω) + d * (Y v ω - Y u ω)) Q = Set.univ := by
    rw [integrableExpSet_eq_of_mgf hmgf, hIESgauss]
  have hset : {z : ℂ | z.re ∈ interior (integrableExpSet
      (fun ω ↦ c * (Y t ω - Y s ω) + d * (Y v ω - Y u ω)) Q)} = Set.univ := by
    rw [hIES, interior_univ]; ext z; simp
  have hcomplexeq : complexMGF (fun ω ↦ c * (Y t ω - Y s ω) + d * (Y v ω - Y u ω)) Q
      = complexMGF id (gaussianReal 0 σ2.toNNReal) := by
    funext z; exact eqOn_complexMGF_of_mgf hmgf (hset ▸ Set.mem_univ z)
  have hmap := Measure.ext_of_complexMGF_eq (μ := Q) (μ' := gaussianReal 0 σ2.toNNReal)
    hlcmeas.aemeasurable aemeasurable_id hcomplexeq
  rwa [Measure.map_id] at hmap

/-- **Disjoint increments are `Q`-independent.** For `s ≤ t ≤ u ≤ v ≤ T`, `Y_t − Y_s` and
`Y_v − Y_u` are independent under `Q`. By `indepFun_iff_charFun_prod`, independence is the
factorisation of the joint characteristic function; the joint charFun is the charFun-at-`1` of the
Gaussian linear combination (`Y_linComb_map_eq_gaussianReal`), which equals the product of the two
marginal Gaussian characteristic functions. -/
theorem increments_indepFun_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {s t u v : ℝ≥0}
    (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    IndepFun (fun ω ↦ Y t ω - Y s ω) (fun ω ↦ Y v ω - Y u ω) Q := by
  have hmeasY : ∀ w, Measurable (Y w) := fun w ↦ ((h.adapted w).mono (𝓕.le w)).measurable
  set I₁ : Ω → ℝ := fun ω ↦ Y t ω - Y s ω with hI₁def
  set I₂ : Ω → ℝ := fun ω ↦ Y v ω - Y u ω with hI₂def
  have hI₁meas : Measurable I₁ := (hmeasY t).sub (hmeasY s)
  have hI₂meas : Measurable I₂ := (hmeasY v).sub (hmeasY u)
  have hlaw1 : Q.map I₁ = gaussianReal 0 (t - s) :=
    increment_map_eq_gaussianReal_of_expMartingale h hst (htu.trans (huv.trans hvT))
  have hlaw2 : Q.map I₂ = gaussianReal 0 (v - u) :=
    increment_map_eq_gaussianReal_of_expMartingale h huv hvT
  rw [indepFun_iff_charFun_prod hI₁meas.aemeasurable hI₂meas.aemeasurable]
  intro w
  have hlin_meas : Measurable (fun ω ↦ w.ofLp.1 * I₁ ω + w.ofLp.2 * I₂ ω) :=
    (hI₁meas.const_mul _).add (hI₂meas.const_mul _)
  have hpair_meas : Measurable (fun ω ↦ (WithLp.toLp 2 (I₁ ω, I₂ ω) : WithLp 2 (ℝ × ℝ))) := by
    fun_prop
  have hLHS : charFun (Q.map (fun ω ↦ (WithLp.toLp 2 (I₁ ω, I₂ ω) : WithLp 2 (ℝ × ℝ)))) w
      = charFun (gaussianReal 0 (Real.toNNReal
          (w.ofLp.1 ^ 2 * ((t : ℝ) - (s : ℝ)) + w.ofLp.2 ^ 2 * ((v : ℝ) - (u : ℝ))))) 1 := by
    rw [← Y_linComb_map_eq_gaussianReal h w.ofLp.1 w.ofLp.2 hst htu huv hvT]
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

/-- **The exponential characterization of a `Q`-Brownian motion.** From the exponential-martingale
data `IsExpQMartingale Q 𝓕 Y T`, the process `Y` has the three defining properties of a Brownian
motion under `Q` on `[0,T]`:

* **zero start** — `Y_0 = 0` a.e. `Q`;
* **Gaussian increments** — `Y_t − Y_s ~ N(0, t−s)` (`increment_map_eq_gaussianReal_of_expMartingale`);
* **independent increments** — disjoint increments are `Q`-independent (`increments_indepFun_of_expMartingale`).

Process- and measure-agnostic: any drift-corrected Girsanov process supplying its own exponential
martingale (via the Bayes engine) is a `Q`-Brownian motion by one application of this theorem. -/
theorem isQBrownianMotion_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) :
    (∀ᵐ ω ∂Q, Y 0 ω = 0)
      ∧ (∀ ⦃s t : ℝ≥0⦄, s ≤ t → t ≤ T →
          Q.map (fun ω ↦ Y t ω - Y s ω) = gaussianReal 0 (t - s))
      ∧ (∀ ⦃s t u v : ℝ≥0⦄, s ≤ t → t ≤ u → u ≤ v → v ≤ T →
          IndepFun (fun ω ↦ Y t ω - Y s ω) (fun ω ↦ Y v ω - Y u ω) Q) := by
  refine ⟨?_, fun s t hst htT ↦ increment_map_eq_gaussianReal_of_expMartingale h hst htT,
    fun s t u v hst htu huv hvT ↦ increments_indepFun_of_expMartingale h hst htu huv hvT⟩
  filter_upwards [h.zero_start] with ω hω
  simpa using hω

end MathFin
