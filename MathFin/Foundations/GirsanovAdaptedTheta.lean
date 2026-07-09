/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.GirsanovSimpleTheta
public import MathFin.Foundations.ItoIntegralRiemannBridgeAdapted
public import MathFin.Foundations.DriftRiemannConvergence
public import MathFin.Foundations.UnifIntegrableL2

/-! # Continuous bounded-adapted-θ Girsanov — `B^θ` is a `Q`-Brownian motion (α4 assembly)

Route-α, brick α4 (`docs/plans/2026-07-06-girsanov-track-alpha.md`). Closes the general bounded
**adapted continuous** Girsanov theorem by passing the simple-θ result
(`isExpQMartingale_BthetaSimple`) to the limit. For a bounded (`|θ| ≤ C`) adapted (`𝓕_t`-measurable
in each `t`) continuous (every path `s ↦ θ_s ω`) market price of risk `θ`, under
`Q = μ.withDensity Z_T` with the Doléans density `Z_T = exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds)` the
drift-corrected process `B^θ_u = B_u + ∫₀ᵘθ ds` is a genuine `Q`-Brownian motion.

The route is **spine-free**: rather than build a continuous Doléans stochastic exponential and prove
it is a martingale (a Novikov-flavoured crux), we pass the *simple* exponential-martingale identity to
the limit. The `unifPart`-partition approximants `c⁽ⁿ⁾_i = θ(tᵢ)` give, per `n`, the simple identity
`∫_A exp(a·Yⁿ − ½)·Z⁽ⁿ⁾_T dμ = …`; the stochastic exponent `Wⁿ = ∑θ(tᵢ)ΔBᵢ → ∫θdB` in `L²` (brick b),
the drift parts converge everywhere (the drift Riemann lemmas), and the set-integral limit goes
through the a.e.-subsequence endpoint `tendsto_setIntegral_of_subseq_ae_of_sq_bound`. Then
`isQBrownianMotion_of_expMartingale` reads off the `Q`-Brownian properties.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal MathFin.QuadraticVariationL2
open scoped MeasureTheory NNReal ENNReal
open ItoIntegralL2 ItoIntegralBrownian ItoIntegralCLM ItoIntegralRiemannBridge ItoIsometryAdapted

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- The pathwise linear drift `∫₀ᵘ θ_s ds` (against `timeMeasure`). -/
noncomputable def contDrift (θ : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Set.Ioc (0 : ℝ≥0) u, θ s ω ∂timeMeasure

/-- The drift-corrected process `B^θ_u = B_u + ∫₀ᵘ θ ds`. -/
noncomputable def BthetaCont (B θ : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  B u ω + contDrift θ u ω

/-- The continuous Doléans density in `exp`-form `exp(−W − ½∫₀ᵀθ²ds)`, parameterized by the Itô
integral `W = ∫₀ᵀθ dB` (a chosen `Lp`-representative). -/
noncomputable def contDoleansExp (W : Ω → ℝ) (θ : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-W ω - 2⁻¹ * ∫ s in Set.Ioc (0 : ℝ≥0) T, (θ s ω) ^ 2 ∂timeMeasure)

omit mΩ in
lemma contDoleansExp_pos (W : Ω → ℝ) (θ : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    0 < contDoleansExp W θ T ω := Real.exp_pos _

omit [IsProbabilityMeasure μ] in
/-- `TendstoInMeasure` only sees a.e.-classes of the sequence: replacing each `f n` by an
a.e.-equal `f' n` preserves convergence in measure. -/
lemma tendstoInMeasure_congr_left {E : Type*} [MetricSpace E] {f f' : ℕ → Ω → E} {g : Ω → E}
    (h : ∀ n, f n =ᵐ[μ] f' n) (hfg : TendstoInMeasure μ f atTop g) :
    TendstoInMeasure μ f' atTop g := by
  intro ε hε
  refine (hfg ε hε).congr fun n => measure_congr ?_
  rw [Filter.eventuallyEq_set]
  filter_upwards [h n] with x hx
  simp only [hx]

variable (hB : IsPreBrownianReal B μ)

/-- The Itô integral `∫₀ᵀ θ dB` as a genuine function — the chosen `Lp`-representative of
`itoIntegralCLM_T (processToLp θ)`. -/
noncomputable def itoIntCont (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    Ω → ℝ :=
  ⇑(itoIntegralCLM_T hB T hBmeas (processToLp (μ := μ) T hBmeas hadap hcont hbdd))

include hB in
/-- **The Riemann–Itô sums converge in measure to `∫₀ᵀ θ dB`.** From the `L²` convergence
(`itoIntegralCLM_T_of_bdd_adapted_cont`, brick b) via `tendstoInMeasure_of_tendsto_Lp`, transported
from the `Lp` classes to the genuine `riemannσ` functions. -/
lemma tendstoInMeasure_riemannσ (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    TendstoInMeasure μ (fun n => riemannσ (B := B) θ T n) atTop
      (itoIntCont hB hBmeas hadap hcont hbdd T) := by
  refine tendstoInMeasure_congr_left
    (fun n => (memLp_riemannσ hB hBmeas hadap hbdd T n).coeFn_toLp) ?_
  exact tendstoInMeasure_of_tendsto_Lp
    (itoIntegralCLM_T_of_bdd_adapted_cont hB hBmeas hadap hcont hbdd T)

omit hB in
/-- The discrete quadratic-drift Riemann sum `∑_{k<n} θ(tₖ)²·(t_{k+1} − tₖ)` (the drift half of the
approximant Doléans exponent), → `∫₀ᵀθ²ds` by `tendsto_driftSq_riemannSum`. -/
noncomputable def driftSqSum (θ : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n,
    (θ (unifPart T n k) ω) ^ 2 * ((unifPart T n (k + 1) : ℝ) - (unifPart T n k : ℝ))

omit hB mΩ in
/-- **The approximant Doléans density in `exp`-form.** The simple Doléans density `E^{−c⁽ⁿ⁾}_T` for
the `unifPart`-partition multipliers `c⁽ⁿ⁾_i = θ(tᵢ)` is `exp(−Wⁿ − ½·driftSqSumⁿ)`, where
`Wⁿ = riemannσ = ∑θ(tᵢ)ΔBᵢ` is the Riemann–Itô sum and `driftSqSumⁿ = ∑θ(tᵢ)²Δτᵢ` the quadratic
drift. All partition points `≤ T`, so the clamps `min(tⱼ,T)` in `simpleDoleansExp_eq_exp_sum` drop. -/
lemma simpleDoleansExp_neg_eq {θ : ℝ≥0 → Ω → ℝ} (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    simpleDoleansExp (X := B) (unifPart T n) (fun i ω => -(θ (unifPart T n i) ω)) n T ω
      = Real.exp (-riemannσ (B := B) θ T n ω - 2⁻¹ * driftSqSum θ T n ω) := by
  rw [simpleDoleansExp_eq_exp_sum]
  congr 1
  rw [riemannσ, driftSqSum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : k + 1 ≤ n := Finset.mem_range.mp hk
  rw [min_eq_left (unifPart_le_T hk1), min_eq_left (unifPart_le_T (le_of_lt (Finset.mem_range.mp hk)))]
  ring

include hB in
/-- **The subsequence-extraction core.** Since `riemannσ → ∫₀ᵀθdB` in measure
(`tendstoInMeasure_riemannσ`), every subsequence `ns` has a further subsequence `ms` along which the
Riemann–Itô sums converge a.e. This is the single stochastic input to the a.e.-subsequence route:
the drift parts converge everywhere, so along `ms` the whole Doléans / drift-corrected exponential
converges a.e. -/
lemma exists_subseq_riemannσ_ae (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ ω ∂μ, Tendsto (fun k => riemannσ (B := B) θ T (ns (ms k)) ω)
      atTop (𝓝 (itoIntCont hB hBmeas hadap hcont hbdd T ω)) := by
  have hconv : TendstoInMeasure μ (fun k => riemannσ (B := B) θ T (ns k)) atTop
      (itoIntCont hB hBmeas hadap hcont hbdd T) :=
    fun ε hε => (tendstoInMeasure_riemannσ hB hBmeas hadap hcont hbdd T ε hε).comp hns
  obtain ⟨ms, hms, hae⟩ := hconv.exists_seq_tendsto_ae
  exact ⟨ms, hms, hae⟩

omit hB mΩ in
/-- The quadratic drift is bounded by `C²·T`: each `θ(tₖ)² ≤ C²` and the cell lengths telescope to
`unifPart T n n ≤ T`. -/
lemma driftSqSum_le {θ : ℝ≥0 → Ω → ℝ} {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ)
    (ω : Ω) : driftSqSum θ T n ω ≤ C ^ 2 * (T : ℝ) := by
  have hC0 : (0 : ℝ) ≤ C := (abs_nonneg _).trans (hbdd 0 ω)
  rw [driftSqSum]
  calc ∑ k ∈ Finset.range n,
          (θ (unifPart T n k) ω) ^ 2 * ((unifPart T n (k + 1) : ℝ) - (unifPart T n k : ℝ))
      ≤ ∑ k ∈ Finset.range n, C ^ 2 * ((unifPart T n (k + 1) : ℝ) - (unifPart T n k : ℝ)) := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_
          (sub_nonneg.mpr (by exact_mod_cast unifPart_mono T n (Nat.le_succ k)))
        rw [← sq_abs (θ (unifPart T n k) ω)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbdd _ ω) 2
    _ = C ^ 2 * ((unifPart T n n : ℝ) - (unifPart T n 0 : ℝ)) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => (unifPart T n k : ℝ))]
    _ ≤ C ^ 2 * (T : ℝ) := by
        rw [show unifPart T n 0 = 0 by simp [unifPart], NNReal.coe_zero, sub_zero]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast unifPart_le_T (le_refl n)) (sq_nonneg C)

omit hB mΩ in
/-- **Scaled Doléans exponent.** For a scalar `r`, `E^{rθ⁽ⁿ⁾}_T = exp(r·Wⁿ − ½r²·driftSqSumⁿ)` — the
generalization of `simpleDoleansExp_neg_eq` (which is the `r = −1` case). Powers the `Lᵖ`-bounds:
`(Zⁿ)^p = E^{−pθ}·exp(½p(p−1)·driftSqSumⁿ)`. -/
lemma simpleDoleansExp_scaled_eq {θ : ℝ≥0 → Ω → ℝ} (r : ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    simpleDoleansExp (X := B) (unifPart T n) (fun i ω => r * θ (unifPart T n i) ω) n T ω
      = Real.exp (r * riemannσ (B := B) θ T n ω - 2⁻¹ * r ^ 2 * driftSqSum θ T n ω) := by
  rw [simpleDoleansExp_eq_exp_sum]
  congr 1
  rw [riemannσ, driftSqSum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : k + 1 ≤ n := Finset.mem_range.mp hk
  rw [min_eq_left (unifPart_le_T hk1), min_eq_left (unifPart_le_T (le_of_lt (Finset.mem_range.mp hk)))]
  ring

include hB in
/-- **Uniform `L²` bound on the approximant densities.** `∫ (Zⁿ_T)² ≤ exp(C²T)`, uniform in `n`.
Pointwise `(Zⁿ_T)² = E^{−2c⁽ⁿ⁾}_T · exp(driftSqSumⁿ) ≤ exp(C²T)·E^{−2c⁽ⁿ⁾}_T` (from the scaled
identity + `driftSqSum_le`), and `E^{−2c⁽ⁿ⁾}` is a positive density with `∫ = 1`
(`simpleDoleansExp_integral_eq_one`). This feeds the a.e.-subsequence engine (the `L²` bound the
linchpin needs) for the density limit `Zⁿ → Z`. -/
lemma sq_integral_Zn_le (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    ∫ ω, (simpleDoleansExp (X := B) (unifPart T n) (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ^ 2 ∂μ
      ≤ Real.exp (C ^ 2 * (T : ℝ)) := by
  haveI : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  have hd2m : ∀ i, StronglyMeasurable[(natFiltration hBmeas (unifPart T n i) : MeasurableSpace Ω)]
      (fun ω => (-2 : ℝ) * θ (unifPart T n i) ω) := fun i => (hadap (unifPart T n i)).const_mul (-2)
  have hd2b : ∀ i ω, |(-2 : ℝ) * θ (unifPart T n i) ω| ≤ 2 * C := fun i ω => by
    rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left (hbdd _ ω) (by norm_num)
  have hmean : ∫ ω, simpleDoleansExp (X := B) (unifPart T n)
      (fun i ω => (-2 : ℝ) * θ (unifPart T n i) ω) n T ω ∂μ = 1 :=
    simpleDoleansExp_integral_eq_one (X := B) (𝓕 := natFiltration hBmeas) (unifPart T n)
      (unifPart_mono T n) _ hd2m hd2b n T
  have hint2 : Integrable (fun ω => simpleDoleansExp (X := B) (unifPart T n)
      (fun i ω => (-2 : ℝ) * θ (unifPart T n i) ω) n T ω) μ :=
    (simpleDoleansExp_isMartingale (X := B) (𝓕 := natFiltration hBmeas) (P := μ) (unifPart T n)
      (unifPart_mono T n) _ hd2m hd2b n).integrable T
  have hpt : ∀ ω,
      (simpleDoleansExp (X := B) (unifPart T n) (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ^ 2
        ≤ Real.exp (C ^ 2 * (T : ℝ)) * simpleDoleansExp (X := B) (unifPart T n)
            (fun i ω => (-2 : ℝ) * θ (unifPart T n i) ω) n T ω := by
    intro ω
    rw [simpleDoleansExp_neg_eq, simpleDoleansExp_scaled_eq, pow_two, ← Real.exp_add,
      ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := driftSqSum_le hbdd T n ω
    nlinarith [this]
  calc ∫ ω, (simpleDoleansExp (X := B) (unifPart T n) (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ^ 2 ∂μ
      ≤ ∫ ω, Real.exp (C ^ 2 * (T : ℝ)) * simpleDoleansExp (X := B) (unifPart T n)
          (fun i ω => (-2 : ℝ) * θ (unifPart T n i) ω) n T ω ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) (hint2.const_mul _)
          (ae_of_all _ hpt)
    _ = Real.exp (C ^ 2 * (T : ℝ)) := by rw [integral_const_mul, hmean, mul_one]

include hB in
/-- **The density's a.e.-subsequence convergence.** Every subsequence `ns` has a further one `ms`
along which `Zⁿ_T → Z_T` a.e., where `Z_T = contDoleansExp (∫θdB)`. Composes `exp` over the a.e.
convergence of `Wⁿ = riemannσ` (`exists_subseq_riemannσ_ae`) and the everywhere convergence of the
quadratic drift (`tendsto_driftSq_riemannSum`). -/
lemma tendsto_Zn_ae_subseq (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, ∀ᵐ ω ∂μ, Tendsto (fun k =>
        simpleDoleansExp (X := B) (unifPart T (ns (ms k)))
          (fun i ω => -(θ (unifPart T (ns (ms k)) i) ω)) (ns (ms k)) T ω) atTop
      (𝓝 (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω)) := by
  obtain ⟨ms, hms, hae⟩ := exists_subseq_riemannσ_ae hB hBmeas hadap hcont hbdd T ns hns
  refine ⟨ms, ?_⟩
  filter_upwards [hae] with ω hω
  have hnsms : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hms.tendsto_atTop
  have hdrift : Tendsto (fun k => driftSqSum θ T (ns (ms k)) ω) atTop
      (𝓝 (∫ s in Set.Ioc (0 : ℝ≥0) T, (θ s ω) ^ 2 ∂timeMeasure)) :=
    (tendsto_driftSq_riemannSum hcont hbdd T ω).comp hnsms
  have hexp := (Real.continuous_exp.tendsto _).comp ((hω.neg).sub (hdrift.const_mul 2⁻¹))
  exact hexp.congr fun k => (simpleDoleansExp_neg_eq T (ns (ms k)) ω).symm

include hB in
/-- The approximant density is in `L²` (the same `E^{−2c}` domination as `sq_integral_Zn_le`). -/
lemma memLp_Zn_two (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    MemLp (fun ω => simpleDoleansExp (X := B) (unifPart T n)
      (fun i ω => -(θ (unifPart T n i) ω)) n T ω) 2 μ := by
  haveI : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  have hd1m : ∀ i, StronglyMeasurable[(natFiltration hBmeas (unifPart T n i) : MeasurableSpace Ω)]
      (fun ω => -(θ (unifPart T n i) ω)) := fun i => (hadap (unifPart T n i)).neg
  have hd1b : ∀ i ω, |(-(θ (unifPart T n i) ω))| ≤ C := fun i ω => by simpa using hbdd (unifPart T n i) ω
  have hZmeas : Measurable (fun ω => simpleDoleansExp (X := B) (unifPart T n)
      (fun i ω => -(θ (unifPart T n i) ω)) n T ω) :=
    (((simpleDoleansExp_isMartingale (X := B) (𝓕 := natFiltration hBmeas) (P := μ) (unifPart T n)
      (unifPart_mono T n) _ hd1m hd1b n).1 T).mono ((natFiltration hBmeas).le T)).measurable
  have hd2m : ∀ i, StronglyMeasurable[(natFiltration hBmeas (unifPart T n i) : MeasurableSpace Ω)]
      (fun ω => (-2 : ℝ) * θ (unifPart T n i) ω) := fun i => (hadap (unifPart T n i)).const_mul (-2)
  have hd2b : ∀ i ω, |(-2 : ℝ) * θ (unifPart T n i) ω| ≤ 2 * C := fun i ω => by
    rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left (hbdd _ ω) (by norm_num)
  have hint2 : Integrable (fun ω => simpleDoleansExp (X := B) (unifPart T n)
      (fun i ω => (-2 : ℝ) * θ (unifPart T n i) ω) n T ω) μ :=
    (simpleDoleansExp_isMartingale (X := B) (𝓕 := natFiltration hBmeas) (P := μ) (unifPart T n)
      (unifPart_mono T n) _ hd2m hd2b n).integrable T
  rw [memLp_two_iff_integrable_sq hZmeas.aestronglyMeasurable]
  refine (hint2.const_mul (Real.exp (C ^ 2 * (T : ℝ)))).mono'
    (hZmeas.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), simpleDoleansExp_neg_eq, simpleDoleansExp_scaled_eq, pow_two,
    ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [driftSqSum_le hbdd T n ω])

include hB in
/-- Unit `P`-mean of the approximant density: `∫ Zⁿ_T = 1`. -/
lemma integral_Zn_eq_one (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    ∫ ω, simpleDoleansExp (X := B) (unifPart T n) (fun i ω => -(θ (unifPart T n i) ω)) n T ω ∂μ = 1 := by
  haveI : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  exact simpleDoleansExp_integral_eq_one (X := B) (𝓕 := natFiltration hBmeas) (unifPart T n)
    (unifPart_mono T n) _ (fun i => (hadap _).neg) (fun i ω => by simpa using hbdd (unifPart T n i) ω) n T

include hB in
/-- Measurability of the approximant density. -/
lemma measurable_Zn (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    Measurable (fun ω => simpleDoleansExp (X := B) (unifPart T n)
      (fun i ω => -(θ (unifPart T n i) ω)) n T ω) := by
  haveI : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  exact (((simpleDoleansExp_isMartingale (X := B) (𝓕 := natFiltration hBmeas) (P := μ) (unifPart T n)
    (unifPart_mono T n) _ (fun i => (hadap _).neg) (fun i ω => by simpa using hbdd (unifPart T n i) ω)
    n).1 T).mono ((natFiltration hBmeas).le T)).measurable

include hB in
/-- Integrability of the approximant density (it is a martingale). -/
lemma integrable_Zn (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun ω => simpleDoleansExp (X := B) (unifPart T n)
      (fun i ω => -(θ (unifPart T n i) ω)) n T ω) μ := by
  haveI : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  exact (simpleDoleansExp_isMartingale (X := B) (𝓕 := natFiltration hBmeas) (P := μ) (unifPart T n)
    (unifPart_mono T n) _ (fun i => (hadap _).neg) (fun i ω => by simpa using hbdd (unifPart T n i) ω)
    n).integrable T

include hB in
/-- **The continuous density is in `L¹`.** By Fatou on an a.e.-convergent approximant subsequence:
`∫⁻ ‖Z_T‖ₑ ≤ liminf ∫⁻ ‖Zⁿ‖ₑ = liminf (∫ Zⁿ) = 1 < ∞`. -/
lemma memLp_ZT_one (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    MemLp (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T) 1 μ := by
  obtain ⟨ms, hae⟩ := tendsto_Zn_ae_subseq hB hBmeas hadap hcont hbdd T id tendsto_id
  have hZTmeas : AEStronglyMeasurable
      (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (measurable_Zn hB hBmeas hadap hbdd T (ms k)).aestronglyMeasurable) hae
  refine ⟨hZTmeas, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hone : ∀ k, ∫⁻ ω, ‖simpleDoleansExp (X := B) (unifPart T (ms k))
      (fun i ω => -(θ (unifPart T (ms k) i) ω)) (ms k) T ω‖ₑ ∂μ = 1 := by
    intro k
    have hpos := fun ω => (simpleDoleansExp_pos (X := B) (unifPart T (ms k))
      (fun i ω => -(θ (unifPart T (ms k) i) ω)) (ms k) T ω).le
    calc ∫⁻ ω, ‖_‖ₑ ∂μ
        = ∫⁻ ω, ENNReal.ofReal (simpleDoleansExp (X := B) (unifPart T (ms k))
            (fun i ω => -(θ (unifPart T (ms k) i) ω)) (ms k) T ω) ∂μ := by
          refine lintegral_congr fun ω => ?_
          rw [Real.enorm_eq_ofReal (hpos ω)]
      _ = ENNReal.ofReal (∫ ω, simpleDoleansExp (X := B) (unifPart T (ms k))
            (fun i ω => -(θ (unifPart T (ms k) i) ω)) (ms k) T ω ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal
            (integrable_Zn hB hBmeas hadap hbdd T (ms k)) (ae_of_all _ hpos)).symm
      _ = 1 := by rw [integral_Zn_eq_one hB hBmeas hadap hbdd T (ms k)]; simp
  have hfatou : ∫⁻ ω, ‖contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω‖ₑ ∂μ ≤ 1 := by
    have hlim : (fun ω => ‖contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω‖ₑ)
        =ᵐ[μ] fun ω => Filter.liminf (fun k => ‖simpleDoleansExp (X := B) (unifPart T (ms k))
          (fun i ω => -(θ (unifPart T (ms k) i) ω)) (ms k) T ω‖ₑ) atTop := by
      filter_upwards [hae] with ω hω
      exact (hω.enorm.liminf_eq).symm
    rw [lintegral_congr_ae hlim]
    refine (lintegral_liminf_le
      (fun k => (measurable_Zn hB hBmeas hadap hbdd T (ms k)).enorm)).trans ?_
    simp only [hone, liminf_const, le_refl]
  exact lt_of_le_of_lt hfatou one_lt_top

include hB in
/-- **Unit mean of the continuous density: `∫ Z_T = 1`.** The a.e.-subsequence engine gives
`∫ Zⁿ → ∫ Z_T`, and `∫ Zⁿ = 1` (`integral_Zn_eq_one`), so the limit is `1`. -/
lemma integral_ZT_eq_one (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    ∫ ω, contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω ∂μ = 1 := by
  have hlim := tendsto_setIntegral_of_subseq_ae_of_sq_bound
    (fun n => memLp_Zn_two hB hBmeas hadap hbdd T n)
    (M := Real.exp (C ^ 2 * (T : ℝ))) (fun n => sq_integral_Zn_le hB hBmeas hadap hbdd T n)
    (memLp_ZT_one hB hBmeas hadap hcont hbdd T)
    (fun ns hns => tendsto_Zn_ae_subseq hB hBmeas hadap hcont hbdd T ns hns) Set.univ
  simp only [setIntegral_univ, integral_Zn_eq_one hB hBmeas hadap hbdd T] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

include hB in
/-- **The continuous Girsanov measure is a probability measure.** `Q = μ.withDensity(Z_T)` with the
positive, unit-mean, `L¹` density `Z_T`. -/
lemma isProbabilityMeasure_contGirsanov (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    IsProbabilityMeasure (μ.withDensity fun ω =>
      ENNReal.ofReal (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((memLp_ZT_one hB hBmeas hadap hcont hbdd T).integrable le_rfl)
      (ae_of_all _ fun ω => (contDoleansExp_pos _ _ _ _).le),
    integral_ZT_eq_one hB hBmeas hadap hcont hbdd T, ENNReal.ofReal_one]

include hB in
/-- **Uniform `L⁴` bound on the approximant densities.** `∫ (Zⁿ_T)⁴ ≤ exp(6C²T)`, uniform in `n`
(the 4th-moment analogue of `sq_integral_Zn_le`): `(Zⁿ)⁴ = E^{−4c}·exp(6·driftSqSumⁿ)`. Needed for
the Hölder step of the mixed-time product `L²` bound. -/
lemma quad_integral_Zn_le (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    ∫ ω, (simpleDoleansExp (X := B) (unifPart T n) (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ^ 4 ∂μ
      ≤ Real.exp (6 * C ^ 2 * (T : ℝ)) := by
  haveI : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  have hd4m : ∀ i, StronglyMeasurable[(natFiltration hBmeas (unifPart T n i) : MeasurableSpace Ω)]
      (fun ω => (-4 : ℝ) * θ (unifPart T n i) ω) := fun i => (hadap (unifPart T n i)).const_mul (-4)
  have hd4b : ∀ i ω, |(-4 : ℝ) * θ (unifPart T n i) ω| ≤ 4 * C := fun i ω => by
    rw [abs_mul, show |(-4 : ℝ)| = 4 by norm_num]
    exact mul_le_mul_of_nonneg_left (hbdd _ ω) (by norm_num)
  have hmean : ∫ ω, simpleDoleansExp (X := B) (unifPart T n)
      (fun i ω => (-4 : ℝ) * θ (unifPart T n i) ω) n T ω ∂μ = 1 :=
    simpleDoleansExp_integral_eq_one (X := B) (𝓕 := natFiltration hBmeas) (unifPart T n)
      (unifPart_mono T n) _ hd4m hd4b n T
  have hint4 : Integrable (fun ω => simpleDoleansExp (X := B) (unifPart T n)
      (fun i ω => (-4 : ℝ) * θ (unifPart T n i) ω) n T ω) μ :=
    (simpleDoleansExp_isMartingale (X := B) (𝓕 := natFiltration hBmeas) (P := μ) (unifPart T n)
      (unifPart_mono T n) _ hd4m hd4b n).integrable T
  have hpt : ∀ ω,
      (simpleDoleansExp (X := B) (unifPart T n) (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ^ 4
        ≤ Real.exp (6 * C ^ 2 * (T : ℝ)) * simpleDoleansExp (X := B) (unifPart T n)
            (fun i ω => (-4 : ℝ) * θ (unifPart T n i) ω) n T ω := by
    intro ω
    rw [simpleDoleansExp_neg_eq, simpleDoleansExp_scaled_eq, ← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by push_cast; nlinarith [driftSqSum_le hbdd T n ω])
  calc ∫ ω, (simpleDoleansExp (X := B) (unifPart T n) (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ^ 4 ∂μ
      ≤ ∫ ω, Real.exp (6 * C ^ 2 * (T : ℝ)) * simpleDoleansExp (X := B) (unifPart T n)
          (fun i ω => (-4 : ℝ) * θ (unifPart T n i) ω) n T ω ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity) (hint4.const_mul _)
          (ae_of_all _ hpt)
    _ = Real.exp (6 * C ^ 2 * (T : ℝ)) := by rw [integral_const_mul, hmean, mul_one]

omit hB mΩ in
/-- The `unifPart` simple drift is bounded by `C·u` for `u ≤ T` (all `n`; `n = 0` is the empty sum). -/
lemma simpleDriftUnif_abs_le {θ : ℝ≥0 → Ω → ℝ} {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0)
    {u : ℝ≥0} (huT : u ≤ T) (n : ℕ) (ω : Ω) :
    |simpleDrift (unifPart T n) (fun i ω => θ (unifPart T n i) ω) n u ω| ≤ C * (u : ℝ) := by
  have hC0 : (0 : ℝ) ≤ C := (abs_nonneg _).trans (hbdd 0 ω)
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simp only [simpleDrift, Finset.range_zero, Finset.sum_empty, abs_zero]
    exact mul_nonneg hC0 u.coe_nonneg
  · have hlast : unifPart T n n = T := by
      rw [unifPart, div_self (Nat.cast_ne_zero.mpr hn.ne'), one_mul]
    exact simpleDrift_abs_le (unifPart_mono T n) (by simp [unifPart]) (fun i ω => hbdd _ ω) n
      (huT.trans_eq hlast.symm) ω

include hB in
omit [IsProbabilityMeasure μ] in
/-- **Uniform `L⁴` bound on the drift-corrected exponentials `Dⁿ_u`.** `∫ (Dⁿ_u)⁴ ≤ exp(4|a|CT)·M₄`
with `M₄ = ∫ exp(4a·B_u)` (the Gaussian 4·`a`-MGF, `n`-independent): `(Dⁿ_u)⁴ = exp(4a·Yⁿ_u − 2a²u) ≤
exp(4|a|CT)·exp(4a·B_u)` since the drift is bounded and `−2a²u ≤ 0`. -/
lemma quad_integral_Dn_le (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (a : ℝ) (T : ℝ≥0) {u : ℝ≥0} (huT : u ≤ T) (n : ℕ) :
    ∫ ω, (Real.exp (a * (B u ω + simpleDrift (unifPart T n)
        (fun i ω => θ (unifPart T n i) ω) n u ω) - a ^ 2 * (u : ℝ) / 2)) ^ 4 ∂μ
      ≤ Real.exp (4 * |a| * C * (T : ℝ)) * ∫ ω, Real.exp (4 * a * B u ω) ∂μ := by
  haveI hFB : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  have hMGF : Integrable (fun ω => Real.exp (4 * a * B u ω)) μ :=
    integrable_exp_mul_of_hasLaw (hFB.hasLaw_eval u) (4 * a)
  have hmeasD : Measurable fun ω => Real.exp (a * (B u ω + simpleDrift (unifPart T n)
      (fun i ω => θ (unifPart T n i) ω) n u ω) - a ^ 2 * (u : ℝ) / 2) := by
    have : Measurable fun ω => simpleDrift (unifPart T n)
        (fun i ω => θ (unifPart T n i) ω) n u ω := by
      unfold simpleDrift
      exact Finset.measurable_sum _ fun i _ =>
        ((hadap (unifPart T n i)).mono ((natFiltration hBmeas).le _)).measurable.mul_const _
    fun_prop (disch := exact this)
  have hpt : ∀ ω, (Real.exp (a * (B u ω + simpleDrift (unifPart T n)
      (fun i ω => θ (unifPart T n i) ω) n u ω) - a ^ 2 * (u : ℝ) / 2)) ^ 4
        ≤ Real.exp (4 * |a| * C * (T : ℝ)) * Real.exp (4 * a * B u ω) := by
    intro ω
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h4 : a * simpleDrift (unifPart T n) (fun i ω => θ (unifPart T n i) ω) n u ω
        ≤ |a| * (C * (T : ℝ)) :=
      calc a * simpleDrift (unifPart T n) (fun i ω => θ (unifPart T n i) ω) n u ω
          ≤ |a * simpleDrift (unifPart T n) (fun i ω => θ (unifPart T n i) ω) n u ω| := le_abs_self _
        _ = |a| * |simpleDrift (unifPart T n) (fun i ω => θ (unifPart T n i) ω) n u ω| := abs_mul _ _
        _ ≤ |a| * (C * (u : ℝ)) :=
            mul_le_mul_of_nonneg_left (simpleDriftUnif_abs_le hbdd T huT n ω) (abs_nonneg a)
        _ ≤ |a| * (C * (T : ℝ)) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by exact_mod_cast huT)
              ((abs_nonneg _).trans (hbdd 0 ω))) (abs_nonneg a)
    push_cast
    nlinarith [h4, sq_nonneg a, u.coe_nonneg]
  calc ∫ ω, (Real.exp (a * (B u ω + simpleDrift (unifPart T n)
        (fun i ω => θ (unifPart T n i) ω) n u ω) - a ^ 2 * (u : ℝ) / 2)) ^ 4 ∂μ
      ≤ ∫ ω, Real.exp (4 * |a| * C * (T : ℝ)) * Real.exp (4 * a * B u ω) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity) (hMGF.const_mul _)
          (ae_of_all _ hpt)
    _ = Real.exp (4 * |a| * C * (T : ℝ)) * ∫ ω, Real.exp (4 * a * B u ω) ∂μ := integral_const_mul _ _

/-! ### The continuous drift `∫₀ᵘθds`: basics and `𝓕`-adaptedness -/

omit hB mΩ in
/-- The continuous drift vanishes at time `0` (the domain `(0,0]` is empty). -/
lemma contDrift_zero (θ : ℝ≥0 → Ω → ℝ) (ω : Ω) : contDrift θ 0 ω = 0 := by
  simp [contDrift]

omit hB mΩ in
/-- **The continuous drift is bounded: `|∫₀ᵘθds| ≤ C·u`.** As the everywhere-limit of the clamped
`unifPart` drift sums (`tendsto_riemannSum_setIntegral_clamp`), each bounded by `C·u`
(`simpleDriftUnif_abs_le`). -/
lemma contDrift_abs_le {θ : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ}
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) {u : ℝ≥0} (huT : u ≤ T) (ω : Ω) :
    |contDrift θ u ω| ≤ C * (u : ℝ) := by
  refine le_of_tendsto
    ((tendsto_riemannSum_setIntegral_clamp (hcont ω) (fun s => hbdd s ω) T huT).abs) ?_
  exact Filter.Eventually.of_forall fun n => simpleDriftUnif_abs_le hbdd T huT n ω

omit hB in
/-- **The continuous drift is `𝓕_u`-adapted (all `u`).** The everywhere-limit of the
`𝓕_u`-strongly-measurable left-endpoint Riemann sums over the partition of `[0,u]` itself
(`tendsto_riemannSum_setIntegral`); each partition point `≤ u` so its `θ`-value is `𝓕_u`-measurable. -/
lemma stronglyMeasurable_contDrift (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (u : ℝ≥0) :
    StronglyMeasurable[(natFiltration hBmeas u : MeasurableSpace Ω)] (contDrift θ u) := by
  have hsm : ∀ n, StronglyMeasurable[(natFiltration hBmeas u : MeasurableSpace Ω)]
      (fun ω => ∑ k ∈ Finset.range n, θ (unifPart u n k) ω
        * ((unifPart u n (k + 1) : ℝ) - (unifPart u n k : ℝ))) := by
    intro n
    rw [show (fun ω => ∑ k ∈ Finset.range n, θ (unifPart u n k) ω
          * ((unifPart u n (k + 1) : ℝ) - (unifPart u n k : ℝ)))
        = ∑ k ∈ Finset.range n, (fun ω => θ (unifPart u n k) ω
          * ((unifPart u n (k + 1) : ℝ) - (unifPart u n k : ℝ)))
        from by funext ω; simp only [Finset.sum_apply]]
    refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
    exact ((hadap (unifPart u n k)).mono ((natFiltration hBmeas).mono
      (unifPart_le_T (le_of_lt (Finset.mem_range.mp hk))))).mul_const _
  exact stronglyMeasurable_of_tendsto atTop hsm
    (tendsto_pi_nhds.mpr fun ω => tendsto_riemannSum_setIntegral (hcont ω) (fun s => hbdd s ω) u)

omit hB [IsProbabilityMeasure μ] in
/-- **The withDensity transport `∫_A h dQ = ∫_A h·Z dμ`** for a nonnegative `AEStronglyMeasurable`
density `Z` (the continuous case has only an `Lp`-representative density, so the `AEMeasurable`
variant is needed; the simple case's measurable density is a special case). -/
lemma setIntegral_withDensity_ofReal {Z : Ω → ℝ} (hZ : AEStronglyMeasurable Z μ)
    (hZpos : ∀ ω, 0 ≤ Z ω) (h : Ω → ℝ) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω in A, h ω ∂(μ.withDensity fun ω => ENNReal.ofReal (Z ω)) = ∫ ω in A, h ω * Z ω ∂μ := by
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hZ.aemeasurable.ennreal_ofReal.restrict
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) h hA]
  refine setIntegral_congr_ae hA (ae_of_all _ fun ω _ => ?_)
  rw [ENNReal.toReal_ofReal (hZpos ω), smul_eq_mul, mul_comm]

/-! ### The mixed-time product `fⁿ = Dⁿ_u · Zⁿ_T`: uniform `L²` bound (route A)

The exp-martingale identity, transported to `μ`, is `∫_A Dⁿ_u · Zⁿ_T dμ`, a product of the
drift-corrected exponential at horizon `u` and the density at `T`. The a.e.-subsequence engine needs
`fⁿ ∈ L²` with a uniform second-moment bound. Via AM–GM `2·D²·Z² ≤ D⁴ + Z⁴`, the bound reduces to
the two `n`-independent `L⁴` estimates `quad_integral_Dn_le` and `quad_integral_Zn_le`. -/

omit hB in
/-- Measurability of the approximant drift-corrected exponential `Dⁿ_u`. -/
lemma measurable_Dn (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (a : ℝ) (T u : ℝ≥0) (n : ℕ) :
    Measurable (fun ω => Real.exp (a * (B u ω + simpleDrift (unifPart T n)
      (fun i ω => θ (unifPart T n i) ω) n u ω) - a ^ 2 * (u : ℝ) / 2)) := by
  have hsd : Measurable fun ω => simpleDrift (unifPart T n)
      (fun i ω => θ (unifPart T n i) ω) n u ω := by
    unfold simpleDrift
    exact Finset.measurable_sum _ fun i _ =>
      ((hadap (unifPart T n i)).mono ((natFiltration hBmeas).le _)).measurable.mul_const _
  fun_prop (disch := exact hsd)

include hB in
/-- **Uniform `L⁴`-integrability of the approximant density `Zⁿ_T`** (the domination behind
`quad_integral_Zn_le`): `(Zⁿ)⁴ ≤ exp(6C²T)·E^{−4c⁽ⁿ⁾}`, an integrable simple density. -/
lemma integrable_Zn_four (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun ω => (simpleDoleansExp (X := B) (unifPart T n)
      (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ^ 4) μ := by
  haveI : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  have hd4m : ∀ i, StronglyMeasurable[(natFiltration hBmeas (unifPart T n i) : MeasurableSpace Ω)]
      (fun ω => (-4 : ℝ) * θ (unifPart T n i) ω) := fun i => (hadap (unifPart T n i)).const_mul (-4)
  have hd4b : ∀ i ω, |(-4 : ℝ) * θ (unifPart T n i) ω| ≤ 4 * C := fun i ω => by
    rw [abs_mul, show |(-4 : ℝ)| = 4 by norm_num]
    exact mul_le_mul_of_nonneg_left (hbdd _ ω) (by norm_num)
  have hint4 : Integrable (fun ω => simpleDoleansExp (X := B) (unifPart T n)
      (fun i ω => (-4 : ℝ) * θ (unifPart T n i) ω) n T ω) μ :=
    (simpleDoleansExp_isMartingale (X := B) (𝓕 := natFiltration hBmeas) (P := μ) (unifPart T n)
      (unifPart_mono T n) _ hd4m hd4b n).integrable T
  refine (hint4.const_mul (Real.exp (6 * C ^ 2 * (T : ℝ)))).mono'
    ((measurable_Zn hB hBmeas hadap hbdd T n).pow_const 4).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity), simpleDoleansExp_neg_eq, simpleDoleansExp_scaled_eq,
    ← Real.exp_nat_mul, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by push_cast; nlinarith [driftSqSum_le hbdd T n ω])

include hB in
omit [IsProbabilityMeasure μ] in
/-- **Uniform `L⁴`-integrability of the drift-corrected exponential `Dⁿ_u`** (the domination behind
`quad_integral_Dn_le`): `(Dⁿ_u)⁴ ≤ exp(4|a|CT)·exp(4a·B_u)`, an integrable Gaussian MGF. -/
lemma integrable_Dn_four (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (a : ℝ) (T : ℝ≥0) {u : ℝ≥0} (huT : u ≤ T) (n : ℕ) :
    Integrable (fun ω => (Real.exp (a * (B u ω + simpleDrift (unifPart T n)
      (fun i ω => θ (unifPart T n i) ω) n u ω) - a ^ 2 * (u : ℝ) / 2)) ^ 4) μ := by
  haveI hFB : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  have hMGF : Integrable (fun ω => Real.exp (4 * a * B u ω)) μ :=
    integrable_exp_mul_of_hasLaw (hFB.hasLaw_eval u) (4 * a)
  refine (hMGF.const_mul (Real.exp (4 * |a| * C * (T : ℝ)))).mono'
    ((measurable_Dn hBmeas hadap a T u n).pow_const 4).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity), ← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h4 : a * simpleDrift (unifPart T n) (fun i ω => θ (unifPart T n i) ω) n u ω
      ≤ |a| * (C * (T : ℝ)) :=
    calc a * simpleDrift (unifPart T n) (fun i ω => θ (unifPart T n i) ω) n u ω
        ≤ |a * simpleDrift (unifPart T n) (fun i ω => θ (unifPart T n i) ω) n u ω| := le_abs_self _
      _ = |a| * |simpleDrift (unifPart T n) (fun i ω => θ (unifPart T n i) ω) n u ω| := abs_mul _ _
      _ ≤ |a| * (C * (T : ℝ)) := mul_le_mul_of_nonneg_left
          ((simpleDriftUnif_abs_le hbdd T huT n ω).trans (mul_le_mul_of_nonneg_left
            (by exact_mod_cast huT) ((abs_nonneg _).trans (hbdd 0 ω)))) (abs_nonneg a)
  push_cast
  nlinarith [h4, sq_nonneg a, u.coe_nonneg]

omit hB mΩ in
/-- Pointwise AM–GM `(x·y)² ≤ ½(x⁴ + y⁴)` — the domination behind the mixed-product `L²` bound. -/
lemma sq_mul_le_half_add_pow4 (x y : ℝ) : (x * y) ^ 2 ≤ 2⁻¹ * (x ^ 4 + y ^ 4) := by
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y)]

include hB in
/-- **The mixed-time product is in `L²`**, via the AM–GM domination `(Dⁿ·Zⁿ)² ≤ ½(Dⁿ⁴ + Zⁿ⁴)`. -/
lemma memLp_fn_two (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (a : ℝ) (T : ℝ≥0) {u : ℝ≥0} (huT : u ≤ T) (n : ℕ) :
    MemLp (fun ω => Real.exp (a * (B u ω + simpleDrift (unifPart T n)
        (fun i ω => θ (unifPart T n i) ω) n u ω) - a ^ 2 * (u : ℝ) / 2)
      * simpleDoleansExp (X := B) (unifPart T n) (fun i ω => -(θ (unifPart T n i) ω)) n T ω) 2 μ := by
  have hDmeas := measurable_Dn hBmeas hadap a T u n
  have hZmeas := measurable_Zn hB hBmeas hadap hbdd T n
  rw [memLp_two_iff_integrable_sq (hDmeas.mul hZmeas).aestronglyMeasurable]
  refine (((integrable_Dn_four hB hBmeas hadap hbdd a T huT n).add
    (integrable_Zn_four hB hBmeas hadap hbdd T n)).const_mul 2⁻¹).mono'
    ((hDmeas.mul hZmeas).pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω =>
      (Real.norm_of_nonneg (sq_nonneg _)).le.trans (sq_mul_le_half_add_pow4 _ _))

include hB in
/-- **Uniform second-moment bound on the mixed-time product**, `n`-independent:
`∫ (Dⁿ_u·Zⁿ_T)² ≤ ½(exp(4|a|CT)·𝔼[exp(4a·B_u)] + exp(6C²T))`. Feeds the a.e.-subsequence engine. -/
lemma sq_integral_fn_le (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (a : ℝ) (T : ℝ≥0) {u : ℝ≥0} (huT : u ≤ T) (n : ℕ) :
    ∫ ω, (Real.exp (a * (B u ω + simpleDrift (unifPart T n)
        (fun i ω => θ (unifPart T n i) ω) n u ω) - a ^ 2 * (u : ℝ) / 2)
      * simpleDoleansExp (X := B) (unifPart T n) (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ^ 2 ∂μ
      ≤ 2⁻¹ * (Real.exp (4 * |a| * C * (T : ℝ)) * (∫ ω, Real.exp (4 * a * B u ω) ∂μ)
          + Real.exp (6 * C ^ 2 * (T : ℝ))) := by
  have hD4 := integrable_Dn_four hB hBmeas hadap hbdd a T huT n
  have hZ4 := integrable_Zn_four hB hBmeas hadap hbdd T n
  calc ∫ ω, (Real.exp (a * (B u ω + simpleDrift (unifPart T n)
          (fun i ω => θ (unifPart T n i) ω) n u ω) - a ^ 2 * (u : ℝ) / 2)
        * simpleDoleansExp (X := B) (unifPart T n) (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ^ 2 ∂μ
      ≤ ∫ ω, 2⁻¹ * ((Real.exp (a * (B u ω + simpleDrift (unifPart T n)
          (fun i ω => θ (unifPart T n i) ω) n u ω) - a ^ 2 * (u : ℝ) / 2)) ^ 4
          + (simpleDoleansExp (X := B) (unifPart T n)
              (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ^ 4) ∂μ := by
        exact integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
          ((hD4.add hZ4).const_mul _) (ae_of_all _ fun ω => sq_mul_le_half_add_pow4 _ _)
    _ = 2⁻¹ * ((∫ ω, (Real.exp (a * (B u ω + simpleDrift (unifPart T n)
          (fun i ω => θ (unifPart T n i) ω) n u ω) - a ^ 2 * (u : ℝ) / 2)) ^ 4 ∂μ)
          + ∫ ω, (simpleDoleansExp (X := B) (unifPart T n)
              (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ^ 4 ∂μ) := by
        rw [integral_const_mul, integral_add hD4 hZ4]
    _ ≤ 2⁻¹ * (Real.exp (4 * |a| * C * (T : ℝ)) * (∫ ω, Real.exp (4 * a * B u ω) ∂μ)
          + Real.exp (6 * C ^ 2 * (T : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add (quad_integral_Dn_le hB hBmeas hadap hbdd a T huT n)
          (quad_integral_Zn_le hB hBmeas hadap hbdd T n)) (by norm_num)

/-! ### The limit `g = Dᵤ·Z_T`: `L¹`-membership and `fⁿ → g` a.e. -/

include hB in
/-- **The continuous density is in `L²`.** By Fatou on the squares of an a.e.-convergent approximant
subsequence: `∫⁻ (Z_T)² ≤ liminf ∫⁻ (Zⁿ)² = liminf ∫ (Zⁿ)² ≤ exp(C²T) < ∞` (`sq_integral_Zn_le`). -/
lemma memLp_ZT_two (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    MemLp (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T) 2 μ := by
  obtain ⟨ms, hae⟩ := tendsto_Zn_ae_subseq hB hBmeas hadap hcont hbdd T id tendsto_id
  simp only [id_eq] at hae
  have hZTmeas : AEStronglyMeasurable
      (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (measurable_Zn hB hBmeas hadap hbdd T (ms k)).aestronglyMeasurable) hae
  rw [memLp_two_iff_integrable_sq hZTmeas]
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun k => ((measurable_Zn hB hBmeas hadap hbdd T (ms k)).pow_const 2).aestronglyMeasurable)
    (by filter_upwards [hae] with ω hω; exact hω.pow 2), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hsqbnd : ∀ k, ∫⁻ ω, ‖(simpleDoleansExp (X := B) (unifPart T (ms k))
      (fun i ω => -(θ (unifPart T (ms k) i) ω)) (ms k) T ω) ^ 2‖ₑ ∂μ
      ≤ ENNReal.ofReal (Real.exp (C ^ 2 * (T : ℝ))) := by
    intro k
    have hint_sq := (memLp_two_iff_integrable_sq
      (measurable_Zn hB hBmeas hadap hbdd T (ms k)).aestronglyMeasurable).mp
        (memLp_Zn_two hB hBmeas hadap hbdd T (ms k))
    calc ∫⁻ ω, ‖(simpleDoleansExp (X := B) (unifPart T (ms k))
            (fun i ω => -(θ (unifPart T (ms k) i) ω)) (ms k) T ω) ^ 2‖ₑ ∂μ
        = ∫⁻ ω, ENNReal.ofReal ((simpleDoleansExp (X := B) (unifPart T (ms k))
            (fun i ω => -(θ (unifPart T (ms k) i) ω)) (ms k) T ω) ^ 2) ∂μ :=
          lintegral_congr fun ω => by rw [Real.enorm_eq_ofReal (sq_nonneg _)]
      _ = ENNReal.ofReal (∫ ω, (simpleDoleansExp (X := B) (unifPart T (ms k))
            (fun i ω => -(θ (unifPart T (ms k) i) ω)) (ms k) T ω) ^ 2 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hint_sq (ae_of_all _ fun ω => sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal (Real.exp (C ^ 2 * (T : ℝ))) :=
          ENNReal.ofReal_le_ofReal (sq_integral_Zn_le hB hBmeas hadap hbdd T (ms k))
  have hlim : (fun ω => ‖(contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω) ^ 2‖ₑ)
      =ᵐ[μ] fun ω => Filter.liminf (fun k => ‖(simpleDoleansExp (X := B) (unifPart T (ms k))
        (fun i ω => -(θ (unifPart T (ms k) i) ω)) (ms k) T ω) ^ 2‖ₑ) atTop := by
    filter_upwards [hae] with ω hω
    exact ((hω.pow 2).enorm.liminf_eq).symm
  rw [lintegral_congr_ae hlim]
  have hbound : ∫⁻ ω, Filter.liminf (fun k => ‖(simpleDoleansExp (X := B) (unifPart T (ms k))
        (fun i ω => -(θ (unifPart T (ms k) i) ω)) (ms k) T ω) ^ 2‖ₑ) atTop ∂μ
      ≤ ENNReal.ofReal (Real.exp (C ^ 2 * (T : ℝ))) :=
    (lintegral_liminf_le (fun k => ((measurable_Zn hB hBmeas hadap hbdd T (ms k)).pow_const 2).enorm)).trans
      ((liminf_le_liminf (Filter.Eventually.of_forall hsqbnd)).trans (liminf_const _).le)
  exact hbound.trans_lt ENNReal.ofReal_lt_top

include hB in
omit [IsProbabilityMeasure μ] in
/-- **The drift-corrected exponential `Dᵤ = exp(a·B^θ_u − ½a²u)` is in `L²`.** Domination
`(Dᵤ)² ≤ exp(2|a|CT)·exp(2a·B_u)`, an integrable Gaussian MGF (`contDrift` bounded, `−a²u ≤ 0`). -/
lemma memLp_contD_two (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (a : ℝ)
    (T : ℝ≥0) {u : ℝ≥0} (huT : u ≤ T) :
    MemLp (fun ω => Real.exp (a * BthetaCont B θ u ω - a ^ 2 * (u : ℝ) / 2)) 2 μ := by
  haveI hFB : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  have hMGF : Integrable (fun ω => Real.exp (2 * a * B u ω)) μ :=
    integrable_exp_mul_of_hasLaw (hFB.hasLaw_eval u) (2 * a)
  have hBt : Measurable (fun ω => BthetaCont B θ u ω) := by
    unfold BthetaCont
    exact (hBmeas u).add ((stronglyMeasurable_contDrift hBmeas hadap hcont hbdd u).mono
      ((natFiltration hBmeas).le u)).measurable
  have hmeas : Measurable (fun ω => Real.exp (a * BthetaCont B θ u ω - a ^ 2 * (u : ℝ) / 2)) := by
    fun_prop (disch := exact hBt)
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
  refine (hMGF.const_mul (Real.exp (2 * |a| * C * (T : ℝ)))).mono'
    (hmeas.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), ← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hcd : a * contDrift θ u ω ≤ |a| * (C * (T : ℝ)) :=
    calc a * contDrift θ u ω ≤ |a * contDrift θ u ω| := le_abs_self _
      _ = |a| * |contDrift θ u ω| := abs_mul _ _
      _ ≤ |a| * (C * (T : ℝ)) := mul_le_mul_of_nonneg_left
          ((contDrift_abs_le hcont hbdd T huT ω).trans (mul_le_mul_of_nonneg_left
            (by exact_mod_cast huT) ((abs_nonneg _).trans (hbdd 0 ω)))) (abs_nonneg a)
  simp only [BthetaCont]
  push_cast
  nlinarith [hcd, sq_nonneg a, u.coe_nonneg]

include hB in
/-- **The limit `g = Dᵤ·Z_T` is in `L¹`.** `L²·L² ⊆ L¹` (`MemLp.mul`): `Dᵤ ∈ L²` (`memLp_contD_two`)
and `Z_T ∈ L²` (`memLp_ZT_two`). -/
lemma memLp_g_one (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (a : ℝ)
    (T : ℝ≥0) {u : ℝ≥0} (huT : u ≤ T) :
    MemLp (fun ω => Real.exp (a * BthetaCont B θ u ω - a ^ 2 * (u : ℝ) / 2)
      * contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω) 1 μ :=
  (memLp_ZT_two hB hBmeas hadap hcont hbdd T).mul
    (memLp_contD_two hB hBmeas hadap hcont hbdd a T huT)

include hB in
/-- **The mixed-time product converges to `g` a.e. along a subsequence (the engine's `hsub`).** Every
subsequence `ns` has a further one `ms` along which `Dⁿ_u·Zⁿ_T → Dᵤ·Z_T` a.e.: the density part
converges a.e. (`exists_subseq_riemannσ_ae` + `simpleDoleansExp_neg_eq`), the drift part converges
everywhere (`tendsto_riemannSum_setIntegral_clamp`), and the product of a.e. limits is a.e. -/
lemma tendsto_fn_ae_subseq (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (a : ℝ)
    (T : ℝ≥0) {u : ℝ≥0} (huT : u ≤ T) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, ∀ᵐ ω ∂μ, Tendsto (fun k => Real.exp (a * (B u ω + simpleDrift
        (unifPart T (ns (ms k))) (fun i ω => θ (unifPart T (ns (ms k)) i) ω) (ns (ms k)) u ω)
        - a ^ 2 * (u : ℝ) / 2)
      * simpleDoleansExp (X := B) (unifPart T (ns (ms k)))
          (fun i ω => -(θ (unifPart T (ns (ms k)) i) ω)) (ns (ms k)) T ω) atTop
      (𝓝 (Real.exp (a * BthetaCont B θ u ω - a ^ 2 * (u : ℝ) / 2)
        * contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω)) := by
  obtain ⟨ms, hms, hae⟩ := exists_subseq_riemannσ_ae hB hBmeas hadap hcont hbdd T ns hns
  refine ⟨ms, ?_⟩
  filter_upwards [hae] with ω hω
  have hnsms : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hms.tendsto_atTop
  have hZ : Tendsto (fun k => simpleDoleansExp (X := B) (unifPart T (ns (ms k)))
      (fun i ω => -(θ (unifPart T (ns (ms k)) i) ω)) (ns (ms k)) T ω) atTop
      (𝓝 (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω)) := by
    have hdriftSq : Tendsto (fun k => driftSqSum θ T (ns (ms k)) ω) atTop
        (𝓝 (∫ s in Set.Ioc (0 : ℝ≥0) T, (θ s ω) ^ 2 ∂timeMeasure)) :=
      (tendsto_driftSq_riemannSum hcont hbdd T ω).comp hnsms
    exact ((Real.continuous_exp.tendsto _).comp ((hω.neg).sub (hdriftSq.const_mul 2⁻¹))).congr
      fun k => (simpleDoleansExp_neg_eq T (ns (ms k)) ω).symm
  have hD : Tendsto (fun k => Real.exp (a * (B u ω + simpleDrift (unifPart T (ns (ms k)))
      (fun i ω => θ (unifPart T (ns (ms k)) i) ω) (ns (ms k)) u ω) - a ^ 2 * (u : ℝ) / 2)) atTop
      (𝓝 (Real.exp (a * BthetaCont B θ u ω - a ^ 2 * (u : ℝ) / 2))) := by
    have hdrift : Tendsto (fun k => simpleDrift (unifPart T (ns (ms k)))
        (fun i ω => θ (unifPart T (ns (ms k)) i) ω) (ns (ms k)) u ω) atTop
        (𝓝 (contDrift θ u ω)) :=
      (tendsto_riemannSum_setIntegral_clamp (hcont ω) (fun s => hbdd s ω) T huT).comp hnsms
    exact (Real.continuous_exp.tendsto _).comp (((hdrift.const_add (B u ω)).const_mul a).sub_const _)
  exact hD.mul hZ

/-! ### The continuous exponential-martingale data and the `Q`-Brownian conclusion -/

include hB in
/-- **Continuous bounded-adapted-θ exponential-martingale data.** For a bounded (`|θ| ≤ C`) adapted
continuous `θ`, under `Q = μ.withDensity(Z_T)` with the Doléans density
`Z_T = exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds)`, the drift-corrected process `B^θ_u = B_u + ∫₀ᵘθ ds` is `𝓕`-adapted,
starts at `0` a.e. `Q`, and every `exp(a·B^θ − ½a²·)` is a `Q`-martingale on `[0,T]`. The martingale
field is the limit of the simple-θ identity (`isExpQMartingale_BthetaSimple` on the `unifPart`
approximants): transported to `μ`, both sides pass through the a.e.-subsequence engine
(`tendsto_setIntegral_of_subseq_ae_of_sq_bound`), and the simple identity forces the limits equal. -/
theorem isExpQMartingale_BthetaCont (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    IsExpQMartingale (μ.withDensity fun ω =>
        ENNReal.ofReal (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω))
      (natFiltration hBmeas) (BthetaCont B θ) T := by
  haveI hFB : IsFilteredPreBrownian B (natFiltration hBmeas) μ := hB.isFilteredPreBrownian hBmeas
  have hZTaesm : AEStronglyMeasurable
      (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T) μ :=
    (memLp_ZT_one hB hBmeas hadap hcont hbdd T).1
  have hZTpos : ∀ ω, 0 ≤ contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω :=
    fun ω => (contDoleansExp_pos _ _ _ _).le
  -- `B_0 = 0` a.e. `μ` (law `𝒩(0,0) = δ₀`)
  have hB0 : ∀ᵐ ω ∂μ, B 0 ω = 0 := by
    have hmap := Measure.map_apply (μ := μ) (hBmeas 0) (measurableSet_singleton (0 : ℝ)).compl
    rw [(hFB.hasLaw_eval 0).map_eq, gaussianReal_zero_var,
      Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl] at hmap
    rw [show B 0 ⁻¹' {(0 : ℝ)}ᶜ = {ω | B 0 ω ≠ 0} from by ext ω; simp [Set.mem_preimage]] at hmap
    exact ae_iff.mpr (by simpa using hmap.symm)
  refine ⟨fun u => (hFB.stronglyAdapted u).add
    (stronglyMeasurable_contDrift hBmeas hadap hcont hbdd u), ?_, ?_⟩
  · -- zero start: `B^θ_0 = B_0 + ∫₀⁰θds = 0` a.e. `Q` (`Q ≪ μ`, `contDrift_0 = 0`)
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le hB0] with ω hω
    simp [BthetaCont, hω, contDrift_zero]
  · -- martingale field: limit of the transported simple identity through the engine
    intro a s' t' hst' ht'T A hA
    have hAmΩ : MeasurableSet A := (natFiltration hBmeas).le s' A hA
    have engine : ∀ (u : ℝ≥0), u ≤ T →
        Tendsto (fun n => ∫ ω in A, (Real.exp (a * (B u ω + simpleDrift (unifPart T n)
            (fun i ω => θ (unifPart T n i) ω) n u ω) - a ^ 2 * (u : ℝ) / 2)
          * simpleDoleansExp (X := B) (unifPart T n)
              (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ∂μ) atTop
          (𝓝 (∫ ω in A, (Real.exp (a * BthetaCont B θ u ω - a ^ 2 * (u : ℝ) / 2)
            * contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω) ∂μ)) := fun u huT =>
      tendsto_setIntegral_of_subseq_ae_of_sq_bound
        (fun n => memLp_fn_two hB hBmeas hadap hbdd a T huT n)
        (M := 2⁻¹ * (Real.exp (4 * |a| * C * (T : ℝ)) * (∫ ω, Real.exp (4 * a * B u ω) ∂μ)
            + Real.exp (6 * C ^ 2 * (T : ℝ))))
        (fun n => sq_integral_fn_le hB hBmeas hadap hbdd a T huT n)
        (memLp_g_one hB hBmeas hadap hcont hbdd a T huT)
        (fun ns hns => tendsto_fn_ae_subseq hB hBmeas hadap hcont hbdd a T huT ns hns) A
    have hsimple : ∀ n, 1 ≤ n →
        (∫ ω in A, (Real.exp (a * (B t' ω + simpleDrift (unifPart T n)
            (fun i ω => θ (unifPart T n i) ω) n t' ω) - a ^ 2 * (t' : ℝ) / 2)
          * simpleDoleansExp (X := B) (unifPart T n)
              (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ∂μ)
          = ∫ ω in A, (Real.exp (a * (B s' ω + simpleDrift (unifPart T n)
              (fun i ω => θ (unifPart T n i) ω) n s' ω) - a ^ 2 * (s' : ℝ) / 2)
            * simpleDoleansExp (X := B) (unifPart T n)
                (fun i ω => -(θ (unifPart T n i) ω)) n T ω) ∂μ := by
      intro n hn
      have hlast : unifPart T n n = T := by
        rw [unifPart, div_self (Nat.cast_ne_zero.mpr (by omega)), one_mul]
      have hfield := (isExpQMartingale_BthetaSimple (X := B) (𝓕 := natFiltration hBmeas) (P := μ)
        (unifPart T n) (unifPart_mono T n) (by simp [unifPart]) (fun i ω => θ (unifPart T n i) ω)
        (fun i => hadap (unifPart T n i)) (fun i ω => hbdd (unifPart T n i) ω) n hlast.ge).martingale
        a hst' ht'T hA
      rwa [setIntegral_withDensity_ofReal
          (measurable_Zn hB hBmeas hadap hbdd T n).aestronglyMeasurable
          (fun ω => (simpleDoleansExp_pos _ _ _ _ ω).le) _ hAmΩ,
        setIntegral_withDensity_ofReal
          (measurable_Zn hB hBmeas hadap hbdd T n).aestronglyMeasurable
          (fun ω => (simpleDoleansExp_pos _ _ _ _ ω).le) _ hAmΩ] at hfield
    rw [setIntegral_withDensity_ofReal hZTaesm hZTpos _ hAmΩ,
      setIntegral_withDensity_ofReal hZTaesm hZTpos _ hAmΩ]
    exact tendsto_nhds_unique (engine t' ht'T)
      (Filter.Tendsto.congr' (Filter.eventually_atTop.mpr ⟨1, fun n hn => (hsimple n hn).symm⟩)
        (engine s' (hst'.trans ht'T)))

include hB in
/-- **Continuous bounded-adapted-θ distributional Girsanov: `B^θ` is a `Q`-Brownian motion.** For a
bounded, adapted, path-continuous market price of risk `θ`, under `Q = μ.withDensity(Z_T)` with the
Doléans density `Z_T = exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds)`, the drift-corrected process
`B^θ_u = B_u + ∫₀ᵘθ ds` is a `Q`-Brownian motion on `[0,T]`: zero start, Gaussian increments
`𝒩(0,t−s)`, and independence of disjoint increments. One application of the exponential
characterization `isQBrownianMotion_of_expMartingale` to `isExpQMartingale_BthetaCont` — the general
adapted continuous case, closed on the existing tower with no adapted-integrand Itô formula. -/
theorem Btheta_isQBrownianMotion_adapted (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hadap : ∀ t, StronglyMeasurable[(natFiltration hBmeas t : MeasurableSpace Ω)] (θ t))
    (hcont : ∀ ω, Continuous (fun s : ℝ≥0 => θ s ω)) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) (T : ℝ≥0) :
    (∀ᵐ ω ∂(μ.withDensity fun ω =>
        ENNReal.ofReal (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω)),
        BthetaCont B θ 0 ω = 0)
      ∧ (∀ ⦃s t : ℝ≥0⦄, s ≤ t → t ≤ T →
          (μ.withDensity fun ω =>
              ENNReal.ofReal (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω)).map
            (fun ω => BthetaCont B θ t ω - BthetaCont B θ s ω) = gaussianReal 0 (t - s))
      ∧ (∀ ⦃s t u v : ℝ≥0⦄, s ≤ t → t ≤ u → u ≤ v → v ≤ T →
          IndepFun (fun ω => BthetaCont B θ t ω - BthetaCont B θ s ω)
              (fun ω => BthetaCont B θ v ω - BthetaCont B θ u ω)
            (μ.withDensity fun ω =>
              ENNReal.ofReal (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω))) := by
  haveI : IsProbabilityMeasure (μ.withDensity fun ω =>
      ENNReal.ofReal (contDoleansExp (itoIntCont hB hBmeas hadap hcont hbdd T) θ T ω)) :=
    isProbabilityMeasure_contGirsanov hB hBmeas hadap hcont hbdd T
  exact isQBrownianMotion_of_expMartingale
    (isExpQMartingale_BthetaCont hB hBmeas hadap hcont hbdd T)

end MathFin
