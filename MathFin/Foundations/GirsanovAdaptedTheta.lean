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
    ∃ ms : ℕ → ℕ, ∀ᵐ ω ∂μ, Tendsto (fun k => riemannσ (B := B) θ T (ns (ms k)) ω) atTop
      (𝓝 (itoIntCont hB hBmeas hadap hcont hbdd T ω)) := by
  have hconv : TendstoInMeasure μ (fun k => riemannσ (B := B) θ T (ns k)) atTop
      (itoIntCont hB hBmeas hadap hcont hbdd T) :=
    fun ε hε => (tendstoInMeasure_riemannσ hB hBmeas hadap hcont hbdd T ε hε).comp hns
  obtain ⟨ms, _, hae⟩ := hconv.exists_seq_tendsto_ae
  exact ⟨ms, hae⟩

end MathFin
