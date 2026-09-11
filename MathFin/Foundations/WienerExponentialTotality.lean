/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.BrownianCylinderGeneration
public import MathFin.Foundations.DoleansStepRepresentation

/-!
# Totality of the Wiener exponentials in `L²(𝓕ᴮ_T)`

The martingale representation theorem is a surjectivity statement, and surjectivity of an
isometry onto a closed subspace is a *totality* statement about its range: nothing in the
target is orthogonal to everything in the range. `DoleansStepRepresentation` puts every
step-integrand Doléans exponential

  `D = ∏ₖ exp(hₖ(B_{sₖ₊₁} − B_{sₖ}) − ½hₖ²(sₖ₊₁ − sₖ))`

inside the range of `∫·dB`, up to the constant `1`. This file supplies the other half: an
`F ∈ L²(𝓕ᴮ_T)` orthogonal to all of them is `0`. Those two facts together are the
representation theorem.

Centering is *not* a hypothesis here. The family already contains the constant `1` — take the
zero integrand `h ≡ 0` over any one cell, where every factor is `exp(0) = 1` — so orthogonality
to the family says `∫F = 0` all by itself.

## The three moves

**A — algebra.** `D = exp(∑ₖ hₖΔBₖ)·exp(−½∑ₖ hₖ²Δsₖ)`, and the second factor is a positive
*constant*: it divides out of `∫ F·D = 0`. What remains is orthogonality to
`exp(∑ₖ hₖΔBₖ)`, and Abel summation on a grid refining `{0,T} ∪ {tᵢ}` turns any coefficient
vector `λ` on the *levels* `B_{tᵢ}` into a coefficient vector `h` on the *increments*
(`B₀ = 0` is what closes the telescope). So `∫ F·exp(∑ᵢ λᵢ B_{tᵢ}) = 0` for every finite
family of times in `[0,T]` and every real `λ`. No analysis yet — this is
`integral_mul_exp_linear_eq_zero`.

**B — Laplace-transform uniqueness on `ℝⁿ`.** Split `F·μ` into its Jordan pieces `ν±`,
finite because `L² ⊆ L¹` here, and push both forward along the coordinate vector
`X = (B_{t₁},…,B_{tₙ})`. Step A says their moment-generating functions agree along every
direction and at every scale. Gaussian marginals give `exp(r⟨λ,X⟩) ∈ L²(μ)` for *every* `r`,
so `integrableExpSet` is the whole line — an open set, which is exactly what licenses the
analytic continuation `eqOn_complexMGF_of_mgf'` from the real axis into `ℂ`. Read at `z = i`
it is equality of characteristic functions along every continuous linear form, and
`Measure.ext_of_charFunDual` (Cramér–Wold in one step) makes the two laws on `ℝⁿ` equal.
Hence `∫_A F = 0` for every cylinder `A`.

**C — Lévy upward.** Step B says `𝔼[F | 𝓖ₙ] = 0` for every dyadic cylinder σ-algebra `𝓖ₙ`.
Path continuity makes `⨆ₙ 𝓖ₙ = 𝓕ᴮ_T` (`iSup_cylinderFiltration_eq_natFiltration`, the whole
content of `BrownianCylinderGeneration`), so Lévy's upward theorem sends `𝔼[F | 𝓖ₙ] → F` in
`L¹`. A sequence of zeros has limit `0`, so `F = 0`.

## Why the hypotheses are what they are

`hB` is not decoration. Without a Brownian law the statement is **false**: for the (continuous,
measurable) process `B ≡ Z` constant in time, every increment vanishes, so every
`stepDoleansExp` is a positive constant and `hFperp` says no more than `∫F = 0` — yet `F = Z` is
centered, `σ(Z) = 𝓕_T`-measurable, in `L²`, and not `0`. (A time-constant but *random* `B` is
what the counterexample needs; `B ≡ 0` will not do, since it makes `𝓕_T = ⊥` and forces `F = 0`
for the right reason.) Brownianness enters twice: at `B₀ = 0` (Step A's telescope) and at the
Gaussian tails (Step B's open `integrableExpSet`).

## Result

* `integral_mul_exp_linear_eq_zero` — Step A: orthogonality to the whole step-Doléans family
  already forces orthogonality to `exp(∑ᵢ λᵢ B_{tᵢ})` for every finite family of times in
  `[0,T]` and every real `λ`.
* `eq_zero_of_orthogonal_stepDoleans` — the totality theorem.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- `exp(c·∑ᵢ λᵢ B_{tᵢ}) ∈ L²(μ)`: induct on the finite sum, at every *scale* `c` at once.
The square of the `(insert a s)`-exponential is the `s`-exponential at twice the scale times
one lognormal marginal factor, and Cauchy–Schwarz (`MemLp.integrable_mul`) multiplies them. -/
private lemma memLp_exp_linear (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    {ι : Type*} (t : ι → ℝ≥0) (lam : ι → ℝ) (S : Finset ι) :
    ∀ c : ℝ, MemLp (fun ω ↦ Real.exp (c * ∑ i ∈ S, lam i * B (t i) ω)) 2 μ := by
  classical
  induction S using Finset.induction_on with
  | empty => intro c; simpa using memLp_const (μ := μ) (1 : ℝ)
  | insert a S ha ih =>
    intro c
    have hsum : Measurable fun ω ↦ ∑ i ∈ insert a S, lam i * B (t i) ω :=
      Finset.measurable_sum _ fun i _ ↦ (hBmeas (t i)).const_mul _
    have hmeas : AEStronglyMeasurable
        (fun ω ↦ Real.exp (c * ∑ i ∈ insert a S, lam i * B (t i) ω)) μ :=
      ((hsum.const_mul c).exp).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmeas]
    have hrw : (fun ω ↦ Real.exp (c * ∑ i ∈ insert a S, lam i * B (t i) ω) ^ 2)
        = fun ω ↦ Real.exp (2 * c * lam a * B (t a) ω)
            * Real.exp (2 * c * ∑ i ∈ S, lam i * B (t i) ω) := by
      funext ω
      rw [Finset.sum_insert ha, sq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hrw]
    exact (memLp_exp_mul_eval hB (t a) (2 * c * lam a)).integrable_mul (ih (2 * c))

omit [IsProbabilityMeasure μ] in
/-- **Step A of totality: from step Doléans exponentials to exponentials of linear
combinations.** `stepDoleansExp B s h N = exp(∑ₖ hₖ ΔBₖ)·exp(−½∑ₖ hₖ²Δsₖ)`, whose second
factor is a positive *constant* that divides out; and Abel summation on a grid refining
`{0, T} ∪ {tᵢ}` realises every real coefficient vector `λ` as some choice of `h`. So
orthogonality to the whole step-Doléans family already forces orthogonality to
`exp(∑ᵢ λᵢ B_{tᵢ})` for every finite family of times in `[0,T]` and every `λ`. -/
theorem integral_mul_exp_linear_eq_zero (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (F : Lp ℝ 2 μ)
    (hFperp : ∀ (s : ℕ → ℝ≥0), Monotone s → ∀ (h : ℕ → ℝ) (N : ℕ),
      s 0 = 0 → s N = T → ∫ ω, F ω * stepDoleansExp B s h N ω ∂μ = 0) :
    ∀ (n : ℕ) (t : Fin n → ℝ≥0), (∀ i, t i ≤ T) → ∀ lam : Fin n → ℝ,
      ∫ ω, F ω * Real.exp (∑ i, lam i * B (t i) ω) ∂μ = 0 := by
  intro n t htT lam
  -- The refining grid: `{0, T} ∪ {tᵢ}`, monotonically enumerated.
  set S : Finset ℝ≥0 := insert 0 (insert T (Finset.image t Finset.univ))
  have h0S : (0 : ℝ≥0) ∈ S := Finset.mem_insert_self _ _
  have hTS : T ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have htS (i : Fin n) : t i ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem t (Finset.mem_univ i)))
  have hSle (q : ℝ≥0) (hq : q ∈ S) : q ≤ T := by
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact zero_le
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact le_rfl
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    exact htT i
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨0, h0S⟩
  set m : ℕ := S.card with hm
  set N : ℕ := m - 1 with hN
  set e : Fin m ↪o ℝ≥0 := S.orderEmbOfFin rfl with he
  have hlt (k : ℕ) : min k N < m := by omega
  set s : ℕ → ℝ≥0 := fun k ↦ e ⟨min k N, hlt k⟩ with hsdef
  have hsval (k : ℕ) (hk : k ≤ N) : s k = e ⟨k, by omega⟩ := by
    simp only [hsdef]
    exact congrArg e (Fin.val_injective (min_eq_left hk))
  have hsmono : Monotone s := fun a b hab ↦ e.monotone (by simp only [Fin.mk_le_mk]; omega)
  have hs0 : s 0 = 0 := by
    have h1 : s 0 = S.min' ⟨0, h0S⟩ := by
      rw [hsval 0 (Nat.zero_le _)]
      exact Finset.orderEmbOfFin_zero (s := S) rfl hcard
    rw [h1]
    exact le_antisymm (Finset.min'_le S 0 h0S) zero_le
  have hsN : s N = T := by
    have h1 : s N = S.max' ⟨0, h0S⟩ := by
      rw [hsval N le_rfl]
      exact Finset.orderEmbOfFin_last (s := S) rfl hcard
    rw [h1]
    exact le_antisymm (Finset.max'_le S _ _ hSle) (Finset.le_max' S T hTS)
  -- The Abel coefficients: `cₖ = ∑ᵢ λᵢ·1_{sₖ < tᵢ}`.
  set c : ℕ → ℝ := fun k ↦ ∑ i, if s k < t i then lam i else 0
  -- Per-index telescoping: the `i`-th slice of the Abel sum is `λᵢ(B_{tᵢ} − B_{s₀})`.
  have hcell (i : Fin n) (ω : Ω) :
      ∑ k ∈ Finset.range N, (if s k < t i then lam i else 0) * (B (s (k + 1)) ω - B (s k) ω)
        = lam i * (B (t i) ω - B (s 0) ω) := by
    obtain ⟨j, hj⟩ : ∃ j : Fin m, e j = t i := by
      show t i ∈ Set.range e
      rw [he, Finset.range_orderEmbOfFin S rfl]
      exact htS i
    have hjlt := j.isLt
    have hjN : (j : ℕ) ≤ N := by omega
    have hsj : s (j : ℕ) = t i := by rw [hsval (j : ℕ) hjN, ← hj]
    have hfilter : {k ∈ Finset.range N | s k < t i} = Finset.range (j : ℕ) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hk, hklt⟩
        rw [hsval k (by omega), ← hj] at hklt
        exact Fin.lt_def.mp (e.lt_iff_lt.mp hklt)
      · intro hk
        refine ⟨by omega, ?_⟩
        rw [hsval k (by omega), ← hj]
        exact e.lt_iff_lt.mpr (Fin.lt_def.mpr hk)
    calc ∑ k ∈ Finset.range N,
          (if s k < t i then lam i else 0) * (B (s (k + 1)) ω - B (s k) ω)
        = ∑ k ∈ Finset.range N,
            if s k < t i then lam i * (B (s (k + 1)) ω - B (s k) ω) else 0 := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          by_cases hk : s k < t i <;> simp [hk]
      _ = ∑ k ∈ {k ∈ Finset.range N | s k < t i}, lam i * (B (s (k + 1)) ω - B (s k) ω) :=
          (Finset.sum_filter _ _).symm
      _ = ∑ k ∈ Finset.range (j : ℕ), lam i * (B (s (k + 1)) ω - B (s k) ω) := by rw [hfilter]
      _ = lam i * ∑ k ∈ Finset.range (j : ℕ), (B (s (k + 1)) ω - B (s k) ω) := by
          rw [Finset.mul_sum]
      _ = lam i * (B (s (j : ℕ)) ω - B (s 0) ω) := by
          rw [Finset.sum_range_sub (fun k ↦ B (s k) ω)]
      _ = lam i * (B (t i) ω - B (s 0) ω) := by rw [hsj]
  -- Abel summation, a.e. (`B₀ = 0`).
  have hkey : ∀ᵐ ω ∂μ, ∑ k ∈ Finset.range N, c k * (B (s (k + 1)) ω - B (s k) ω)
      = ∑ i, lam i * B (t i) ω := by
    filter_upwards [ItoIntegralBrownian.eval_zero_ae hB hBmeas] with ω hω
    have hB0 : B (s 0) ω = 0 := by rw [hs0]; simpa using hω
    calc ∑ k ∈ Finset.range N, c k * (B (s (k + 1)) ω - B (s k) ω)
        = ∑ k ∈ Finset.range N, ∑ i,
            (if s k < t i then lam i else 0) * (B (s (k + 1)) ω - B (s k) ω) :=
          Finset.sum_congr rfl fun k _ ↦ Finset.sum_mul _ _ _
      _ = ∑ i, ∑ k ∈ Finset.range N,
            (if s k < t i then lam i else 0) * (B (s (k + 1)) ω - B (s k) ω) := Finset.sum_comm
      _ = ∑ i, lam i * (B (t i) ω - B (s 0) ω) := Finset.sum_congr rfl fun i _ ↦ hcell i ω
      _ = ∑ i, lam i * B (t i) ω := by rw [hB0]; simp
  -- The deterministic factor divides out.
  set C : ℝ :=
    Real.exp (-(∑ k ∈ Finset.range N, c k ^ 2 * ((s (k + 1) : ℝ) - (s k : ℝ)) / 2)) with hCdef
  have hprod (ω : Ω) : stepDoleansExp B s c N ω
      = C * Real.exp (∑ k ∈ Finset.range N, c k * (B (s (k + 1)) ω - B (s k) ω)) := by
    rw [hCdef, ← Real.exp_add]
    simp only [stepDoleansExp]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_sub_distrib]
    ring
  have hstep : ∫ ω, C * (F ω
      * Real.exp (∑ k ∈ Finset.range N, c k * (B (s (k + 1)) ω - B (s k) ω))) ∂μ = 0 := by
    rw [← hFperp s hsmono c N hs0 hsN]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    simp only [hprod ω]
    ring
  rw [integral_const_mul] at hstep
  have h2 := (mul_eq_zero.mp hstep).resolve_left (Real.exp_pos _).ne'
  rw [integral_congr_ae (g := fun ω ↦ F ω * Real.exp (∑ i, lam i * B (t i) ω))
    (by filter_upwards [hkey] with ω hω; rw [hω])] at h2
  exact h2

omit [IsProbabilityMeasure μ] in
/-- Integration against the density `ofReal ∘ f` is integration of the positive part of `f`
against the integrand: `∫ g d(f⁺·μ) = ∫ f⁺·g dμ`. -/
private lemma integral_withDensity_ofReal_eq {f : Ω → ℝ} (hf : AEMeasurable f μ) (g : Ω → ℝ) :
    ∫ ω, g ω ∂(μ.withDensity fun ω ↦ ENNReal.ofReal (f ω))
      = ∫ ω, max (f ω) 0 * g ω ∂μ := by
  have hnn : AEMeasurable (fun ω ↦ (f ω).toNNReal) μ :=
    continuous_real_toNNReal.measurable.comp_aemeasurable hf
  rw [show (fun ω ↦ ENNReal.ofReal (f ω)) = fun ω ↦ (((f ω).toNNReal : ℝ≥0) : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul₀ hnn]
  simp [NNReal.smul_def, Real.coe_toNNReal']

omit [IsProbabilityMeasure μ] in
/-- Integrability against the density `ofReal ∘ f`, in the same positive-part form. -/
private lemma integrable_withDensity_ofReal_iff {f : Ω → ℝ} (hf : AEMeasurable f μ) (g : Ω → ℝ) :
    Integrable g (μ.withDensity fun ω ↦ ENNReal.ofReal (f ω))
      ↔ Integrable (fun ω ↦ max (f ω) 0 * g ω) μ := by
  have hnn : AEMeasurable (fun ω ↦ (f ω).toNNReal) μ :=
    continuous_real_toNNReal.measurable.comp_aemeasurable hf
  rw [show (fun ω ↦ ENNReal.ofReal (f ω)) = fun ω ↦ (((f ω).toNNReal : ℝ≥0) : ℝ≥0∞) from rfl,
    integrable_withDensity_iff_integrable_smul₀ hnn]
  simp [NNReal.smul_def, Real.coe_toNNReal']

/-- **Step B of totality: a coordinate cylinder carries no mass of `f`.** If `f ∈ L²(μ)` is
orthogonal to `exp(∑ᵢ λᵢ B_{τᵢ})` for every real vector `λ`, then `∫_A f = 0` for every `A` in the
σ-algebra generated by the finitely many coordinates `B_{τᵢ}`. Centering is not a separate
hypothesis: `λ = 0` is one of the vectors, and it says exactly `∫ f = 0`.

The mechanism is Laplace-transform uniqueness. Split `f·μ` into its Jordan pieces `ν±` — finite
measures, since `L² ⊆ L¹` on a probability space — and push both forward along the coordinate
vector `X = (B_{τᵢ})ᵢ` into `ℝ^ι`. Orthogonality says the two moment-generating functions of
`⟨λ, X⟩` agree, for every `λ` and at every scale. The Brownian marginals are Gaussian, so
`exp(r⟨λ,X⟩) ∈ L²(μ)` for *every* `r` and `integrableExpSet` is the whole line — the open strip
that licenses analytic continuation (`eqOn_complexMGF_of_mgf'`). Evaluated at `z = i` that gives
equal characteristic functions along every continuous linear form, and
`Measure.ext_of_charFunDual` turns it into equality of the two pushforwards. -/
private lemma setIntegral_eq_zero_of_iSup_comap (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) {ι : Type*} [Fintype ι] (τ : ι → ℝ≥0)
    {f : Ω → ℝ} (hfL2 : MemLp f 2 μ)
    (hperp : ∀ lam : ι → ℝ, ∫ ω, f ω * Real.exp (∑ i, lam i * B (τ i) ω) ∂μ = 0)
    {A : Set Ω} (hA : MeasurableSet[⨆ i : ι, MeasurableSpace.comap (B (τ i)) inferInstance] A) :
    ∫ ω in A, f ω ∂μ = 0 := by
  classical
  have hf0 : ∫ ω, f ω ∂μ = 0 := by simpa using hperp 0
  have hfae : AEMeasurable f μ := hfL2.aestronglyMeasurable.aemeasurable
  have hfaeneg : AEMeasurable (fun ω ↦ -f ω) μ := hfae.neg
  have hfint : Integrable f μ := memLp_one_iff_integrable.mp (hfL2.mono_exponent one_le_two)
  have hXmeas : Measurable fun (ω : Ω) (i : ι) ↦ B (τ i) ω :=
    measurable_pi_lambda _ fun i ↦ hBmeas (τ i)
  obtain ⟨G, hGmeas, hGA⟩ :
      ∃ G : Set (ι → ℝ), MeasurableSet G ∧ (fun (ω : Ω) (i : ι) ↦ B (τ i) ω) ⁻¹' G = A := by
    rw [← MeasurableSpace.comap_process_pi fun i ↦ B (τ i)] at hA
    exact hA
  have hAmeas : MeasurableSet A := hGA ▸ hXmeas hGmeas
  -- The Jordan pieces of `f·μ`, as finite measures.
  have hfnegL2 : MemLp (fun ω ↦ -f ω) 2 μ := hfL2.neg
  have hposL2 : MemLp (fun ω ↦ max (f ω) 0) 2 μ :=
    hfL2.mono (hfae.max aemeasurable_const).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ by
        rcases le_total 0 (f ω) with h | h
        · rw [max_eq_left h]
        · rw [max_eq_right h, norm_zero]; exact norm_nonneg _)
  have hnegL2 : MemLp (fun ω ↦ max (-f ω) 0) 2 μ :=
    hfnegL2.mono (hfae.neg.max aemeasurable_const).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ by
        rcases le_total 0 (-f ω) with h | h
        · rw [max_eq_left h]
        · rw [max_eq_right h, norm_zero]; exact norm_nonneg _)
  set nuPos : Measure Ω := μ.withDensity (fun ω ↦ ENNReal.ofReal (f ω)) with hnuPos
  set nuNeg : Measure Ω := μ.withDensity (fun ω ↦ ENNReal.ofReal (-f ω)) with hnuNeg
  haveI : IsFiniteMeasure nuPos := isFiniteMeasure_withDensity_ofReal hfint.2
  haveI : IsFiniteMeasure nuNeg := isFiniteMeasure_withDensity_ofReal hfint.neg.2
  -- The total masses agree, because `f` is centered.
  have huniv : nuPos Set.univ = nuNeg Set.univ := by
    have hp : nuPos Set.univ = ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
      rw [hnuPos, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hm : nuNeg Set.univ = ∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ := by
      rw [hnuNeg, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hsub : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ).toReal
        = (∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ).toReal := by
      have hsplit := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfint
      rw [hf0] at hsplit
      linarith
    rw [hp, hm]
    exact (ENNReal.toReal_eq_toReal_iff' (hp ▸ measure_ne_top nuPos Set.univ)
      (hm ▸ measure_ne_top nuNeg Set.univ)).mp hsub
  -- Equality of the two laws of the coordinate vector.
  have hmap : nuPos.map (fun (ω : Ω) (i : ι) ↦ B (τ i) ω)
      = nuNeg.map (fun (ω : Ω) (i : ι) ↦ B (τ i) ω) := by
    haveI : IsFiniteMeasure (nuPos.map fun (ω : Ω) (i : ι) ↦ B (τ i) ω) :=
      Measure.isFiniteMeasure_map _ _
    haveI : IsFiniteMeasure (nuNeg.map fun (ω : Ω) (i : ι) ↦ B (τ i) ω) :=
      Measure.isFiniteMeasure_map _ _
    refine Measure.ext_of_charFunDual (funext fun L ↦ ?_)
    set lam : ι → ℝ := fun i ↦ L (fun j ↦ if i = j then (1 : ℝ) else 0) with hlam
    have hLX (ω : Ω) : L (fun i ↦ B (τ i) ω) = ∑ i, lam i * B (τ i) ω := by
      conv_lhs => rw [pi_eq_sum_univ fun i ↦ B (τ i) ω]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul]; simp [hlam, mul_comm]
    have hexpL2 (r : ℝ) : MemLp (fun ω ↦ Real.exp (r * ∑ i, lam i * B (τ i) ω)) 2 μ :=
      memLp_exp_linear hB hBmeas τ lam Finset.univ r
    have hmgf : mgf (fun ω ↦ ∑ i, lam i * B (τ i) ω) nuPos
        = mgf (fun ω ↦ ∑ i, lam i * B (τ i) ω) nuNeg := by
      funext r
      have hz := hperp fun i ↦ r * lam i
      have hre (ω : Ω) : ∑ i, r * lam i * B (τ i) ω = r * ∑ i, lam i * B (τ i) ω := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ mul_assoc _ _ _
      simp only [hre] at hz
      have hip : Integrable (fun ω ↦ max (f ω) 0
          * Real.exp (r * ∑ i, lam i * B (τ i) ω)) μ := hposL2.integrable_mul (hexpL2 r)
      have him : Integrable (fun ω ↦ max (-f ω) 0
          * Real.exp (r * ∑ i, lam i * B (τ i) ω)) μ := hnegL2.integrable_mul (hexpL2 r)
      have hp : mgf (fun ω ↦ ∑ i, lam i * B (τ i) ω) nuPos r
          = ∫ ω, max (f ω) 0 * Real.exp (r * ∑ i, lam i * B (τ i) ω) ∂μ := by
        rw [show mgf (fun ω ↦ ∑ i, lam i * B (τ i) ω) nuPos r
            = ∫ ω, Real.exp (r * ∑ i, lam i * B (τ i) ω) ∂nuPos from rfl, hnuPos,
          integral_withDensity_ofReal_eq hfae]
      have hm : mgf (fun ω ↦ ∑ i, lam i * B (τ i) ω) nuNeg r
          = ∫ ω, max (-f ω) 0 * Real.exp (r * ∑ i, lam i * B (τ i) ω) ∂μ := by
        rw [show mgf (fun ω ↦ ∑ i, lam i * B (τ i) ω) nuNeg r
            = ∫ ω, Real.exp (r * ∑ i, lam i * B (τ i) ω) ∂nuNeg from rfl, hnuNeg,
          integral_withDensity_ofReal_eq hfaeneg]
      rw [hp, hm, ← sub_eq_zero, ← integral_sub hip him]
      have hpt (ω : Ω) : max (f ω) 0 * Real.exp (r * ∑ i, lam i * B (τ i) ω)
          - max (-f ω) 0 * Real.exp (r * ∑ i, lam i * B (τ i) ω)
          = f ω * Real.exp (r * ∑ i, lam i * B (τ i) ω) := by
        rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
      simp only [hpt]
      exact hz
    have hIES : integrableExpSet (fun ω ↦ ∑ i, lam i * B (τ i) ω) nuPos = Set.univ := by
      refine Set.eq_univ_of_forall fun r ↦ ?_
      show Integrable (fun ω ↦ Real.exp (r * ∑ i, lam i * B (τ i) ω)) nuPos
      rw [hnuPos, integrable_withDensity_ofReal_iff hfae]
      exact hposL2.integrable_mul (hexpL2 r)
    have hnull : nuPos = 0 ↔ nuNeg = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← Measure.measure_univ_eq_zero, huniv]
    have hcx := eqOn_complexMGF_of_mgf' hmgf hnull
      (show Complex.I ∈ {z : ℂ | z.re ∈ interior
        (integrableExpSet (fun ω ↦ ∑ i, lam i * B (τ i) ω) nuPos)} by
        rw [Set.mem_ofPred_eq, hIES, interior_univ]; trivial)
    have hcfd (ν : Measure Ω) :
        charFunDual (ν.map fun (ω : Ω) (i : ι) ↦ B (τ i) ω) L
          = complexMGF (fun ω ↦ ∑ i, lam i * B (τ i) ω) ν Complex.I := by
      have hcont : Continuous fun v : ι → ℝ ↦ Complex.exp ((L v : ℂ) * Complex.I) :=
        Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp L.continuous).mul continuous_const)
      rw [charFunDual_apply, integral_map hXmeas.aemeasurable hcont.aestronglyMeasurable,
        show complexMGF (fun ω ↦ ∑ i, lam i * B (τ i) ω) ν Complex.I
          = ∫ ω, Complex.exp (Complex.I * ((∑ i, lam i * B (τ i) ω : ℝ) : ℂ)) ∂ν from rfl]
      exact integral_congr_ae (Eventually.of_forall fun ω ↦ by
        simp only [hLX ω]; rw [mul_comm])
    rw [hcfd nuPos, hcfd nuNeg]
    exact hcx
  -- A coordinate cylinder is measured equally by the two pieces.
  have hnuA : nuPos A = nuNeg A := by
    rw [← hGA, ← Measure.map_apply hXmeas hGmeas, ← Measure.map_apply hXmeas hGmeas, hmap]
  have ep : ∫⁻ ω in A, ENNReal.ofReal (f ω) ∂μ = nuPos A := by
    rw [hnuPos, withDensity_apply _ hAmeas]
  have em : ∫⁻ ω in A, ENNReal.ofReal (-f ω) ∂μ = nuNeg A := by
    rw [hnuNeg, withDensity_apply _ hAmeas]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfint.restrict, ep, em, hnuA, sub_self]

/-- **Totality of the Wiener exponentials.** An `L²` variable measurable for the Brownian
σ-algebra `𝓕ᴮ_T` and orthogonal to every step-integrand Doléans exponential is zero.

Centering is derived, not assumed. The zero integrand `h ≡ 0` over the single cell `[0,T]` (with
the monotone witness `s k = if k = 0 then 0 else T`, legitimate even at `T = 0`) makes every
factor `exp(0) = 1`, so `hFperp` at that one instantiation is exactly `∫F = 0`. The proof reaches
it through Step A at `n = 0` and then `λ = 0` inside Step B, which is the same fact taking the
route the argument was already travelling.

Three moves. Step A (`integral_mul_exp_linear_eq_zero`) trades the Doléans family for the raw
exponentials `exp(∑ᵢ λᵢ B_{tᵢ})`. Step B (`setIntegral_eq_zero_of_iSup_comap`) turns that, by
Laplace-transform uniqueness on `ℝⁿ`, into `∫_A F = 0` for every cylinder `A` — i.e. every
conditional expectation `𝔼[F | 𝓖ₙ]` on the dyadic cylinder filtration vanishes. Step C is Lévy's
upward theorem: those conditional expectations converge in `L¹` to `F`, because
`⨆ₙ 𝓖ₙ = 𝓕ᴮ_T` (`iSup_cylinderFiltration_eq_natFiltration`, the countable-generation theorem that
path continuity buys), so `F` is the `L¹` limit of zeros. -/
theorem eq_zero_of_orthogonal_stepDoleans (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) (T : ℝ≥0)
    (F : Lp ℝ 2 μ)
    (hFmeas : AEStronglyMeasurable[ItoIntegralL2.natFiltration hBmeas T] (⇑F) μ)
    (hFperp : ∀ (s : ℕ → ℝ≥0), Monotone s → ∀ (h : ℕ → ℝ) (N : ℕ),
      s 0 = 0 → s N = T → ∫ ω, F ω * stepDoleansExp B s h N ω ∂μ = 0) :
    F = 0 := by
  -- The `𝓕ᴮ_T`-strongly-measurable representative Lévy's theorem asks for.
  set f : Ω → ℝ := hFmeas.mk (⇑F)
  have hfae : (⇑F) =ᵐ[μ] f := hFmeas.ae_eq_mk
  have hfsm : StronglyMeasurable[ItoIntegralL2.natFiltration hBmeas T] f :=
    hFmeas.stronglyMeasurable_mk
  have hfL2 : MemLp f 2 μ := MemLp.ae_eq hfae (Lp.memLp F)
  have hfint : Integrable f μ := memLp_one_iff_integrable.mp (hfL2.mono_exponent one_le_two)
  -- Step A, read on the representative.
  have hperp (k : ℕ) (t : Fin k → ℝ≥0) (ht : ∀ i, t i ≤ T) (lam : Fin k → ℝ) :
      ∫ ω, f ω * Real.exp (∑ i, lam i * B (t i) ω) ∂μ = 0 := by
    have hA := integral_mul_exp_linear_eq_zero hB hBmeas T F hFperp k t ht lam
    rwa [integral_congr_ae (g := fun ω ↦ f ω * Real.exp (∑ i, lam i * B (t i) ω))
      (by filter_upwards [hfae] with ω hω; rw [hω])] at hA
  -- Step B, at every level of the dyadic cylinder filtration.
  have hcond (n : ℕ) : μ[f | (cylinderFiltration B T hBmeas) n] =ᵐ[μ] 0 := by
    refine (ae_eq_condExp_of_forall_setIntegral_eq ((cylinderFiltration B T hBmeas).le n) hfint
      (fun A _ _ ↦ integrable_zero _ _ _) (fun A hAm _ ↦ ?_) aestronglyMeasurable_zero).symm
    have hperpι (lam : {q : ℝ≥0 // q ∈ dyadicGrid T n} → ℝ) :
        ∫ ω, f ω * Real.exp (∑ i, lam i * B (i : ℝ≥0) ω) ∂μ = 0 := by
      obtain ⟨e⟩ : Nonempty (Fin (Fintype.card {q : ℝ≥0 // q ∈ dyadicGrid T n})
          ≃ {q : ℝ≥0 // q ∈ dyadicGrid T n}) := ⟨(Fintype.equivFin _).symm⟩
      have hsum (ω : Ω) : ∑ j, lam (e j) * B (e j : ℝ≥0) ω = ∑ i, lam i * B (i : ℝ≥0) ω :=
        Equiv.sum_comp e fun i ↦ lam i * B (i : ℝ≥0) ω
      simpa only [hsum] using
        hperp _ (fun j ↦ (e j : ℝ≥0)) (fun j ↦ dyadicGrid_le (e j).2) fun j ↦ lam (e j)
    have hAcyl : MeasurableSet[⨆ i : {q : ℝ≥0 // q ∈ dyadicGrid T n},
        MeasurableSpace.comap (B (i : ℝ≥0)) inferInstance] A := by
      rw [← iSup_subtype' (p := fun q : ℝ≥0 ↦ q ∈ dyadicGrid T n)
        (f := fun q (_ : q ∈ dyadicGrid T n) ↦ MeasurableSpace.comap (B q) inferInstance)]
      exact hAm
    simp only [Pi.zero_apply, integral_zero]
    exact (setIntegral_eq_zero_of_iSup_comap hB hBmeas
      (fun i : {q : ℝ≥0 // q ∈ dyadicGrid T n} ↦ (i : ℝ≥0)) hfL2 hperpι hAcyl).symm
  -- Step C: Lévy upward on the cylinder filtration, whose limit σ-algebra is `𝓕ᴮ_T`.
  have hsm : StronglyMeasurable[⨆ n : ℕ, (cylinderFiltration B T hBmeas) n] f := by
    rw [iSup_cylinderFiltration_eq_natFiltration hBmeas hBcont T]
    exact hfsm
  have hlim := hfint.tendsto_eLpNorm_condExp (ℱ := cylinderFiltration B T hBmeas) hsm
  have heq (n : ℕ) :
      eLpNorm (μ[f | (cylinderFiltration B T hBmeas) n] - f) 1 μ = eLpNorm f 1 μ := by
    have hsub : (μ[f | (cylinderFiltration B T hBmeas) n] - f) =ᵐ[μ] -f := by
      filter_upwards [hcond n] with ω hω
      simp [hω]
    rw [eLpNorm_congr_ae hsub, eLpNorm_neg]
  simp only [heq] at hlim
  have hf0ae : f =ᵐ[μ] 0 :=
    (eLpNorm_eq_zero_iff hfL2.aestronglyMeasurable one_ne_zero).mp
      (tendsto_nhds_unique hlim tendsto_const_nhds).symm
  exact Lp.ext_iff.mpr ((hfae.trans hf0ae).trans (Lp.coeFn_zero ℝ 2 μ).symm)

end MathFin
