/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- `import Mathlib` + `BrownianMotion.*` come transitively through `ItoIntegralCLM`.
import MathFin.Foundations.ItoIntegralCLM
import MathFin.Foundations.ItoFormulaSquaredL2

/-!
# The Itô integral of Brownian motion: `∫₀ᵀ B dB = ½(B_T² − B₀² − T)` via the CLM

This is the **keystone consumer** of the continuous Itô integral
`ItoIntegralCLM.itoIntegralCLM_T`. Until now the library held two unconnected
notions of `∫₀ᵀ B dB`: the abstract CLM (built at 733 LOC) and the concrete
quadratic-variation limit `½(B_T² − B₀² − T)` (`itoSquared_L2_tendsto_div2`),
with no theorem bridging them — and the CLM had **zero consumers**. This file
bridges them: the CLM, evaluated on the Itô-L² realisation of the integrand
`s ↦ B_s`, equals `½(B_T² − B₀² − T)`.

## The boundedness obstruction (and its honest resolution)

Degenne's `SimpleProcess` requires *uniformly bounded* coefficients
(`bounded_value`). The natural left-endpoint integrand coefficient `B_{t_k}` is
an unbounded Gaussian, so `∑ B_{t_k}·ΔB_k` is **not** the elementary integral of
any simple process. We therefore work with the **truncated** left-endpoint
process `∑ clamp_M(B_{t_k})·𝟙_{(t_k,t_{k+1}]}` (a genuine bounded simple
process), and recover the untruncated Riemann sum in the `L²` limit via the
*unbounded*-`L²` discrete isometry (`ItoIsometryAdapted.ito_isometry_discrete`,
which needs only adapted + `L²`, not boundedness). This truncation is not a
device — it is exactly how the Itô integral is defined for unbounded integrands.

## Architecture

1. `clampM` — truncation to `[−M, M]`; bounded, measurable, `𝓕`-preserving.
2. `stepSP` — a single bounded adapted step `φ·𝟙_{(a,b]}` as a `TBoundedSP`.
3. `truncStep n M` — the truncated left-endpoint process over `unifPart T n`.
4. `itoSimple (truncStep n M) = ∑ clamp_M(B_{t_k})·ΔB_k` — the truncated sum.
5. CLM evaluates: `itoIntegralCLM_T (simpleAssembly_T (truncStep n M))` is that
   sum's `L²` class (`extendOfNorm_eq` + the assembly isometry).
6. The truncated sums converge in `L²` to `½(B_T² − B₀² − T)`
   (`itoSquared_L2_tendsto_div2` + the truncation error → 0).
7. By the isometry the embeddings are Cauchy in the predictable `L²`; their limit
   `g_B` is the Itô-L² realisation of `s ↦ B_s`.
8. `itoIntegralCLM_T g_B = ½·⟦B_T² − B₀² − T⟧` — the keystone.
-/

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal MathFin.QuadraticVariationL2
open scoped MeasureTheory NNReal ENNReal InnerProductSpace

namespace MathFin
namespace ItoIntegralBrownian

open ItoIntegralL2 ItoIntegralCLM ItoIsometryAdapted

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### Truncation to `[−M, M]` -/

/-- Truncation of a real to `[−M, M]`. -/
noncomputable def clampM (M x : ℝ) : ℝ := max (-M) (min M x)

@[simp] lemma clampM_abs_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |clampM M x| ≤ M := by
  rw [clampM, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma measurable_clampM (M : ℝ) : Measurable (clampM M) := by
  unfold clampM; fun_prop

/-- `clamp_M(B_a)` is `𝓕_a`-measurable when `B_a` is. -/
lemma measurable_clampM_comp {a : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {M : ℝ}
    {f : Ω → ℝ} (hf : Measurable[natFiltration hBmeas a] f) :
    Measurable[natFiltration hBmeas a] (fun ω => clampM M (f ω)) :=
  (measurable_clampM M).comp hf

/-! ### A single bounded adapted step `φ·𝟙_{(a,b]}` -/

/-- The single-step simple process `φ · 𝟙_{(a,b]}` with `φ` bounded by `M` and
`𝓕_a`-measurable. Its terminal Itô integral is `φ·(B_b − B_a)`. -/
noncomputable def stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a b : ℝ≥0}
    (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ}
    (hφ : Measurable[natFiltration hBmeas a] φ) {M : ℝ} (hφM : ∀ ω, |φ ω| ≤ M) :
    TBoundedSP T hBmeas :=
  ⟨{ valueBot := 0
     value := Finsupp.single (a, b) φ
     le_of_mem_support_value := fun p hp => by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       exact hab
     measurable_valueBot := measurable_const
     measurable_value' := fun p hp => by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       rw [Finsupp.single_eq_same]; exact hφ
     bounded_valueBot := ⟨0, by simp⟩
     bounded_value := ⟨M, fun p hp ω => by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       rw [Finsupp.single_eq_same, Real.norm_eq_abs]; exact hφM ω⟩ },
   fun p hp => by
     obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
     exact hbT⟩

/-- The terminal Itô integral of a single step is `φ·(B_b − B_a)`. -/
lemma itoSimple_stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a b : ℝ≥0}
    (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ}
    (hφ : Measurable[natFiltration hBmeas a] φ) {M : ℝ} (hφM : ∀ ω, |φ ω| ≤ M) (ω : Ω) :
    itoSimple hBmeas (stepSP hBmeas hab hbT hφ hφM).val ω = φ ω * (B b ω - B a ω) := by
  rw [itoSimple_apply]
  show (Finsupp.single (a, b) φ).sum (fun p v => v ω * (B p.2 ω - B p.1 ω))
      = φ ω * (B b ω - B a ω)
  rw [Finsupp.sum_single_index (by simp)]

/-! ### The uniform partition and adaptedness of `B` to its own filtration -/

/-- The uniform partition points `unifPart T n = (k/n)·T` are monotone in `k`. -/
lemma unifPart_mono (T : ℝ≥0) (n : ℕ) : Monotone (unifPart T n) :=
  fun a b hab => by simp only [unifPart]; gcongr

/-- A partition point `unifPart T n j ≤ T` whenever `j ≤ n`. -/
lemma unifPart_le_T {T : ℝ≥0} {n j : ℕ} (hj : j ≤ n) : unifPart T n j ≤ T := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp only [Nat.le_zero] at hj; subst hj; simp [unifPart]
  · rw [unifPart]
    have h1 : (j : ℝ≥0) / n ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hn)]; exact_mod_cast hj
    calc (j : ℝ≥0) / n * T ≤ 1 * T := by gcongr
      _ = T := one_mul T

/-- `B s` is measurable with respect to the natural filtration at `s`: the
natural filtration at `s` is `⨆ j ≤ s, comap (B j)`, which contains `comap (B s)`. -/
lemma measurable_eval_natFiltration (hBmeas : ∀ t, Measurable (B t)) (s : ℝ≥0) :
    Measurable[natFiltration hBmeas s] (B s) := by
  have hle : MeasurableSpace.comap (B s) inferInstance ≤ natFiltration hBmeas s :=
    le_iSup₂ (f := fun j (_ : j ≤ s) => MeasurableSpace.comap (B j) inferInstance) s le_rfl
  exact (measurable_iff_comap_le.mpr le_rfl).mono hle le_rfl

/-! ### The truncated left-endpoint process -/

/-- The **truncated left-endpoint step process** over the uniform partition of
`[0,T]` into `n` pieces, with coefficients clamped to `[−m, m]`:
`∑_{k<n} clamp_m(B_{t_k}) · 𝟙_{(t_k, t_{k+1}]}`, `t_k = unifPart T n k`. A genuine
bounded `TBoundedSP` (the clamp is what makes it bounded — `B_{t_k}` itself is
not). Indexed over `(range n).attach` so each step sees `k < n` for `t_{k+1} ≤ T`. -/
noncomputable def truncStep (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (n m : ℕ) :
    TBoundedSP T hBmeas :=
  ∑ k ∈ (Finset.range n).attach,
    stepSP hBmeas (a := unifPart T n k.1) (b := unifPart T n (k.1 + 1))
      (unifPart_mono T n (Nat.le_succ k.1))
      (unifPart_le_T (Finset.mem_range.mp k.2))
      (φ := fun ω => clampM (m : ℝ) (B (unifPart T n k.1) ω))
      (measurable_clampM_comp hBmeas (measurable_eval_natFiltration hBmeas (unifPart T n k.1)))
      (M := (m : ℝ)) (fun ω => clampM_abs_le (Nat.cast_nonneg m) (B (unifPart T n k.1) ω))

/-- The truncated left-endpoint Riemann sum as a function:
`∑_{k<n} clamp_m(B_{t_k})·(B_{t_{k+1}} − B_{t_k})`. -/
noncomputable def truncRiemannFn (_hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (n m : ℕ)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, clampM (m : ℝ) (B (unifPart T n k) ω)
    * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)

/-- The elementary Itô integral is additive over a finite sum of simple processes. -/
lemma itoSimple_sum (hBmeas : ∀ t, Measurable (B t)) {ι' : Type*} (s : Finset ι')
    (V : ι' → SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    itoSimple hBmeas (∑ i ∈ s, V i) = ∑ i ∈ s, itoSimple hBmeas (V i) := by
  classical
  induction s using Finset.induction with
  | empty => funext ω; simp [itoSimple]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, itoSimple_add, ih]

/-- **The truncated step process integrates to the truncated Riemann sum.** -/
lemma itoSimple_truncStep (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (n m : ℕ) (ω : Ω) :
    itoSimple hBmeas (truncStep hBmeas T n m).val ω = truncRiemannFn hBmeas T n m ω := by
  rw [truncStep, AddSubmonoidClass.coe_finsetSum, itoSimple_sum]
  rw [Finset.sum_apply]
  rw [truncRiemannFn, ← Finset.sum_attach (Finset.range n) (fun k =>
    clampM (m : ℝ) (B (unifPart T n k) ω) * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [itoSimple_stepSP]

/-! ### `L²` truncation primitives -/

variable [hB : IsPreBrownian B μ]

omit [IsProbabilityMeasure μ] in
/-- `B s` is in `L²(μ)` (a centered Gaussian). -/
lemma memLp_eval (s : ℝ≥0) : MemLp (B s) 2 μ :=
  (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two

omit mΩ in
/-- `clampM` preserves adaptedness: clamping an `𝓕_{t₀}`-adapted coefficient keeps it adapted. -/
lemma adaptedAt_clampM {t₀ : ℝ≥0} {φ : Ω → ℝ} (M : ℝ)
    (hφ : ItoIsometryAdapted.AdaptedAt B t₀ φ) :
    ItoIsometryAdapted.AdaptedAt B t₀ (fun ω => clampM M (φ ω)) := by
  obtain ⟨g, hg, rfl⟩ := hφ
  exact ⟨fun p => clampM M (g p), (measurable_clampM M).comp hg, rfl⟩

/-- `clamp_M(x) = x` once `|x| ≤ M`. -/
lemma clampM_eq_self {M x : ℝ} (h : |x| ≤ M) : clampM M x = x := by
  rw [abs_le] at h
  rw [clampM, min_eq_right h.2, max_eq_right h.1]

/-- `clampM` is nonexpansive toward `0`: `|clamp_M(x) − x| ≤ |x|`. -/
lemma clampM_sub_self_abs_le {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : |clampM M x - x| ≤ |x| := by
  rw [clampM]
  rcases le_total x (-M) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h,
        abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; linarith
  · rcases le_total x M with h2 | h2
    · rw [min_eq_right h2, max_eq_right h, sub_self, abs_zero]; exact abs_nonneg _
    · rw [min_eq_left h2, max_eq_right (by linarith),
          abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; linarith

omit [IsProbabilityMeasure μ] in
/-- **The truncation error vanishes in `L²`.** For `X ∈ L²(μ)`,
`∫ (clamp_m(X) − X)² ∂μ → 0` as `m → ∞`. Dominated convergence: the integrand is
dominated by `X²` and tends pointwise to `0` (`clamp_m(X) = X` once `m ≥ |X|`). -/
lemma tendsto_clampM_sub_sq_integral {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Tendsto (fun m : ℕ => ∫ ω, (clampM (m : ℝ) (X ω) - X ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hXsq : Integrable (fun ω => (X ω) ^ 2) μ := hX.integrable_sq
  have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun ω => (X ω) ^ 2)
    (F := fun (m : ℕ) ω => (clampM (m : ℝ) (X ω) - X ω) ^ 2)
    (f := fun _ => (0 : ℝ))
    (fun m => (((measurable_clampM (m : ℝ)).comp_aemeasurable hX.aemeasurable).sub
        hX.aemeasurable).pow_const 2 |>.aestronglyMeasurable)
    hXsq
    (fun m => ae_of_all _ fun ω => by
      show ‖(clampM (m : ℝ) (X ω) - X ω) ^ 2‖ ≤ (X ω) ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (X ω),
          ← sq_abs (clampM (m : ℝ) (X ω) - X ω)]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (clampM_sub_self_abs_le (Nat.cast_nonneg m) (X ω)) 2)
    (ae_of_all _ fun ω => ?_)
  · simpa using hconv
  · -- eventually `clamp_m(X ω) = X ω`, so the sequence is eventually 0.
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|X ω|⌉₊] with m hm
    have hle : |X ω| ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm)
    rw [clampM_eq_self hle, sub_self]; ring

/-! ### Convergence of the truncated Riemann sums to `½(B_T² − B₀² − T)` -/

/-- The **untruncated** left-endpoint Riemann sum `∑_{k<n} B_{t_k}·ΔB_k`. -/
noncomputable def riemannFn (_hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, B (unifPart T n k) ω
    * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)

omit [IsProbabilityMeasure μ] in
/-- `‖g‖² = ∫ (g ω)² ∂μ` for `g ∈ Lp 2 μ` (the real `L²` norm-square as an integral). -/
lemma lp_norm_sq (g : Lp ℝ 2 μ) : ‖g‖ ^ 2 = ∫ ω, (g ω) ^ 2 ∂μ := by
  have h : ⟪g, g⟫_ℝ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  rw [L2.inner_def] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  show (g a) * (g a) = (g a) ^ 2
  ring

/-- `MemLp` of the truncated Riemann sum (finite sum of adapted·increment `L²` terms). -/
lemma memLp_truncRiemannFn (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (n m : ℕ) :
    MemLp (truncRiemannFn hBmeas T n m) 2 μ := by
  unfold truncRiemannFn
  refine memLp_finsetSum _ fun k _ => ?_
  refine ItoIsometryAdapted.memLp_adapted_mul_increment hBmeas
    (unifPart_mono T n (Nat.le_succ k)) (adaptedAt_clampM _ (adaptedAt_eval le_rfl)) ?_
  exact MemLp.of_bound ((measurable_clampM (m : ℝ)).comp (hBmeas _)).aestronglyMeasurable (m : ℝ)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact clampM_abs_le (Nat.cast_nonneg m) _)

omit [IsProbabilityMeasure μ] in
/-- `MemLp` of the untruncated Riemann sum. -/
lemma memLp_riemannFn (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (n : ℕ) :
    MemLp (riemannFn hBmeas T n) 2 μ := by
  unfold riemannFn
  refine memLp_finsetSum _ fun k _ => ?_
  exact ItoIsometryAdapted.memLp_adapted_mul_increment hBmeas
    (unifPart_mono T n (Nat.le_succ k)) (adaptedAt_eval le_rfl) (memLp_eval _)

/-- **The CLM evaluated on `truncStep` is the truncated Riemann sum's `L²` class.** This is
where `itoIntegralCLM_T` gets a genuine consumer: the continuous Itô integral of the bounded
step process is, by construction (`extendOfNorm_eq` + the assembly isometry), the `L²` class of
`∑ clamp_m(B_{t_k})·ΔB_k`. -/
lemma itoIntegralCLM_T_truncStep (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (n m : ℕ) :
    itoIntegralCLM_T (μ := μ) T hBmeas (simpleAssembly_T (μ := μ) T hBmeas (truncStep hBmeas T n m))
      = (memLp_truncRiemannFn hBmeas T n m).toLp (truncRiemannFn hBmeas T n m) := by
  rw [itoIntegralCLM_T, LinearMap.extendOfNorm_eq (simpleAssembly_T_denseRange T hBmeas)
        ⟨1, fun V => by rw [one_mul]; exact (assembly_isometry_T T hBmeas V).le⟩]
  show ItoIntegralL2.itoSimpleLp hBmeas (truncStep hBmeas T n m).val = _
  rw [ItoIntegralL2.itoSimpleLp]
  exact (MemLp.toLp_eq_toLp_iff _ _).mpr
    (Filter.Eventually.of_forall fun ω => itoSimple_truncStep hBmeas T n m ω)

/-- The truncated minus untruncated Riemann sum is the increment sum of the clamp errors. -/
lemma truncRiemannFn_sub_riemannFn (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (n m : ℕ) (ω : Ω) :
    truncRiemannFn hBmeas T n m ω - riemannFn hBmeas T n ω
      = ∑ k ∈ Finset.range n, (clampM (m : ℝ) (B (unifPart T n k) ω) - B (unifPart T n k) ω)
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) := by
  rw [truncRiemannFn, riemannFn, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The truncation error as a variance sum** (Itô isometry). -/
lemma integral_truncRiemann_sub_sq (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (n m : ℕ) :
    ∫ ω, (truncRiemannFn hBmeas T n m ω - riemannFn hBmeas T n ω) ^ 2 ∂μ
      = ∑ k ∈ Finset.range n,
          (∫ ω, (clampM (m : ℝ) (B (unifPart T n k) ω) - B (unifPart T n k) ω) ^ 2 ∂μ)
            * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
  rw [show (fun ω => (truncRiemannFn hBmeas T n m ω - riemannFn hBmeas T n ω) ^ 2)
        = (fun ω => (∑ k ∈ Finset.range n,
            (clampM (m : ℝ) (B (unifPart T n k) ω) - B (unifPart T n k) ω)
              * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω)) ^ 2)
      from funext fun ω => by rw [truncRiemannFn_sub_riemannFn]]
  refine ito_isometry_discrete hBmeas (unifPart_mono T n)
    (fun k => (adaptedAt_clampM _ (adaptedAt_eval le_rfl)).sub (adaptedAt_eval le_rfl))
    (fun k => MemLp.sub ?_ (memLp_eval _))
  exact MemLp.of_bound ((measurable_clampM (m : ℝ)).comp (hBmeas _)).aestronglyMeasurable (m : ℝ)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact clampM_abs_le (Nat.cast_nonneg m) _)

/-- **For each `n`, the truncation error → 0 as `m → ∞`** (a finite sum of clamp-error
integrals, each vanishing by `tendsto_clampM_sub_sq_integral`). -/
lemma tendsto_integral_truncRiemann_sub_sq (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) (n : ℕ) :
    Tendsto (fun m => ∫ ω, (truncRiemannFn hBmeas T n m ω - riemannFn hBmeas T n ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  simp_rw [integral_truncRiemann_sub_sq]
  have h0 : (0 : ℝ) = ∑ k ∈ Finset.range n, (0 : ℝ) * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) := by
    simp
  rw [h0]
  exact tendsto_finsetSum _ fun k _ =>
    (tendsto_clampM_sub_sq_integral (memLp_eval (unifPart T n k))).mul_const _

/-! ### The limit `½(B_T² − B₀² − T)` as an `L²` element -/

omit [IsProbabilityMeasure μ] in
/-- `B 0 = 0` a.s. (its second moment `∫ (B 0)² = 0`). -/
lemma eval_zero_ae (hBmeas : ∀ t, Measurable (B t)) : B 0 =ᵐ[μ] 0 := by
  have hint : ∫ ω, (B 0 ω) ^ 2 ∂μ = 0 := by rw [integral_eval_sq hBmeas 0]; simp
  have hsq : (fun ω => (B 0 ω) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _)
      (memLp_eval 0).integrable_sq).mp hint
  filter_upwards [hsq] with ω hω
  exact pow_eq_zero_iff two_ne_zero |>.mp hω

omit [IsProbabilityMeasure μ] in
/-- `MemLp` of the keystone limit `½(B_T² − B₀² − T)` (`= ½(B_T² − T)` a.s. since `B₀ = 0`),
via the centered squared increment `(B_T − B₀)² − T ∈ L²`. -/
lemma memLp_halfD (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) :
    MemLp (fun ω => (1 / 2 : ℝ) * (B T ω ^ 2 - B 0 ω ^ 2 - (T : ℝ))) 2 μ := by
  refine (memLp_congr_ae ?_).mp
    (MemLp.const_mul (memLp_increment_sq_centered_two (B := B) 0 T (T : ℝ)) (1 / 2))
  filter_upwards [eval_zero_ae hBmeas] with ω hω
  simp only [Pi.zero_apply] at hω
  rw [hω]; ring

omit [IsProbabilityMeasure μ] in
/-- The squared `L²`-distance of two `toLp` classes is the integral of the squared difference. -/
lemma lp_dist_sq {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ ω, (f ω - g ω) ^ 2 ∂μ := by
  rw [lp_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with ω h1 h2 h3
  rw [h1]; simp only [Pi.sub_apply]; rw [h2, h3]

omit [IsProbabilityMeasure μ] in
/-- If `∫ (Fₙ − Gₙ)² → 0` then the `L²` classes converge: `‖⟦Fₙ⟧ − ⟦Gₙ⟧‖ → 0`. -/
lemma tendsto_norm_toLp_sub {F G : ℕ → Ω → ℝ} (hF : ∀ n, MemLp (F n) 2 μ)
    (hG : ∀ n, MemLp (G n) 2 μ)
    (h : Tendsto (fun n => ∫ ω, (F n ω - G n ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ‖(hF n).toLp (F n) - (hG n).toLp (G n)‖) atTop (𝓝 0) := by
  have heq : (fun n => ‖(hF n).toLp (F n) - (hG n).toLp (G n)‖)
      = fun n => Real.sqrt (∫ ω, (F n ω - G n ω) ^ 2 ∂μ) := by
    funext n; rw [← lp_dist_sq (hF n) (hG n), Real.sqrt_sq (norm_nonneg _)]
  rw [heq]
  simpa using (Real.continuous_sqrt.tendsto 0).comp h

/-- **Keystone: `∫₀ᵀ B dB = ½(B_T² − B₀² − T)` through the CLM.** There is an Itô-`L²`
integrand `gB` — the `trim_T`-limit of the truncated left-endpoint approximations of `s ↦ Bₛ`
— whose continuous Itô integral `itoIntegralCLM_T gB` equals `½(B_T² − B₀² − T)`. This gives the
733-LOC `itoIntegralCLM_T` its **first genuine consumer** and bridges the abstract CLM integral
to the concrete quadratic-variation limit (`itoSquared_L2_tendsto_div2`). The unbounded Gaussian
coefficients `B_{t_k}` are handled by clamp-truncation; the truncation error vanishes by the
unbounded-`L²` discrete isometry. -/
theorem itoIntegralCLM_T_brownian (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) :
    ∃ gB : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      itoIntegralCLM_T (μ := μ) T hBmeas gB
        = (memLp_halfD hBmeas T).toLp (fun ω => (1 / 2 : ℝ) * (B T ω ^ 2 - B 0 ω ^ 2 - (T : ℝ))) := by
  classical
  set c := (memLp_halfD (μ := μ) hBmeas T).toLp
    (fun ω => (1 / 2 : ℝ) * (B T ω ^ 2 - B 0 ω ^ 2 - (T : ℝ))) with hc
  -- Diagonal truncation level `M n` making the truncation error `< 1/(n+1)`.
  have hMex : ∀ n, ∃ m, ∫ ω, (truncRiemannFn hBmeas T n m ω - riemannFn hBmeas T n ω) ^ 2 ∂μ
      < 1 / (n + 1) := fun n =>
    ((tendsto_integral_truncRiemann_sub_sq hBmeas T n).eventually_lt_const (by positivity)).exists
  choose M hM using hMex
  -- Truncation error → 0 (squeeze by `1/(n+1)`).
  have herr : Tendsto (fun n => ∫ ω,
      (truncRiemannFn hBmeas T n (M n) ω - riemannFn hBmeas T n ω) ^ 2 ∂μ) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) (fun n => (hM n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  -- Untruncated Riemann sums → ½(B_T²−B₀²−T) in L² (the QV keystone).
  have hrito : Tendsto (fun n => ∫ ω,
      (riemannFn hBmeas T n ω - (1 / 2 : ℝ) * (B T ω ^ 2 - B 0 ω ^ 2 - (T : ℝ))) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    have key := itoSquared_L2_tendsto_div2 (μ := μ) (B := B) hBmeas T
    simpa only [riemannFn] using key
  -- The CLM images `a n = ⟦truncRiemannFn n (M n)⟧` converge to `c = ⟦½(B_T²−B₀²−T)⟧`.
  have hA : Tendsto (fun n => (memLp_truncRiemannFn hBmeas T n (M n)).toLp
      (truncRiemannFn hBmeas T n (M n))) atTop (𝓝 c) := by
    have hb1 := tendsto_norm_toLp_sub (fun n => memLp_truncRiemannFn hBmeas T n (M n))
      (fun n => memLp_riemannFn hBmeas T n) herr
    have hb2 := tendsto_norm_toLp_sub (fun n => memLp_riemannFn hBmeas T n)
      (fun _ => memLp_halfD hBmeas T) hrito
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hb1.add hb2)
    calc ‖(memLp_truncRiemannFn hBmeas T n (M n)).toLp (truncRiemannFn hBmeas T n (M n)) - c‖
        = dist ((memLp_truncRiemannFn hBmeas T n (M n)).toLp (truncRiemannFn hBmeas T n (M n))) c :=
          (dist_eq_norm _ _).symm
      _ ≤ dist ((memLp_truncRiemannFn hBmeas T n (M n)).toLp (truncRiemannFn hBmeas T n (M n)))
            ((memLp_riemannFn hBmeas T n).toLp (riemannFn hBmeas T n))
          + dist ((memLp_riemannFn hBmeas T n).toLp (riemannFn hBmeas T n)) c :=
          dist_triangle _ _ _
      _ = _ := by rw [dist_eq_norm, dist_eq_norm, hc]; simp only [one_div]
  -- `itoIntegralCLM_T` is an isometry; the preimages are Cauchy, hence converge to `gB`.
  have hisom : Isometry (itoIntegralCLM_T (μ := μ) T hBmeas) :=
    AddMonoidHomClass.isometry_of_norm _ (itoIntegralCLM_T_norm T hBmeas)
  set x : ℕ → Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas) :=
    fun n => simpleAssembly_T (μ := μ) T hBmeas (truncStep hBmeas T n (M n)) with hxdef
  have hax : ∀ n, itoIntegralCLM_T (μ := μ) T hBmeas (x n)
      = (memLp_truncRiemannFn hBmeas T n (M n)).toLp (truncRiemannFn hBmeas T n (M n)) :=
    fun n => itoIntegralCLM_T_truncStep hBmeas T n (M n)
  have hxCauchy : CauchySeq x := by
    have haC : CauchySeq (fun n => itoIntegralCLM_T (μ := μ) T hBmeas (x n)) := by
      simp only [hax]; exact hA.cauchySeq
    rw [Metric.cauchySeq_iff] at haC ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := haC ε hε
    exact ⟨N, fun mm hmm nn hnn => by rw [← hisom.dist_eq]; exact hN mm hmm nn hnn⟩
  obtain ⟨gB, hgB⟩ := cauchySeq_tendsto_of_complete hxCauchy
  refine ⟨gB, ?_⟩
  have h1 : Tendsto (fun n => itoIntegralCLM_T (μ := μ) T hBmeas (x n)) atTop
      (𝓝 (itoIntegralCLM_T (μ := μ) T hBmeas gB)) :=
    ((itoIntegralCLM_T (μ := μ) T hBmeas).continuous.tendsto gB).comp hgB
  have h2 : Tendsto (fun n => itoIntegralCLM_T (μ := μ) T hBmeas (x n)) atTop (𝓝 c) := by
    simp only [hax]; exact hA
  exact tendsto_nhds_unique h1 h2

end ItoIntegralBrownian
end MathFin
