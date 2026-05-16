/-
  HybridVerify.MartingaleTransform
  Theorem 2.2.9: the martingale transform of a martingale by a bounded
  predictable process is itself a martingale (discrete stochastic integral).
-/
import Mathlib

namespace HybridVerify

open MeasureTheory ProbabilityTheory

/-- Specification of the (discrete-time) martingale transform: a martingale `M`
    and a bounded predictable process `A`, where `AM n ω = ∑_{k=0}^{n-1}
    A_{k+1}(ω) · (M_{k+1}(ω) − M_k(ω))`. This is the discrete stochastic
    integral. The conclusion (Theorem 2.2.9 — `AM` is itself a martingale) is
    **derived** below, not axiomatized. -/
structure MartingaleTransform {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (𝓕 : Filtration ℕ m0)
    (M A AM : ℕ → Ω → ℝ) : Prop where
  /-- M is a martingale w.r.t. 𝓕. -/
  martingale_M : Martingale M 𝓕 μ
  /-- A is predictable: A (n+1) is 𝓕 n-measurable. -/
  predictable_A : StronglyAdapted 𝓕 (fun n => A (n + 1))
  /-- A is uniformly bounded. -/
  A_bounded : ∃ K : ℝ, ∀ n ω, |A n ω| ≤ K
  /-- The transform value at time n is the discrete stochastic integral. -/
  transform_def : ∀ n ω,
    AM n ω = ∑ k ∈ Finset.range n, A (k + 1) ω * (M (k + 1) ω - M k ω)

namespace MartingaleTransform

variable {Ω : Type*} [m0 : MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℕ m0}
  {M A AM : ℕ → Ω → ℝ}

/-- Each summand `A_{k+1}(ω) · (M_{k+1}(ω) − M_k(ω))` is `𝓕 n`-measurable when `k < n`. -/
private lemma summand_strongly_measurable
    (h : MartingaleTransform μ 𝓕 M A AM) (n k : ℕ) (hk_lt : k < n) :
    StronglyMeasurable[𝓕 n] (fun ω => A (k + 1) ω * (M (k + 1) ω - M k ω)) := by
  have hA : StronglyMeasurable[𝓕 n] (A (k + 1)) :=
    h.predictable_A.stronglyMeasurable_le hk_lt.le
  have hMkp1 : StronglyMeasurable[𝓕 n] (M (k + 1)) :=
    h.martingale_M.stronglyAdapted.stronglyMeasurable_le (Nat.succ_le_of_lt hk_lt)
  have hMk : StronglyMeasurable[𝓕 n] (M k) :=
    h.martingale_M.stronglyAdapted.stronglyMeasurable_le hk_lt.le
  exact hA.mul (hMkp1.sub hMk)

/-- `AM` is adapted to `𝓕`. -/
private lemma adapted_AM (h : MartingaleTransform μ 𝓕 M A AM) : StronglyAdapted 𝓕 AM := by
  intro n
  have heq : AM n = fun ω => ∑ k ∈ Finset.range n,
      A (k + 1) ω * (M (k + 1) ω - M k ω) := funext (h.transform_def n)
  rw [heq]
  refine Finset.stronglyMeasurable_fun_sum (m := 𝓕 n) (M := ℝ) (Finset.range n) fun k hk => ?_
  exact h.summand_strongly_measurable n k (Finset.mem_range.mp hk)

/-- Each summand is integrable: `A_{k+1}` bounded times an integrable martingale increment. -/
private lemma integrable_summand (h : MartingaleTransform μ 𝓕 M A AM) (k : ℕ) :
    Integrable (fun ω => A (k + 1) ω * (M (k + 1) ω - M k ω)) μ := by
  obtain ⟨K, hK⟩ := h.A_bounded
  refine Integrable.bdd_mul (c := K) ?_ ?_ ?_
  · exact (h.martingale_M.integrable (k + 1)).sub (h.martingale_M.integrable k)
  · exact (h.predictable_A.stronglyMeasurable (i := k)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    simpa [Real.norm_eq_abs] using hK (k + 1) ω

/-- `AM n` is integrable (finite sum of integrable summands). -/
private lemma integrable_AM (h : MartingaleTransform μ 𝓕 M A AM) (n : ℕ) :
    Integrable (AM n) μ := by
  have heq : AM n = fun ω => ∑ k ∈ Finset.range n,
      A (k + 1) ω * (M (k + 1) ω - M k ω) := funext (h.transform_def n)
  rw [heq]
  exact integrable_finset_sum _ (fun k _ => h.integrable_summand k)

/-- The martingale step: `AM n =ᵐ μ[AM (n+1) | 𝓕 n]`. The new summand
    `δ = A_{n+1} (M_{n+1} - M_n)` has zero conditional expectation w.r.t. `𝓕 n`
    (pull `A_{n+1}` out, martingale increment is centered), and `AM n` is
    `𝓕 n`-measurable so it equals its own conditional expectation. -/
private lemma step (h : MartingaleTransform μ 𝓕 M A AM) (n : ℕ) :
    AM n =ᵐ[μ] μ[AM (n + 1) | 𝓕 n] := by
  set δ : Ω → ℝ := fun ω => A (n + 1) ω * (M (n + 1) ω - M n ω)
  have hAM_succ_eq : AM (n + 1) = AM n + δ := by
    funext ω
    have e := h.transform_def (n + 1) ω
    rw [Finset.sum_range_succ] at e
    show AM (n + 1) ω = (AM n + δ) ω
    simp only [Pi.add_apply]
    rw [e, ← h.transform_def n ω]
  have hδ_int : Integrable δ μ := h.integrable_summand n
  have hMdiff : μ[M (n + 1) - M n | 𝓕 n] =ᵐ[μ] (0 : Ω → ℝ) := by
    have h1 : μ[M (n + 1) - M n | 𝓕 n] =ᵐ[μ]
              μ[M (n + 1) | 𝓕 n] - μ[M n | 𝓕 n] :=
      condExp_sub (h.martingale_M.integrable (n + 1))
                   (h.martingale_M.integrable n) _
    have h2 : μ[M (n + 1) | 𝓕 n] =ᵐ[μ] M n :=
      h.martingale_M.condExp_ae_eq (Nat.le_succ n)
    have h3 : μ[M n | 𝓕 n] = M n :=
      condExp_of_stronglyMeasurable (𝓕.le n) (h.martingale_M.stronglyAdapted n)
        (h.martingale_M.integrable n)
    filter_upwards [h1, h2] with ω hω1 hω2
    simp [Pi.sub_apply, hω1, hω2, h3]
  have hpull : μ[A (n + 1) * (M (n + 1) - M n) | 𝓕 n] =ᵐ[μ]
               A (n + 1) * μ[M (n + 1) - M n | 𝓕 n] :=
    condExp_mul_of_stronglyMeasurable_left
      (h.predictable_A n) hδ_int
      ((h.martingale_M.integrable (n + 1)).sub (h.martingale_M.integrable n))
  have hδ_condExp : μ[δ | 𝓕 n] =ᵐ[μ] (0 : Ω → ℝ) := by
    refine hpull.trans ?_
    filter_upwards [hMdiff] with ω hω
    simp [Pi.mul_apply, hω]
  have hAM_n_int : Integrable (AM n) μ := h.integrable_AM n
  have hAM_n_meas : StronglyMeasurable[𝓕 n] (AM n) := h.adapted_AM n
  have hcondAM_n : μ[AM n | 𝓕 n] = AM n :=
    condExp_of_stronglyMeasurable (𝓕.le n) hAM_n_meas hAM_n_int
  have hsplit : μ[AM (n + 1) | 𝓕 n] =ᵐ[μ] μ[AM n | 𝓕 n] + μ[δ | 𝓕 n] := by
    rw [hAM_succ_eq]
    exact condExp_add hAM_n_int hδ_int (𝓕 n)
  filter_upwards [hsplit, hδ_condExp] with ω hω1 hω2
  show AM n ω = (μ[AM (n + 1) | 𝓕 n]) ω
  rw [hω1]
  simp [Pi.add_apply, hcondAM_n, hω2]

/-- **Theorem 2.2.9**: the martingale transform of a martingale by a bounded
    predictable process is itself a martingale. -/
theorem transform_is_martingale (h : MartingaleTransform μ 𝓕 M A AM) :
    Martingale AM 𝓕 μ :=
  martingale_nat h.adapted_AM h.integrable_AM h.step

end MartingaleTransform

end HybridVerify
