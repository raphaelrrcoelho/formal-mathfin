/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralL2Dense

/-!
# The unbounded-horizon Itô integral as an L² process

B2 (`ItoIntegralL2Dense`) built the **terminal** `[0,∞)` Itô integral
`itoIntegralL2 : Lp 2 trim_full →L[ℝ] Lp 2 μ` over the **horizon-independent**
predictable integrand `f` (the σ-finite completion). This file lifts it to a
**process** `itoProcessL2Inf t f := E[∫₀^∞ f dB | 𝓕_t]` — the
conditional-expectation projection of the terminal integral onto the natural
filtration `𝓕_t`, exactly mirroring the finite-horizon `itoProcessCLM`
(`ItoIntegralProcessGeneral`) but with the horizon-independent terminal integral.

Because the integrand no longer depends on the horizon, the L² **martingale
property** (`itoProcessL2Inf_isMartingale`) and **adaptedness**
(`itoProcessL2Inf_aeStronglyMeasurable`) hold on all of `ℝ≥0` directly from the
conditional-expectation tower — no integrand gluing is needed.

## The `[0,∞)` continuous-local-martingale arc

This is **step 1** (the L² process). Remaining:
* **step 2** — horizon consistency: `itoProcessL2Inf t f =ᵐ itoProcessCLM T t (f|[0,T])`
  for `t ≤ T` (the Itô increment-independence lemma `E[∫₀^∞ | 𝓕_T] = ∫₀ᵀ`);
* **step 3** — the glued continuous modification on `[0,∞)` (the finite gate per
  horizon `T = n`, glued by `indistinguishable_of_modification_on`);
* **step 4** — the `IsLocalMartingale` on the null-augmented filtration (reusing
  `condExp_sup_nulls` / `augFiltration` from the `[0,T]` follow-on).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcessL2Infinite

open ItoIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

/-- **The unbounded-horizon Itô process** `(f●B)_t = E[∫₀^∞ f dB | 𝓕_t]`: the
conditional-expectation projection of the terminal `[0,∞)` integral `itoIntegralL2 f`
onto `𝓕_t`. The horizon-independent analogue of `itoProcessCLM`. -/
noncomputable def itoProcessL2Inf (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) →L[ℝ] Lp ℝ 2 μ :=
  ((lpMeas ℝ ℝ (natFiltration hBmeas t) 2 μ).subtypeL.comp
    (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t))).comp (itoIntegralL2 hB hBmeas)

/-- Unfold of the process to the `condExpL2` projection of the terminal integral
(coerced from the `𝓕_t`-measurable subspace into `Lp 2 μ`). -/
lemma itoProcessL2Inf_apply (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    itoProcessL2Inf hB t hBmeas f
      = (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t) (itoIntegralL2 hB hBmeas f) : Lp ℝ 2 μ) :=
  rfl

/-- **The unbounded-horizon Itô process is an L² martingale.** For `i ≤ j`,
`E[(f●B)_j | 𝓕_i] =ᵐ (f●B)_i` — directly from the conditional-expectation tower,
since each value is `E[∫₀^∞ f dB | 𝓕_k]`. -/
theorem itoProcessL2Inf_isMartingale (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) {i j : ℝ≥0} (hij : i ≤ j) :
    μ[(itoProcessL2Inf hB j hBmeas f : Ω → ℝ) | natFiltration hBmeas i]
      =ᵐ[μ] (itoProcessL2Inf hB i hBmeas f : Ω → ℝ) := by
  have hbridge : ∀ k : ℝ≥0,
      (itoProcessL2Inf hB k hBmeas f : Ω → ℝ)
        =ᵐ[μ] μ[(itoIntegralL2 hB hBmeas f : Ω → ℝ) | natFiltration hBmeas k] := by
    intro k
    rw [itoProcessL2Inf_apply]
    have h := (Lp.memLp (itoIntegralL2 hB hBmeas f)).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) ((natFiltration hBmeas).le k)
    rwa [Lp.toLp_coeFn] at h
  calc μ[(itoProcessL2Inf hB j hBmeas f : Ω → ℝ) | natFiltration hBmeas i]
      =ᵐ[μ] μ[μ[(itoIntegralL2 hB hBmeas f : Ω → ℝ) | natFiltration hBmeas j]
              | natFiltration hBmeas i] := condExp_congr_ae (hbridge j)
    _ =ᵐ[μ] μ[(itoIntegralL2 hB hBmeas f : Ω → ℝ) | natFiltration hBmeas i] :=
        condExp_condExp_of_le ((natFiltration hBmeas).mono hij) ((natFiltration hBmeas).le j)
    _ =ᵐ[μ] (itoProcessL2Inf hB i hBmeas f : Ω → ℝ) := (hbridge i).symm

/-- **a.e.-adaptedness.** `(f●B)_t` is a.e. `𝓕_t`-measurable: it is the `condExpL2`
projection onto the `𝓕_t`-measurable subspace. -/
theorem itoProcessL2Inf_aeStronglyMeasurable (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    AEStronglyMeasurable[natFiltration hBmeas t]
      (itoProcessL2Inf hB t hBmeas f : Ω → ℝ) μ := by
  rw [itoProcessL2Inf_apply]
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    (condExpL2 ℝ ℝ ((natFiltration hBmeas).le t) (itoIntegralL2 hB hBmeas f)).2

/-- **The Itô-isometry contraction.** `‖(f●B)_t‖ ≤ ‖f‖`: conditional expectation is
an L² contraction and the terminal integral is an isometry (`itoIntegralL2_norm`). -/
theorem itoProcessL2Inf_norm_le (t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod)) :
    ‖itoProcessL2Inf hB t hBmeas f‖ ≤ ‖f‖ := by
  rw [itoProcessL2Inf_apply]
  exact (norm_condExpL2_le ((natFiltration hBmeas).le t) (itoIntegralL2 hB hBmeas f)).trans
    (itoIntegralL2_norm hB hBmeas f).le

end ItoIntegralProcessL2Infinite
end MathFin
