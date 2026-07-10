/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaUnrestricted

/-! # Summit C — the `IsLocalMartingale` typeclass wrapper

`ItoFormulaUnrestricted.lean` delivers the unrestricted-`C³` Itô formula with the local-martingale
property in **explicit** form. This file packages it into Degenne's `IsLocalMartingale` *typeclass*.

The one missing ingredient was the **adaptedness** of the explicit residual `M` (so that the
`σ_N`-stopped indicator process is `StronglyAdapted`, hence a martingale): `M_t = f(t,B_t) − f(0,B_0)
− ∫₀ᵗ drift`, and the drift primitive `D_t = ∫₀ᵗ drift` is `𝓕_t`-measurable because, after clamping
the integrand's time to `[0,t]` (so each slice is `𝓕_t`-measurable), it is jointly strongly
measurable (Carathéodory: continuous in `s`, `𝓕_t`-measurable in `ω`), and the integral of a jointly
measurable function is measurable (`StronglyMeasurable.integral_prod_right`). With `M` adapted,
`StronglyAdapted.stoppedProcess_indicator` and the all-time agreement
`indistinguishable_on_stochInterval` assemble `Locally (Martingale ∧ cadlag)` with localizer `σ_N`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology
open ItoIntegralL2 ItoIntegralBrownian ItoIntegralProcessLocalMartingaleGeneral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The drift primitive is adapted.** `D_t = ∫₀ᵗ (f_t + ½f_xx)(s, B_s) ds` is
`𝓕_t`-measurable: clamping the integrand's time to `[0,t]` makes every slice `𝓕_t`-measurable
(`B_{min s t}` with `min s t ≤ t`), so the clamped integrand is jointly strongly measurable
(Carathéodory) and the integral over `s` is `𝓕_t`-measurable. -/
lemma driftPrimitive_stronglyMeasurable (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {f_t f_xx : ℝ → ℝ → ℝ}
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2) (t : ℝ≥0) :
    StronglyMeasurable[natFiltration hBmeas t]
      (fun ω ↦ ∫ s in Set.Ioc 0 t,
        (f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω)) ∂timeMeasure) := by
  classical
  -- the time-clamped integrand `g s ω = drift (min s t) ω`
  set g : ℝ≥0 → Ω → ℝ := fun s ω ↦
    f_t (↑(min s t)) (B (min s t) ω) + (1 / 2) * f_xx (↑(min s t)) (B (min s t) ω) with hg
  -- every clamped slice is `𝓕_t`-measurable (`min s t ≤ t`) — proved with `mΩ` still ambient
  have hBmin : ∀ s : ℝ≥0, StronglyMeasurable[natFiltration hBmeas t] (B (min s t)) := fun s ↦
    ((measurable_eval_natFiltration hBmeas (min s t)).mono
      ((natFiltration hBmeas).mono (min_le_right s t)) le_rfl).stronglyMeasurable
  have hg_meas : ∀ s, StronglyMeasurable[natFiltration hBmeas t] (g s) := by
    intro s
    refine StronglyMeasurable.add ?_ (stronglyMeasurable_const.mul ?_)
    · exact (hf_t_cont.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable
        (hBmin s)
    · exact (hf_xx_cont.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable
        (hBmin s)
  -- and `s ↦ g s ω` is continuous (drift continuous, `min` continuous)
  have hg_cont : ∀ ω, Continuous fun s ↦ g s ω := by
    intro ω
    have hdrift : Continuous fun s : ℝ≥0 ↦
        f_t (↑s) (B s ω) + (1 / 2) * f_xx (↑s) (B s ω) :=
      (hf_t_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))).add
        (continuous_const.mul (hf_xx_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))))
    exact hdrift.comp (continuous_id.min continuous_const)
  -- now switch to `𝓕_t` as the ambient σ-algebra for the joint-measurability + integral lemmas
  letI : MeasurableSpace Ω := natFiltration hBmeas t
  -- the uncurried clamped integrand is jointly strongly measurable (Carathéodory + swap + indicator)
  have huncurry : StronglyMeasurable
      (Function.uncurry fun (ω : Ω) (s : ℝ≥0) ↦
        (Set.Ioc 0 t).indicator (fun s ↦ g s ω) s) := by
    have hjoint : StronglyMeasurable (Function.uncurry g) :=
      stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hg_cont hg_meas
    have hswap : StronglyMeasurable (fun p : Ω × ℝ≥0 ↦ g p.2 p.1) :=
      hjoint.comp_measurable measurable_swap
    have heq : (Function.uncurry fun (ω : Ω) (s : ℝ≥0) ↦
          (Set.Ioc 0 t).indicator (fun s ↦ g s ω) s)
        = (Set.univ ×ˢ Set.Ioc 0 t).indicator (fun p : Ω × ℝ≥0 ↦ g p.2 p.1) := by
      funext p
      simp only [Function.uncurry, Set.indicator]
      by_cases hp : p.2 ∈ Set.Ioc 0 t <;> simp [hp]
    rw [heq]
    exact hswap.indicator (MeasurableSet.univ.prod measurableSet_Ioc)
  -- the integral equals the clamped integral (`g = drift` on `(0,t]`), which is `𝓕_t`-measurable
  have hval : (fun ω ↦ ∫ s in Set.Ioc 0 t,
        (f_t (↑s) (B s ω) + (1 / 2) * f_xx (↑s) (B s ω)) ∂timeMeasure)
      = fun ω ↦ ∫ s, (Set.Ioc 0 t).indicator (fun s ↦ g s ω) s ∂timeMeasure := by
    funext ω
    rw [integral_indicator measurableSet_Ioc]
    refine setIntegral_congr_fun measurableSet_Ioc (fun s hs ↦ ?_)
    simp only [hg, min_eq_left hs.2]
  rw [hval]
  exact huncurry.integral_prod_right

/-- **The compensated residual `M` is adapted.** `M_t = f(t,B_t) − f(0,B_0) − D_t` is
`𝓕_t`-measurable: `f(t,B_t)` and `f(0,B_0)` are (`B` adapted, `f` continuous), and `D_t` is by
`driftPrimitive_stronglyMeasurable`. -/
lemma residual_stronglyMeasurable (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {f f_t f_xx : ℝ → ℝ → ℝ}
    (hf_cont : Continuous fun p : ℝ × ℝ ↦ f p.1 p.2)
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2) (t : ℝ≥0) :
    StronglyMeasurable[natFiltration hBmeas t]
      (fun ω ↦ f (t : ℝ) (B t ω) - f 0 (B 0 ω)
        - ∫ s in Set.Ioc 0 t,
            (f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω)) ∂timeMeasure) := by
  have hBt : StronglyMeasurable[natFiltration hBmeas t] (B t) :=
    (measurable_eval_natFiltration hBmeas t).stronglyMeasurable
  have hB0 : StronglyMeasurable[natFiltration hBmeas t] (B 0) :=
    ((measurable_eval_natFiltration hBmeas 0).mono
      ((natFiltration hBmeas).mono zero_le) le_rfl).stronglyMeasurable
  refine (StronglyMeasurable.sub ?_ ?_).sub
    (driftPrimitive_stronglyMeasurable hBmeas hBcont hf_t_cont hf_xx_cont t)
  · exact (hf_cont.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable hBt
  · exact (hf_cont.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable hB0

variable [IsProbabilityMeasure μ]

/-- **The unrestricted-`C³` Itô formula — Summit C, in Degenne's `IsLocalMartingale` typeclass.**
For a general `C³` `f` (six partials, all jointly continuous, **no** growth or boundedness), the
compensated residual `M_t = f(t,B_t) − f(0,B_0) − ∫₀ᵗ(f_t+½f_xx)ds` is everywhere-continuous,
satisfies the Itô identity by construction, and is a genuine **`IsLocalMartingale`** on the
null-augmented Brownian filtration. `M` is adapted (`residual_stronglyMeasurable`), so for the
exit-time localizer `σ_N` the `σ_N`-stopped indicator process of `M` is `StronglyAdapted` and a
martingale — agreeing (via `indistinguishable_on_stochInterval`) with the genuine martingale stopped
from the truncated `Mₙ`. -/
theorem ito_formula_unrestricted (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
    (hf_tt : ∀ t x, HasDerivAt (fun s ↦ f_t s x) (f_tt t x) t)
    (hf_tx : ∀ t x, HasDerivAt (fun u ↦ f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
    (hf_xxx : ∀ t x, HasDerivAt (fun u ↦ f_xx t u) (f_xxx t x) x)
    (hf_cont : Continuous fun p : ℝ × ℝ ↦ f p.1 p.2)
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)
    (hf_tt_cont : Continuous fun p : ℝ × ℝ ↦ f_tt p.1 p.2)
    (hf_tx_cont : Continuous fun p : ℝ × ℝ ↦ f_tx p.1 p.2)
    (hf_xxx_cont : Continuous fun p : ℝ × ℝ ↦ f_xxx p.1 p.2) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ ω, Continuous fun t ↦ M t ω) ∧
      IsLocalMartingale M (augFiltration (μ := μ) hBmeas) μ ∧
      (∀ t : ℝ≥0, (fun ω ↦ f (t : ℝ) (B t ω) - f 0 (B 0 ω)) =ᵐ[μ]
        (fun ω ↦ M t ω + ∫ s in Set.Ioc 0 t,
          (f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω)) ∂timeMeasure)) := by
  classical
  set M : ℝ≥0 → Ω → ℝ := fun t ω ↦
    f (t : ℝ) (B t ω) - f 0 (B 0 ω)
      - ∫ s in Set.Ioc 0 t, (f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω))
        ∂timeMeasure with hM
  have hMcont : ∀ ω, Continuous fun t ↦ M t ω := by
    intro ω
    simp only [hM]
    exact ((hf_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))).sub continuous_const).sub
      (continuous_timeMeasure_primitive
        ((hf_t_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))).add
          (continuous_const.mul (hf_xx_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))))))
  have hMadapt : MeasureTheory.StronglyAdapted (augFiltration (μ := μ) hBmeas) M := by
    intro i
    refine (residual_stronglyMeasurable hBmeas hBcont hf_cont hf_t_cont hf_xx_cont i).mono ?_
    rw [augFiltration_apply]; exact le_sup_left
  have hMcadlag : ∀ ω, IsCadlag fun i ↦ M i ω := fun ω ↦
    ⟨fun _ ↦ (hMcont ω).continuousWithinAt,
      fun x ↦ ⟨M x ω, (hMcont ω).continuousWithinAt.tendsto⟩⟩
  -- the localized-form data: a localizing sequence and per-`N` true martingales agreeing with `M`
  obtain ⟨M', _, hform', σ, hσloc, hN⟩ :=
    ito_formula_unrestricted_local hB hBmeas hBcont hf_t hf_tt hf_tx hf_x hf_xx hf_xxx
      hf_cont hf_t_cont hf_x_cont hf_xx_cont hf_tt_cont hf_tx_cont hf_xxx_cont
  have hMM' : ∀ t, (fun ω ↦ M t ω) =ᵐ[μ] fun ω ↦ M' t ω := by
    intro t
    filter_upwards [hform' t] with ω hω
    simp only [hM]; linarith [hω]
  refine ⟨M, hMcont, ?_,
    fun t ↦ Filter.Eventually.of_forall fun ω ↦ by simp only [hM]; ring⟩
  refine ⟨σ, hσloc, fun N ↦ ?_⟩
  obtain ⟨Mₙ, hMₙmart, hMₙcont, hagreeMₙ⟩ := hN N
  have hMₙcadlag : ∀ ω, IsCadlag fun i ↦ Mₙ i ω := fun ω ↦
    ⟨fun _ ↦ (hMₙcont ω).continuousWithinAt,
      fun x ↦ ⟨Mₙ x ω, (hMₙcont ω).continuousWithinAt.tendsto⟩⟩
  have hagreeM : ∀ t : ℝ≥0, ∀ᵐ ω ∂μ, (t : WithTop ℝ≥0) ≤ σ N ω → M t ω = Mₙ t ω := by
    intro t
    filter_upwards [hMM' t, hagreeMₙ t] with ω hMM hag hle
    rw [hMM]; exact hag hle
  have hindist : ∀ᵐ ω ∂μ, ⊥ < σ N ω → ∀ u : ℝ≥0,
      (u : WithTop ℝ≥0) ≤ σ N ω → M u ω = Mₙ u ω :=
    indistinguishable_on_stochInterval hMcont hMₙcont hagreeM
  set τN : Ω → WithTop ℝ≥0 := σ N with hτN
  have hτstop : IsStoppingTime (augFiltration (μ := μ) hBmeas) τN := hσloc.isStoppingTime N
  have hZmart : Martingale (stoppedProcess (fun i ↦ {ω | ⊥ < τN ω}.indicator (Mₙ i)) τN)
      (augFiltration (μ := μ) hBmeas) μ :=
    hMₙmart.stoppedProcess_indicator (fun ω ↦ (hMₙcadlag ω).right_continuous) hτstop
  -- `Y =ᵐ Z` at each time (indistinguishability handles the random evaluation point)
  have hYZ : ∀ i, (fun ω ↦ stoppedProcess (fun j ↦ {ω | ⊥ < τN ω}.indicator (M j)) τN i ω)
      =ᵐ[μ] fun ω ↦ stoppedProcess (fun j ↦ {ω | ⊥ < τN ω}.indicator (Mₙ j)) τN i ω := by
    intro i
    filter_upwards [hindist] with ω hω
    by_cases hpos : ⊥ < τN ω
    · have hmem : ω ∈ {ω | ⊥ < τN ω} := hpos
      rcases le_total (i : WithTop ℝ≥0) (τN ω) with hle | hge
      · rw [stoppedProcess_eq_of_le hle, stoppedProcess_eq_of_le hle,
          Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        exact hω hpos i hle
      · rw [stoppedProcess_eq_of_ge hge, stoppedProcess_eq_of_ge hge,
          Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hge)
        refine hω hpos (τN ω).untopA (le_of_eq ?_)
        rw [← hv]; rfl
    · have hnmem : ω ∉ {ω | ⊥ < τN ω} := hpos
      have hle : τN ω ≤ (i : WithTop ℝ≥0) := (not_lt.mp hpos).trans bot_le
      rw [stoppedProcess_eq_of_ge hle, stoppedProcess_eq_of_ge hle,
        Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hnmem]
  refine ⟨⟨hMadapt.stoppedProcess_indicator (fun ω ↦ (hMcadlag ω).right_continuous) hτstop,
    fun i j hij ↦ ?_⟩, isStable_isCadlag M hMcadlag τN hτstop⟩
  calc μ[fun ω ↦ stoppedProcess (fun j ↦ {ω | ⊥ < τN ω}.indicator (M j)) τN j ω
          | augFiltration (μ := μ) hBmeas i]
      =ᵐ[μ] μ[fun ω ↦ stoppedProcess (fun j ↦ {ω | ⊥ < τN ω}.indicator (Mₙ j)) τN j ω
          | augFiltration (μ := μ) hBmeas i] := condExp_congr_ae (hYZ j)
    _ =ᵐ[μ] (fun ω ↦ stoppedProcess (fun j ↦ {ω | ⊥ < τN ω}.indicator (Mₙ j)) τN i ω) :=
        hZmart.2 i j hij
    _ =ᵐ[μ] (fun ω ↦ stoppedProcess (fun j ↦ {ω | ⊥ < τN ω}.indicator (M j)) τN i ω) :=
        (hYZ i).symm

end MathFin
