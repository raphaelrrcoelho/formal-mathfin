/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaTD
public import MathFin.Foundations.ItoIntegralProcessLocalMartingaleInfinite

/-! # The time-dependent Itô formula as a process — Itô's lemma as a semimartingale decomposition

The terminal Itô formula `ito_formula_td_L2_bddDeriv` is a single-time statement: it decomposes
`f(T, B_T) − f(0, B_0)` at the *fixed horizon* `T` as `itoIntegralCLM_T gfx + drift`, an `Lp 2 μ`
element. This file lifts it to a **process identity** holding simultaneously for every `t ≤ T`:

  `f(t, B_t) − f(0, B_0) =ᵐ (gfx ● B)_t + ∫₀ᵗ (f_t + ½f_xx)(s, B_s) ds`,

where `(gfx ● B)_t = itoProcessL2Inf t F` is the genuine Itô-integral **process** — a continuous
`L²` martingale that, on the null-augmented Brownian filtration, admits an everywhere-continuous
**local-martingale** modification (`exists_continuous_localMartingale_modification_infinite`). This
is *Itô's lemma as a semimartingale decomposition*: the compensated process
`M_t = f(t, B_t) − f(0, B_0) − ∫₀ᵗ drift` is (a modification of) a continuous local martingale.

## The construction (entirely inside the Itô tower — no Markov property, no PDE)

The single new ingredient is the **canonical witness** now exposed by
`ito_formula_td_L2_bddDeriv_explicit`: the terminal integrand `gfx` is the explicit `L²` class
`[f_x(s, B_s)]` (not a bare existential). With that:

* **Zero-extension** (`exists_fullHorizon_extension`): the horizon-`T` witness `gfx`, supported on
  `(0,T]`, extends to a `[0,∞)` predictable `L²` integrand `F = 𝟙_{(0,T]} · gfx ∈ Lp 2 trim_full`
  (bounded ⇒ `∫₀ᵀ E[f_x²] < ∞`), agreeing with `gfx` on the band — `restrictToBand T F = gfx`.
* **Horizon consistency** (the existing `itoProcessL2Inf_eq_itoProcessCLM`): for each `t ≤ T` the
  unbounded-horizon process at `t` is the finite-horizon integral of the band restriction, and the
  band restriction of `F` is again `[f_x]`, so it matches the horizon-`t` terminal witness `gfxₜ`.

Hence at every `t ≤ T` the terminal formula at horizon `t` reads `M_t =ᵐ itoIntegralCLM_t gfxₜ`,
and `itoIntegralCLM_t gfxₜ = (itoProcessCLM t t) gfxₜ = itoProcessL2Inf t F` — one process, all `t`.
The martingale, continuity and local-martingale structure come for free from the `[0,∞)` tower.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral
open ItoIntegralProcessL2Infinite ItoIntegralProcessLocalMartingaleGeneral ItoLocalMartingale
open ItoLocalMartingaleInfinite

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

/-- **Zero-extension to the full horizon.** A finite-horizon predictable `L²` integrand `g`
(over the band `(0,T]`) extends to an unbounded-horizon predictable `L²` integrand
`F = 𝟙_{(0,T]} · g ∈ Lp 2 trim_full` agreeing with `g` on the band, from which
`restrictToBand T F =ᵐ g` follows (re-reading the same function against the smaller measure).
The bridge that feeds a finite-horizon Itô-formula integrand to the `[0,∞)` process tower. The
predictability over the full product is the extension by zero of `g`'s predictable representative
across the predictable rectangle `(0,T] × Ω`; the `L²` finiteness is `g`'s (the indicator only
removes mass). -/
lemma exists_fullHorizon_extension (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (g : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas)) :
    ∃ F : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod),
      (⇑F : ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (μ := μ) T hBmeas] ⇑g := by
  classical
  set m := (natFiltration (mΩ := mΩ) hBmeas).predictable
  have hSpred : MeasurableSet[m] (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := natFiltration hBmeas) 0 T
      MeasurableSet.univ
  -- a predictable strongly-measurable representative of `g`
  set h : ℝ≥0 × Ω → ℝ := (Lp.aestronglyMeasurable g).mk ⇑g
  have hh_sm : StronglyMeasurable[m] h := (Lp.aestronglyMeasurable g).stronglyMeasurable_mk
  have hgh : (⇑g : ℝ≥0 × Ω → ℝ) =ᵐ[trimMeasure_T (μ := μ) T hBmeas] h :=
    (Lp.aestronglyMeasurable g).ae_eq_mk
  -- the zero-extension
  set Ffn : ℝ≥0 × Ω → ℝ := (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)).indicator h with hFfn
  have hFfn_sm : StronglyMeasurable[m] Ffn := hh_sm.indicator hSpred
  have hSrestrict : ((timeMeasure.prod μ).trim
        (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod).restrict
        (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) = trimMeasure_T (μ := μ) T hBmeas :=
    (trimMeasure_T_eq_restrict T hBmeas).symm
  have hmem : MemLp Ffn 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod) := by
    refine ⟨hFfn_sm.aestronglyMeasurable, ?_⟩
    rw [hFfn, eLpNorm_indicator_eq_eLpNorm_restrict hSpred, hSrestrict, ← eLpNorm_congr_ae hgh]
    exact (Lp.memLp g).2
  refine ⟨hmem.toLp Ffn, ?_⟩
  have hle : trimMeasure_T (μ := μ) T hBmeas ≤ (timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod := by
    rw [trimMeasure_T_eq_restrict]; exact Measure.restrict_le_self
  calc (⇑(hmem.toLp Ffn) : ℝ≥0 × Ω → ℝ)
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas] Ffn :=
        (MemLp.coeFn_toLp hmem).filter_mono (ae_mono hle)
    _ =ᵐ[trimMeasure_T (μ := μ) T hBmeas] h := by
        rw [hFfn, ← hSrestrict]; exact indicator_ae_eq_restrict hSpred
    _ =ᵐ[trimMeasure_T (μ := μ) T hBmeas] ⇑g := hgh.symm

/-- **The time-dependent Itô formula as a process (semimartingale decomposition).** For `f(t,x)`
with the `C^{1,2}`-with-bounds package, there is a `[0,∞)` predictable `L²` integrand `F`
(realizing `f_x(s, B_s)` on `(0,T]`) such that, **for every `t ≤ T` simultaneously**,

  `f(t, B_t) − f(0, B_0) =ᵐ (itoProcessL2Inf t F) + ∫₀ᵗ (f_t + ½f_xx)(s, B_s) ds`,

with the stochastic term the Itô-integral process `(f_x(·,B) ● B)_t`. That process is a continuous
`L²` martingale, and admits an everywhere-continuous **local-martingale** modification on the
null-augmented Brownian filtration — so the compensated process `f(t,B_t) − f(0,B_0) − ∫₀ᵗ drift`
is (a modification of) a continuous local martingale. -/
theorem ito_formula_td_process
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous (fun s : ℝ≥0 => B s ω))
    (T : ℝ≥0) {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s => f s x) (f_t t x) t)
    (hf_tt : ∀ t x, HasDerivAt (fun s => f_t s x) (f_tt t x) t)
    (hf_tx : ∀ t x, HasDerivAt (fun u => f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u => f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u => f_x t u) (f_xx t x) x)
    (hf_xxx : ∀ t x, HasDerivAt (fun u => f_xx t u) (f_xxx t x) x)
    (hf_x_cont : Continuous fun p : ℝ × ℝ => f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ => f_xx p.1 p.2)
    {Ct C1 C2 Ctt Ctx Cxxx : ℝ}
    (hbd_t : ∀ t x, |f_t t x| ≤ Ct) (hbd_x : ∀ t x, |f_x t x| ≤ C1)
    (hbd_xx : ∀ t x, |f_xx t x| ≤ C2)
    (hbd_tt : ∀ t x, |f_tt t x| ≤ Ctt) (hbd_tx : ∀ t x, |f_tx t x| ≤ Ctx)
    (hbd_xxx : ∀ t x, |f_xxx t x| ≤ Cxxx) :
    ∃ F : Lp ℝ 2 ((timeMeasure.prod μ).trim
      (natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod),
      (∀ t : ℝ≥0, t ≤ T →
        (fun ω => f (t : ℝ) (B t ω) - f 0 (B 0 ω)) =ᵐ[μ]
          (fun ω => (itoProcessL2Inf hB t hBmeas F) ω
            + ∫ s in Set.Ioc 0 t,
                (f_t s (B s ω) + (1 / 2) * f_xx s (B s ω)) ∂ItoIntegralL2.timeMeasure)) ∧
      (∀ (i j : ℝ≥0), i ≤ j →
        μ[(itoProcessL2Inf hB j hBmeas F : Ω → ℝ) | natFiltration hBmeas i]
          =ᵐ[μ] (itoProcessL2Inf hB i hBmeas F : Ω → ℝ)) ∧
      (∃ X : ℝ≥0 → Ω → ℝ,
        (∀ t, X t =ᵐ[μ] (itoProcessL2Inf hB t hBmeas F : Ω → ℝ)) ∧
        (∀ ω, Continuous fun t => X t ω) ∧
        IsLocalMartingale X (augFiltration (μ := μ) hBmeas) μ) := by
  classical
  -- the explicit horizon-`T` witness `gfx_T = [f_x(·, B)]`
  obtain ⟨gfxT, hgfxT_eq, -⟩ := ito_formula_td_L2_bddDeriv_explicit hB hBmeas hBcont T
    hf_t hf_tt hf_tx hf_x hf_xx hf_xxx hf_x_cont hf_xx_cont hbd_t hbd_x hbd_xx hbd_tt hbd_tx hbd_xxx
  -- extend it to a `[0,∞)` integrand `F` agreeing with `gfx_T` (hence `[f_x]`) on `(0,T]`
  obtain ⟨F, hF_eq⟩ := exists_fullHorizon_extension T hBmeas gfxT
  have hF_fx : (⇑F : ℝ≥0 × Ω → ℝ)
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun z => f_x z.1 (B z.1 z.2) := hF_eq.trans hgfxT_eq
  refine ⟨F, fun t ht => ?_, fun i j hij => itoProcessL2Inf_isMartingale hB hBmeas F hij,
    exists_continuous_localMartingale_modification_infinite hB hBmeas hBcont (f := F)⟩
  -- the explicit horizon-`t` witness and terminal identity at `t`
  obtain ⟨gfxt, hgfxt_eq, hMt⟩ := ito_formula_td_L2_bddDeriv_explicit hB hBmeas hBcont t
    hf_t hf_tt hf_tx hf_x hf_xx hf_xxx hf_x_cont hf_xx_cont hbd_t hbd_x hbd_xx hbd_tt hbd_tx hbd_xxx
  have hle_tT : trimMeasure_T (μ := μ) t hBmeas ≤ trimMeasure_T (μ := μ) T hBmeas := by
    rw [trimMeasure_T_eq_restrict, trimMeasure_T_eq_restrict]
    exact Measure.restrict_mono
      (Set.prod_mono (Set.Ioc_subset_Ioc_right ht) (subset_refl _)) le_rfl
  -- the band restriction of `F` to `[0,t]` is the horizon-`t` witness `gfxₜ`
  have hrestr : restrictToBand (μ := μ) t hBmeas F = gfxt := by
    refine Lp.ext ((restrictToBand_coeFn t hBmeas F).trans ?_)
    exact (hF_fx.filter_mono (ae_mono hle_tT)).trans hgfxt_eq.symm
  -- the stochastic term is the Itô process `(f_x ● B)_t`
  have hstoch_lp : itoProcessL2Inf hB t hBmeas F = itoIntegralCLM_T hB t hBmeas gfxt := by
    rw [itoProcessL2Inf_eq_itoProcessCLM hB t t hBmeas (le_refl t) F, hrestr, itoProcessCLM_terminal_eq]
  filter_upwards [hMt] with ω hω
  show f (t : ℝ) (B t ω) - f 0 (B 0 ω)
      = (itoProcessL2Inf hB t hBmeas F) ω
        + ∫ s in Set.Ioc 0 t,
            (f_t s (B s ω) + (1 / 2) * f_xx s (B s ω)) ∂ItoIntegralL2.timeMeasure
  rw [hstoch_lp]; exact hω

end MathFin
