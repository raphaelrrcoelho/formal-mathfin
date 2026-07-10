/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaLocalized
public import MathFin.Foundations.ItoFormulaProcess
public import MathFin.Foundations.ExitTime

/-! # The unrestricted-`C³` Itô formula via stopping-time localization (Summit C)

The process Itô formula `ito_formula_td_process` requires **globally bounded** derivatives. This
file removes the bound entirely: for a general `C³` `f` (the six partials continuous, no growth
or boundedness hypothesis), the compensated process

  `M_t = f(t, B_t) − f(0, B_0) − ∫₀ᵗ (f_t + ½f_xx)(s, B_s) ds`

is a **continuous local martingale** on the null-augmented Brownian filtration.

## Strategy — localize in space *and* time, glue with the exit times

The single gating ingredient is the genuine localizing sequence `exitTime` (`ExitTime.lean`).
The local-martingale property is delivered here in **explicit form** (a localizing sequence + per-`N`
continuous true martingales agreeing with `M` on the stochastic intervals) — this *is* the textbook
definition of a continuous local martingale; the packaging into Degenne's `IsLocalMartingale`
*typeclass* is `ito_formula_unrestricted` in `ItoFormulaUnrestrictedLocMart.lean` (it consumes the
all-time-agreement step below). Three steps:

* **Double truncation** (this section). `fTrunc N (t, x) = f(cut N t, cut N x)` cuts **both**
  arguments smoothly onto the compact square `[−M₀(N+1), M₀(N+1)]²`, on which the continuous
  partials of `f` are bounded by constants. The chain rule gives `fTrunc N`'s six partials in
  closed form, each globally bounded — so `ito_formula_td_process` applies, giving a `[0,∞)`
  integrand `Fᴺ` and the truncated Itô identity. The Itô integral of `Fᴺ` admits a global
  **true-martingale** continuous modification `Mₙ` (`exists_continuous_martingale_modification_infinite`).
* **Agreement on `{· ≤ σ_N}`**, where `σ_N = min(exitTime N, N)`. There `t ≤ N` (time cut inert)
  and `|B_s| ≤ N` for `s ≤ t` (space cut inert), so `fTrunc N = f`, `drift_trunc = drift`, hence
  `Mₙ_t =ᵐ M_t` on `{t ≤ σ_N}` — the per-`t` agreement the headline `ito_formula_unrestricted_local`
  returns. As `N → ∞` the exit times escape, so `M` is *locally* a true martingale.
* **All-time indistinguishability** (`indistinguishable_on_stochInterval`). The per-`t` agreement
  lifts to `∀ᵐ ω, ∀ u ≤ σ_N, M_u = Mₙ_u` (continuity + countable rationals + `Set.EqOn.closure`).
  This is the all-time-agreement crux consumed by the `IsLocalMartingale`-typeclass wrapper
  (`ItoFormulaUnrestrictedLocMart.lean`, `ito_formula_unrestricted`), which stops the indicator
  processes and invokes `Martingale.stoppedProcess_indicator`. That wrapper is **complete** — the
  one remaining ingredient, the drift-integral adaptedness of `M`, is discharged via
  `StronglyMeasurable.integral_prod_right` (a time-clamped Carathéodory argument).

The time cut is essential: `cut N` confines `x`, but a general `C³` `f` has `t`-derivatives
unbounded over `t ∈ ℝ`; capping the localizer at `N` keeps `t ≤ N` so the time cut is inert
exactly where the agreement is used.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology
open ItoIntegralL2 ItoIntegralBrownian ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral
open ItoIntegralProcessL2Infinite ItoIntegralProcessLocalMartingaleGeneral

namespace SmoothTrunc

/-- On the plateau `|y| < 1` where `φ = id`, the second derivative vanishes: `φ'' y = 0`
(`φ'` is locally the constant `1`, so its derivative is `0`). -/
lemma phi''_eq_zero_of_lt (S : SmoothTrunc) {y : ℝ} (hy : |y| < 1) : S.φ'' y = 0 := by
  have h2 : HasDerivAt S.φ' 0 y :=
    (hasDerivAt_const y (1 : ℝ)).congr_of_eventuallyEq (by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hy] with z hz
      exact S.phi'_eq_one_of_lt hz)
  exact (S.hasDeriv₂ y).unique h2

/-- For `|x| < n + 1` the second cutoff derivative vanishes: `φₙ''(x) = 0` (it is the identity
there). -/
lemma cutD2_eq_zero_of_abs_lt (S : SmoothTrunc) {n : ℕ} {x : ℝ} (hx : |x| < (n : ℝ) + 1) :
    S.cutD2 n x = 0 := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [cutD2, S.phi''_eq_zero_of_lt (by rw [abs_div, abs_of_pos hn1, div_lt_one hn1]; exact hx),
    zero_div]

end SmoothTrunc

/-- **The drift primitive is continuous.** `t ↦ ∫_{(0,t]} h dτ` for continuous `h` and
`τ = timeMeasure` (finite on compacts): dominated convergence, the integrand `t ↦ 𝟙_{(0,t]}(s)·h(s)`
having its only discontinuity in `t` at the τ-null point `t = s`. -/
lemma continuous_timeMeasure_primitive {h : ℝ≥0 → ℝ} (hh : Continuous h) :
    Continuous fun t : ℝ≥0 ↦ ∫ s in Set.Ioc 0 t, h s ∂ItoIntegralL2.timeMeasure := by
  have hrw : (fun t : ℝ≥0 ↦ ∫ s in Set.Ioc 0 t, h s ∂ItoIntegralL2.timeMeasure)
      = fun t ↦ ∫ s, (Set.Ioc 0 t).indicator h s ∂ItoIntegralL2.timeMeasure := by
    funext t; rw [integral_indicator measurableSet_Ioc]
  rw [hrw]
  refine continuous_iff_continuousAt.mpr fun t₀ ↦ ?_
  refine continuousAt_of_dominated
    (bound := fun s ↦ (Set.Icc 0 (t₀ + 1)).indicator (fun u ↦ |h u|) s)
    (Filter.Eventually.of_forall fun t ↦
      (hh.stronglyMeasurable.indicator measurableSet_Ioc).aestronglyMeasurable)
    (Filter.eventually_of_mem (Iio_mem_nhds (lt_add_one t₀)) fun t ht ↦
      Filter.Eventually.of_forall fun s ↦ ?_)
    ?_ ?_
  · -- pointwise domination by `𝟙_{[0,t₀+1]}·|h|`
    by_cases hmem : s ∈ Set.Ioc 0 t
    · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs,
        Set.indicator_of_mem (show s ∈ Set.Icc 0 (t₀ + 1) from
          ⟨zero_le, le_of_lt (lt_of_le_of_lt hmem.2 ht)⟩)]
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      exact Set.indicator_nonneg (fun s _ ↦ abs_nonneg _) s
  · -- the dominator is integrable (continuous on a compact, finite measure there)
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (hh.abs.continuousOn.integrableOn_compact isCompact_Icc)
  · -- a.e.-`s` continuity in `t` (off the null point `t₀`)
    have hne : ∀ᵐ s ∂ItoIntegralL2.timeMeasure, s ≠ t₀ := by
      rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]
      exact ItoIntegralL2.timeMeasure_singleton t₀
    filter_upwards [hne] with s hs
    by_cases hs0 : 0 < s
    · rcases lt_or_gt_of_ne hs with hlt | hgt
      · refine (continuousAt_congr ?_).mpr (continuousAt_const (y := h s))
        filter_upwards [Ioi_mem_nhds hlt] with t ht
        exact Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hs0, le_of_lt ht⟩) h
      · refine (continuousAt_congr ?_).mpr (continuousAt_const (y := (0 : ℝ)))
        filter_upwards [Iio_mem_nhds hgt] with t ht
        exact Set.indicator_of_notMem (fun hmem ↦ absurd (Set.mem_Ioc.mp hmem).2 (not_le.mpr ht)) h
    · refine (continuousAt_congr ?_).mpr (continuousAt_const (y := (0 : ℝ)))
      have hs00 : s = 0 := le_antisymm (not_lt.mp hs0) (zero_le)
      filter_upwards with t
      exact Set.indicator_of_notMem (by rw [hs00]; exact fun hmem ↦ lt_irrefl 0 (Set.mem_Ioc.mp hmem).1) h

namespace SummitC

variable {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}

/-- The double cutoff `fTrunc N (t,x) = f(φₙ t, φₙ x)` — `f` confined to the compact square. -/
noncomputable def fTrunc (f : ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x : ℝ) : ℝ :=
  f (S.cut N t) (S.cut N x)
/-- `∂_t fTrunc = f_t(φₙ t, φₙ x)·φₙ'(t)`. -/
noncomputable def fTruncT (f_t : ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x : ℝ) : ℝ :=
  f_t (S.cut N t) (S.cut N x) * S.cutD1 N t
/-- `∂_x fTrunc = f_x(φₙ t, φₙ x)·φₙ'(x)`. -/
noncomputable def fTruncX (f_x : ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x : ℝ) : ℝ :=
  f_x (S.cut N t) (S.cut N x) * S.cutD1 N x
/-- `∂_tt fTrunc = f_tt·(φₙ' t)² + f_t·φₙ''(t)`. -/
noncomputable def fTruncTT (f_t f_tt : ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x : ℝ) : ℝ :=
  f_tt (S.cut N t) (S.cut N x) * (S.cutD1 N t * S.cutD1 N t) + f_t (S.cut N t) (S.cut N x) * S.cutD2 N t
/-- `∂_tx fTrunc = f_tx·φₙ'(x)·φₙ'(t)`. -/
noncomputable def fTruncTX (f_tx : ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x : ℝ) : ℝ :=
  f_tx (S.cut N t) (S.cut N x) * S.cutD1 N x * S.cutD1 N t
/-- `∂_xx fTrunc = f_xx·(φₙ' x)² + f_x·φₙ''(x)`. -/
noncomputable def fTruncXX (f_x f_xx : ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x : ℝ) : ℝ :=
  f_xx (S.cut N t) (S.cut N x) * (S.cutD1 N x * S.cutD1 N x) + f_x (S.cut N t) (S.cut N x) * S.cutD2 N x
/-- `∂_xxx fTrunc = f_xxx·(φₙ' x)³ + 3 f_xx·φₙ'(x)·φₙ''(x) + f_x·φₙ'''(x)`. -/
noncomputable def fTruncXXX (f_x f_xx f_xxx : ℝ → ℝ → ℝ) (S : SmoothTrunc) (N : ℕ) (t x : ℝ) : ℝ :=
  f_xxx (S.cut N t) (S.cut N x) * (S.cutD1 N x * S.cutD1 N x * S.cutD1 N x)
    + 3 * f_xx (S.cut N t) (S.cut N x) * S.cutD1 N x * S.cutD2 N x
    + f_x (S.cut N t) (S.cut N x) * S.cutD3 N x

/-- `∂_t fTrunc` exists with value `fTruncT` (chain rule through the time cut). -/
lemma fTrunc_hasDerivAt_t (hf_t : ∀ t x, HasDerivAt (fun s ↦ f s x) (f_t t x) t)
    (S : SmoothTrunc) (N : ℕ) (t x : ℝ) :
    HasDerivAt (fun s ↦ fTrunc f S N s x) (fTruncT f_t S N t x) t :=
  (hf_t (S.cut N t) (S.cut N x)).comp t (S.cut_hasDerivAt N t)

/-- `∂_x fTrunc` exists with value `fTruncX` (chain rule through the space cut). -/
lemma fTrunc_hasDerivAt_x (hf_x : ∀ t x, HasDerivAt (fun u ↦ f t u) (f_x t x) x)
    (S : SmoothTrunc) (N : ℕ) (t x : ℝ) :
    HasDerivAt (fun u ↦ fTrunc f S N t u) (fTruncX f_x S N t x) x :=
  (hf_x (S.cut N t) (S.cut N x)).comp x (S.cut_hasDerivAt N x)

/-- `∂_t fTruncT = fTruncTT` (product rule, `t`-derivative). -/
lemma fTrunc_hasDerivAt_tt (hf_tt : ∀ t x, HasDerivAt (fun s ↦ f_t s x) (f_tt t x) t)
    (S : SmoothTrunc) (N : ℕ) (t x : ℝ) :
    HasDerivAt (fun s ↦ fTruncT f_t S N s x) (fTruncTT f_t f_tt S N t x) t := by
  have hu : HasDerivAt (fun s ↦ f_t (S.cut N s) (S.cut N x))
      (f_tt (S.cut N t) (S.cut N x) * S.cutD1 N t) t :=
    (hf_tt (S.cut N t) (S.cut N x)).comp t (S.cut_hasDerivAt N t)
  have hv : HasDerivAt (fun s ↦ S.cutD1 N s) (S.cutD2 N t) t := S.cutD1_hasDerivAt N t
  rw [show fTruncTT f_t f_tt S N t x
      = f_tt (S.cut N t) (S.cut N x) * S.cutD1 N t * S.cutD1 N t
        + f_t (S.cut N t) (S.cut N x) * S.cutD2 N t from by unfold fTruncTT; ring]
  exact hu.mul hv

/-- `∂_x fTruncT = fTruncTX` (product rule, `x`-derivative; `φₙ'(t)` is constant in `x`). -/
lemma fTrunc_hasDerivAt_tx (hf_tx : ∀ t x, HasDerivAt (fun u ↦ f_t t u) (f_tx t x) x)
    (S : SmoothTrunc) (N : ℕ) (t x : ℝ) :
    HasDerivAt (fun u ↦ fTruncT f_t S N t u) (fTruncTX f_tx S N t x) x := by
  have h := ((hf_tx (S.cut N t) (S.cut N x)).comp x (S.cut_hasDerivAt N x)).mul_const (S.cutD1 N t)
  rw [show fTruncTX f_tx S N t x
      = f_tx (S.cut N t) (S.cut N x) * S.cutD1 N x * S.cutD1 N t from by unfold fTruncTX; ring]
  exact h

/-- `∂_x fTruncX = fTruncXX` (product rule, `x`-derivative). -/
lemma fTrunc_hasDerivAt_xx (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
    (S : SmoothTrunc) (N : ℕ) (t x : ℝ) :
    HasDerivAt (fun u ↦ fTruncX f_x S N t u) (fTruncXX f_x f_xx S N t x) x := by
  have hu : HasDerivAt (fun u ↦ f_x (S.cut N t) (S.cut N u))
      (f_xx (S.cut N t) (S.cut N x) * S.cutD1 N x) x :=
    (hf_xx (S.cut N t) (S.cut N x)).comp x (S.cut_hasDerivAt N x)
  have hv : HasDerivAt (fun u ↦ S.cutD1 N u) (S.cutD2 N x) x := S.cutD1_hasDerivAt N x
  rw [show fTruncXX f_x f_xx S N t x
      = f_xx (S.cut N t) (S.cut N x) * S.cutD1 N x * S.cutD1 N x
        + f_x (S.cut N t) (S.cut N x) * S.cutD2 N x from by unfold fTruncXX; ring]
  exact hu.mul hv

/-- `∂_x fTruncXX = fTruncXXX` (sum + product + chain rules). -/
lemma fTrunc_hasDerivAt_xxx (hf_xx : ∀ t x, HasDerivAt (fun u ↦ f_x t u) (f_xx t x) x)
    (hf_xxx : ∀ t x, HasDerivAt (fun u ↦ f_xx t u) (f_xxx t x) x)
    (S : SmoothTrunc) (N : ℕ) (t x : ℝ) :
    HasDerivAt (fun u ↦ fTruncXX f_x f_xx S N t u) (fTruncXXX f_x f_xx f_xxx S N t x) x := by
  -- term 1 : f_xx(·,φₙ ·)·(φₙ' ·)²
  have h_fxx : HasDerivAt (fun u ↦ f_xx (S.cut N t) (S.cut N u))
      (f_xxx (S.cut N t) (S.cut N x) * S.cutD1 N x) x :=
    (hf_xxx (S.cut N t) (S.cut N x)).comp x (S.cut_hasDerivAt N x)
  have h_cD1 : HasDerivAt (fun u ↦ S.cutD1 N u) (S.cutD2 N x) x := S.cutD1_hasDerivAt N x
  have h_cD1sq : HasDerivAt (fun u ↦ S.cutD1 N u * S.cutD1 N u)
      (S.cutD2 N x * S.cutD1 N x + S.cutD1 N x * S.cutD2 N x) x := h_cD1.mul h_cD1
  have hterm1 := h_fxx.mul h_cD1sq
  -- term 2 : f_x(·,φₙ ·)·(φₙ'' ·)
  have h_fx : HasDerivAt (fun u ↦ f_x (S.cut N t) (S.cut N u))
      (f_xx (S.cut N t) (S.cut N x) * S.cutD1 N x) x :=
    (hf_xx (S.cut N t) (S.cut N x)).comp x (S.cut_hasDerivAt N x)
  have h_cD2 : HasDerivAt (fun u ↦ S.cutD2 N u) (S.cutD3 N x) x := S.cutD2_hasDerivAt N x
  have hterm2 := h_fx.mul h_cD2
  rw [show fTruncXXX f_x f_xx f_xxx S N t x
      = f_xxx (S.cut N t) (S.cut N x) * S.cutD1 N x * (S.cutD1 N x * S.cutD1 N x)
          + f_xx (S.cut N t) (S.cut N x)
            * (S.cutD2 N x * S.cutD1 N x + S.cutD1 N x * S.cutD2 N x)
        + (f_xx (S.cut N t) (S.cut N x) * S.cutD1 N x * S.cutD2 N x
          + f_x (S.cut N t) (S.cut N x) * S.cutD3 N x) from by unfold fTruncXXX; ring]
  exact hterm1.add hterm2

/-! ### Constant bounds on the truncated partials -/

/-- `|a·b| ≤ A·B` from `|a| ≤ A` and `|b| ≤ B`. -/
private lemma abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)

/-- A jointly-continuous `g` is bounded after both arguments pass through the cutoff `φₙ` (which
maps into the compact square `[−M₀(N+1), M₀(N+1)]²`). -/
lemma exists_bound_cut (S : SmoothTrunc) (N : ℕ) {g : ℝ → ℝ → ℝ}
    (hg : Continuous fun p : ℝ × ℝ ↦ g p.1 p.2) :
    ∃ C : ℝ, ∀ t x, |g (S.cut N t) (S.cut N x)| ≤ C := by
  set r : ℝ := S.M₀ * ((N : ℝ) + 1) with hr
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := -r) (b := r)).prod
    (isCompact_Icc (a := -r) (b := r))).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun t x ↦ ?_⟩
  have hmem : ((S.cut N t, S.cut N x) : ℝ × ℝ) ∈ Set.Icc (-r) r ×ˢ Set.Icc (-r) r :=
    ⟨by rw [Set.mem_Icc, ← abs_le]; exact S.cut_bdd N t,
     by rw [Set.mem_Icc, ← abs_le]; exact S.cut_bdd N x⟩
  have := hC _ hmem
  rwa [Real.norm_eq_abs] at this

lemma fTruncT_bdd (S : SmoothTrunc) (N : ℕ)
    (hcont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2) :
    ∃ C : ℝ, ∀ t x, |fTruncT f_t S N t x| ≤ C := by
  obtain ⟨B, hB⟩ := exists_bound_cut S N hcont
  exact ⟨B * S.M₁, fun t x ↦ abs_mul_le_of (hB t x) (S.cutD1_bdd N t)⟩

lemma fTruncX_bdd (S : SmoothTrunc) (N : ℕ)
    (hcont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2) :
    ∃ C : ℝ, ∀ t x, |fTruncX f_x S N t x| ≤ C := by
  obtain ⟨B, hB⟩ := exists_bound_cut S N hcont
  exact ⟨B * S.M₁, fun t x ↦ abs_mul_le_of (hB t x) (S.cutD1_bdd N x)⟩

lemma fTruncTX_bdd (S : SmoothTrunc) (N : ℕ)
    (hcont : Continuous fun p : ℝ × ℝ ↦ f_tx p.1 p.2) :
    ∃ C : ℝ, ∀ t x, |fTruncTX f_tx S N t x| ≤ C := by
  obtain ⟨B, hB⟩ := exists_bound_cut S N hcont
  exact ⟨B * S.M₁ * S.M₁,
    fun t x ↦ abs_mul_le_of (abs_mul_le_of (hB t x) (S.cutD1_bdd N x)) (S.cutD1_bdd N t)⟩

lemma fTruncTT_bdd (S : SmoothTrunc) (N : ℕ)
    (hf_t_cont : Continuous fun p : ℝ × ℝ ↦ f_t p.1 p.2)
    (hf_tt_cont : Continuous fun p : ℝ × ℝ ↦ f_tt p.1 p.2) :
    ∃ C : ℝ, ∀ t x, |fTruncTT f_t f_tt S N t x| ≤ C := by
  obtain ⟨Bt, hBt⟩ := exists_bound_cut S N hf_t_cont
  obtain ⟨Btt, hBtt⟩ := exists_bound_cut S N hf_tt_cont
  refine ⟨Btt * (S.M₁ * S.M₁) + Bt * S.M₂, fun t x ↦ ?_⟩
  unfold fTruncTT
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_mul_le_of (hBtt t x) (abs_mul_le_of (S.cutD1_bdd N t) (S.cutD1_bdd N t))
  · exact abs_mul_le_of (hBt t x) (S.cutD2_bdd N t)

lemma fTruncXX_bdd (S : SmoothTrunc) (N : ℕ)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2) :
    ∃ C : ℝ, ∀ t x, |fTruncXX f_x f_xx S N t x| ≤ C := by
  obtain ⟨Bx, hBx⟩ := exists_bound_cut S N hf_x_cont
  obtain ⟨Bxx, hBxx⟩ := exists_bound_cut S N hf_xx_cont
  refine ⟨Bxx * (S.M₁ * S.M₁) + Bx * S.M₂, fun t x ↦ ?_⟩
  unfold fTruncXX
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_mul_le_of (hBxx t x) (abs_mul_le_of (S.cutD1_bdd N x) (S.cutD1_bdd N x))
  · exact abs_mul_le_of (hBx t x) (S.cutD2_bdd N x)

lemma fTruncXXX_bdd (S : SmoothTrunc) (N : ℕ)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2)
    (hf_xxx_cont : Continuous fun p : ℝ × ℝ ↦ f_xxx p.1 p.2) :
    ∃ C : ℝ, ∀ t x, |fTruncXXX f_x f_xx f_xxx S N t x| ≤ C := by
  obtain ⟨Bx, hBx⟩ := exists_bound_cut S N hf_x_cont
  obtain ⟨Bxx, hBxx⟩ := exists_bound_cut S N hf_xx_cont
  obtain ⟨Bxxx, hBxxx⟩ := exists_bound_cut S N hf_xxx_cont
  refine ⟨Bxxx * (S.M₁ * S.M₁ * S.M₁) + 3 * Bxx * S.M₁ * S.M₂ + Bx * S.M₃, fun t x ↦ ?_⟩
  unfold fTruncXXX
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact abs_mul_le_of (hBxxx t x)
      (abs_mul_le_of (abs_mul_le_of (S.cutD1_bdd N x) (S.cutD1_bdd N x)) (S.cutD1_bdd N x))
  · refine abs_mul_le_of (abs_mul_le_of ?_ (S.cutD1_bdd N x)) (S.cutD2_bdd N x)
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    exact mul_le_mul_of_nonneg_left (hBxx t x) (by norm_num)
  · exact abs_mul_le_of (hBx t x) (S.cutD3_bdd N x)

/-! ### Joint continuity of the two partials `ito_formula_td_process` requires -/

/-- `p ↦ (φₙ p.1, φₙ p.2)` is continuous. -/
private lemma continuous_cut_pair (S : SmoothTrunc) (N : ℕ) :
    Continuous fun p : ℝ × ℝ ↦ ((S.cut N p.1, S.cut N p.2) : ℝ × ℝ) :=
  ((S.continuous_cut N).comp continuous_fst).prodMk ((S.continuous_cut N).comp continuous_snd)

lemma fTruncX_continuous (S : SmoothTrunc) (N : ℕ)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2) :
    Continuous fun p : ℝ × ℝ ↦ fTruncX f_x S N p.1 p.2 := by
  simp only [fTruncX]
  exact (hf_x_cont.comp (continuous_cut_pair S N)).mul ((S.continuous_cutD1 N).comp continuous_snd)

lemma fTruncXX_continuous (S : SmoothTrunc) (N : ℕ)
    (hf_x_cont : Continuous fun p : ℝ × ℝ ↦ f_x p.1 p.2)
    (hf_xx_cont : Continuous fun p : ℝ × ℝ ↦ f_xx p.1 p.2) :
    Continuous fun p : ℝ × ℝ ↦ fTruncXX f_x f_xx S N p.1 p.2 := by
  simp only [fTruncXX]
  refine ((hf_xx_cont.comp (continuous_cut_pair S N)).mul
    (((S.continuous_cutD1 N).comp continuous_snd).mul
      ((S.continuous_cutD1 N).comp continuous_snd))).add ?_
  exact (hf_x_cont.comp (continuous_cut_pair S N)).mul ((S.continuous_cutD2 N).comp continuous_snd)

/-! ### Cut inactivity — where `|z| ≤ N` the truncation is the identity -/

/-- Where `|z| ≤ N` the cutoff is inert: `φₙ z = z`, `φₙ' z = 1`, `φₙ'' z = 0` (the plateau
`[−(N+1), N+1] ⊋ [−N, N]`). -/
lemma cut_inactive (S : SmoothTrunc) {N : ℕ} {z : ℝ} (hz : |z| ≤ (N : ℝ)) :
    S.cut N z = z ∧ S.cutD1 N z = 1 ∧ S.cutD2 N z = 0 :=
  ⟨S.cut_eq_id_of_abs_le (le_trans hz (by linarith)),
   S.cutD1_eq_one_of_abs_lt (lt_of_le_of_lt hz (by linarith)),
   S.cutD2_eq_zero_of_abs_lt (lt_of_le_of_lt hz (by linarith))⟩

/-- On the inert region `fTrunc N = f`. -/
lemma fTrunc_eq_of (S : SmoothTrunc) {N : ℕ} {s y : ℝ} (hs : |s| ≤ (N : ℝ)) (hy : |y| ≤ (N : ℝ)) :
    fTrunc f S N s y = f s y := by
  unfold fTrunc; rw [(cut_inactive S hs).1, (cut_inactive S hy).1]

/-- On the inert region the truncated drift is the true drift. -/
lemma truncDrift_eq_of (S : SmoothTrunc) {N : ℕ} {s y : ℝ}
    (hs : |s| ≤ (N : ℝ)) (hy : |y| ≤ (N : ℝ)) :
    fTruncT f_t S N s y + (1 / 2) * fTruncXX f_x f_xx S N s y
      = f_t s y + (1 / 2) * f_xx s y := by
  obtain ⟨hcs, hc1s, _⟩ := cut_inactive S hs
  obtain ⟨hcy, hc1y, hc2y⟩ := cut_inactive S hy
  unfold fTruncT fTruncXX
  rw [hcs, hcy, hc1s, hc1y, hc2y]; ring

end SummitC

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The path stays confined up to the exit time.** On `{s ≤ τ_N}` with `0 < s`, `|B_s| ≤ N`:
for `u < s ≤ τ_N` the exit has not happened (`|B_u| < N`), and left-continuity carries the bound
to the boundary value at `s`. -/
lemma abs_le_N_of_le_exitTime (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
    {N : ℕ} {s : ℝ≥0} {ω : Ω} (hs0 : 0 < s)
    (h : (s : WithTop ℝ≥0) ≤ exitTime B N ω) : |B s ω| ≤ (N : ℝ) := by
  have hbelow : ∀ u : ℝ≥0, u < s → |B u ω| < (N : ℝ) := by
    intro u hu
    by_contra hN
    rw [not_lt] at hN
    have hle : exitTime B N ω ≤ (u : WithTop ℝ≥0) :=
      (exitTime_le_iff hBcont N u ω).mpr ⟨u, ⟨zero_le, le_refl u⟩, hN⟩
    exact absurd hle (not_le.mpr (lt_of_lt_of_le (by exact_mod_cast hu) h))
  have htend : Tendsto (fun u : ℝ≥0 ↦ |B u ω|) (𝓝[<] s) (𝓝 (|B s ω|)) :=
    (continuous_abs.comp (hBcont ω)).continuousWithinAt
  haveI : (𝓝[<] s).NeBot := nhdsWithin_Iio_neBot' ⟨0, hs0⟩ le_rfl
  exact le_of_tendsto htend
    (eventually_nhdsWithin_of_forall fun u hu ↦ le_of_lt (hbelow u hu))

/-- The exit time capped at the level: `σ_N = min(τ_N, N)`. Capping the **time** keeps `t ≤ N` on
`{t ≤ σ_N}`, where the truncation's time cut is inert; still a genuine localizing sequence (the
exit times localize, and `min` with `N ↑ ⊤` preserves all three properties). -/
noncomputable def sigmaSeq (B : ℝ≥0 → Ω → ℝ) (N : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  min (exitTime B N ω) ((N : ℝ≥0) : WithTop ℝ≥0)

lemma isLocalizingSequence_sigma [IsProbabilityMeasure μ] (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω) :
    IsLocalizingSequence (augFiltration (μ := μ) hBmeas) (fun N ↦ sigmaSeq B N) μ where
  isStoppingTime := fun N ↦
    ((isLocalizingSequence_exitTime hBmeas hBcont).isStoppingTime N).min
      (isStoppingTime_const' _ _)
  tendsto_top := Filter.Eventually.of_forall fun ω ↦ by
    have htop := exitTime_tendsto_top hBcont ω
    rw [WithTop.tendsto_nhds_top_iff] at htop ⊢
    intro c
    have h2 : ∀ᶠ N : ℕ in atTop, (c : WithTop ℝ≥0) < ((N : ℝ≥0) : WithTop ℝ≥0) := by
      filter_upwards [eventually_gt_atTop ⌈c⌉₊] with N hN
      have hcN : (c : ℝ≥0) < (N : ℝ≥0) := lt_of_le_of_lt (Nat.le_ceil c) (by exact_mod_cast hN)
      exact_mod_cast hcN
    filter_upwards [htop c, h2] with N hN1 hN2
    exact lt_min hN1 hN2
  mono := Filter.Eventually.of_forall fun ω _ _ hNM ↦
    min_le_min (exitTime_monotone hBcont ω hNM) (by exact_mod_cast hNM)

open SummitC

variable {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}

/-- **The unrestricted-`C³` Itô formula in explicit local-martingale form (Summit C).** For a
general `C³` `f` (six partials with `HasDerivAt` witnesses, all jointly continuous — **no** growth
or boundedness hypothesis), the compensated process

  `M_t = f(t, B_t) − f(0, B_0) − ∫₀ᵗ (f_t + ½f_xx)(s, B_s) ds`

is everywhere-continuous, satisfies the Itô identity by construction, and is a **continuous local
martingale** in explicit form: there is a localizing sequence `σ_N = min(τ_N, N) ↑ ⊤` (`τ_N` the
exit times) and, for each `N`, a continuous **true** martingale `Mₙ` on the null-augmented Brownian
filtration with `M = Mₙ` on the stochastic interval `{t ≤ σ_N}`.

The localization is genuine: `Mₙ` is the continuous global-martingale modification of the Itô
integral of the time-and-space–truncated `fTrunc N = f(φₙ·, φₙ·)`, whose globally-bounded
derivatives let `ito_formula_td_process` apply; on `{t ≤ σ_N}` the cuts are inert, so the truncated
formula collapses to the true one and `Mₙ` agrees with `M`. As `N → ∞` the exit times escape, so
`M` is locally a martingale on all of `[0, ∞)`. -/
theorem ito_formula_unrestricted_local [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ B s ω)
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
      (∀ t : ℝ≥0, (fun ω ↦ f (t : ℝ) (B t ω) - f 0 (B 0 ω)) =ᵐ[μ]
        (fun ω ↦ M t ω + ∫ s in Set.Ioc 0 t,
          (f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω)) ∂ItoIntegralL2.timeMeasure)) ∧
      ∃ σ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence (augFiltration (μ := μ) hBmeas) σ μ ∧
        ∀ N : ℕ, ∃ Mₙ : ℝ≥0 → Ω → ℝ,
          Martingale Mₙ (augFiltration (μ := μ) hBmeas) μ ∧
          (∀ ω, Continuous fun t ↦ Mₙ t ω) ∧
          ∀ t : ℝ≥0, ∀ᵐ ω ∂μ, (t : WithTop ℝ≥0) ≤ σ N ω → M t ω = Mₙ t ω := by
  classical
  obtain ⟨S⟩ := smoothTrunc_exists
  set M : ℝ≥0 → Ω → ℝ := fun t ω ↦
    f (t : ℝ) (B t ω) - f 0 (B 0 ω)
      - ∫ s in Set.Ioc 0 t, (f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω))
        ∂ItoIntegralL2.timeMeasure with hM
  -- continuity of `M` (the drift primitive is continuous; `f∘(↑·,B)` is continuous)
  have hMcont : ∀ ω, Continuous fun t ↦ M t ω := by
    intro ω
    simp only [hM]
    exact ((hf_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))).sub continuous_const).sub
      (continuous_timeMeasure_primitive
        ((hf_t_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))).add
          (continuous_const.mul (hf_xx_cont.comp (NNReal.continuous_coe.prodMk (hBcont ω))))))
  refine ⟨M, hMcont, fun t ↦ Filter.Eventually.of_forall fun ω ↦ by simp only [hM]; ring,
    fun N ↦ sigmaSeq B N, isLocalizingSequence_sigma hBmeas hBcont, fun N ↦ ?_⟩
  -- the truncated process formula at horizon `N`
  obtain ⟨Ct, hCt⟩ := fTruncT_bdd S N hf_t_cont
  obtain ⟨C1, hC1⟩ := fTruncX_bdd S N hf_x_cont
  obtain ⟨C2, hC2⟩ := fTruncXX_bdd S N hf_x_cont hf_xx_cont
  obtain ⟨Ctt, hCtt⟩ := fTruncTT_bdd S N hf_t_cont hf_tt_cont
  obtain ⟨Ctx, hCtx⟩ := fTruncTX_bdd S N hf_tx_cont
  obtain ⟨Cxxx, hCxxx⟩ := fTruncXXX_bdd S N hf_x_cont hf_xx_cont hf_xxx_cont
  obtain ⟨F, hform, -, -⟩ := ito_formula_td_process hB hBmeas hBcont (N : ℝ≥0)
    (f := fTrunc f S N) (f_t := fTruncT f_t S N) (f_x := fTruncX f_x S N)
    (f_xx := fTruncXX f_x f_xx S N) (f_tt := fTruncTT f_t f_tt S N)
    (f_tx := fTruncTX f_tx S N) (f_xxx := fTruncXXX f_x f_xx f_xxx S N)
    (fTrunc_hasDerivAt_t hf_t S N) (fTrunc_hasDerivAt_tt hf_tt S N)
    (fTrunc_hasDerivAt_tx hf_tx S N) (fTrunc_hasDerivAt_x hf_x S N)
    (fTrunc_hasDerivAt_xx hf_xx S N) (fTrunc_hasDerivAt_xxx hf_xx hf_xxx S N)
    (fTruncX_continuous S N hf_x_cont) (fTruncXX_continuous S N hf_x_cont hf_xx_cont)
    hCt hC1 hC2 hCtt hCtx hCxxx
  -- the continuous GLOBAL martingale modification of the truncated Itô integral
  obtain ⟨X, hmodX, hcontX, hmartX⟩ :=
    ItoLocalMartingaleInfinite.exists_continuous_martingale_modification_infinite hB hBmeas hBcont F
  refine ⟨X, hmartX, hcontX, fun t ↦ ?_⟩
  -- agreement `M t = X t` on `{t ≤ σ_N}`
  have hN0 : |(0 : ℝ)| ≤ (N : ℝ) := by rw [abs_zero]; exact Nat.cast_nonneg N
  rcases eq_zero_or_pos t with ht0 | ht0
  · -- `t = 0`: both sides are `0` (`hform 0` gives `itoProcessL2Inf 0 F =ᵐ 0`)
    subst ht0
    filter_upwards [hform 0 zero_le, hmodX 0] with ω hf hmod _
    simp only [hM, hmod, NNReal.coe_zero, Set.Ioc_self, MeasureTheory.setIntegral_empty,
      add_zero, sub_self] at hf ⊢
    linarith [hf]
  · by_cases htN : t ≤ (N : ℝ≥0)
    · filter_upwards [hform t htN, hmodX t, eval_zero_ae hB hBmeas] with ω hf hmod hB0 hev
      have hexit : (t : WithTop ℝ≥0) ≤ exitTime B N ω := le_trans hev (min_le_left _ _)
      have hBt : |B t ω| ≤ (N : ℝ) := abs_le_N_of_le_exitTime hBcont ht0 hexit
      have htNr : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast htN
      have hb1 : fTrunc f S N (t : ℝ) (B t ω) = f (t : ℝ) (B t ω) :=
        fTrunc_eq_of S (by rw [abs_of_nonneg t.coe_nonneg]; exact htNr) hBt
      have hb0 : fTrunc f S N 0 (B 0 ω) = f 0 (B 0 ω) := by
        rw [hB0]; exact fTrunc_eq_of S hN0 hN0
      have hdr : (∫ s in Set.Ioc 0 t, (fTruncT f_t S N (s : ℝ) (B s ω)
            + (1 / 2) * fTruncXX f_x f_xx S N (s : ℝ) (B s ω)) ∂ItoIntegralL2.timeMeasure)
          = ∫ s in Set.Ioc 0 t, (f_t (s : ℝ) (B s ω) + (1 / 2) * f_xx (s : ℝ) (B s ω))
              ∂ItoIntegralL2.timeMeasure := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun s hs ↦ ?_)
        have hsexit : (s : WithTop ℝ≥0) ≤ exitTime B N ω :=
          le_trans (by exact_mod_cast hs.2) hexit
        have hBs : |B s ω| ≤ (N : ℝ) := abs_le_N_of_le_exitTime hBcont hs.1 hsexit
        have hsN : (s : ℝ) ≤ N := le_trans (by exact_mod_cast hs.2) htNr
        exact truncDrift_eq_of S (by rw [abs_of_nonneg s.coe_nonneg]; exact hsN) hBs
      rw [hb1, hb0, hdr] at hf
      simp only [hM, hmod]
      linarith [hf]
    · -- `t > N`: vacuous, since `t ≤ σ_N ≤ N`
      refine Filter.Eventually.of_forall fun ω hev ↦ ?_
      exact absurd (by exact_mod_cast le_trans hev (min_le_right _ _) : t ≤ (N : ℝ≥0)) htN

/-- **The indistinguishability upgrade.** Two continuous processes that agree a.s. at every
deterministic time below a stopping time `σ` agree, a.s., on the whole stochastic interval
`[0, σ]` — the per-deterministic-`t` modification lifted to all-`t` by continuity on the dense
countable set, then to the closed interval by left-continuity at the boundary.

This is the staging lemma for the `IsLocalMartingale`-typeclass wrapper of Summit C: it upgrades the
per-`t` agreement that `ito_formula_unrestricted_local` returns to the all-time agreement a
`Martingale.stoppedProcess_indicator` argument needs. It is consumed by `ito_formula_unrestricted`
in `ItoFormulaUnrestrictedLocMart.lean`. -/
lemma indistinguishable_on_stochInterval {M' X' : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0}
    (hM'cont : ∀ ω, Continuous fun t ↦ M' t ω) (hX'cont : ∀ ω, Continuous fun t ↦ X' t ω)
    (hagree : ∀ t : ℝ≥0, ∀ᵐ ω ∂μ, (t : WithTop ℝ≥0) ≤ σ ω → M' t ω = X' t ω) :
    ∀ᵐ ω ∂μ, ⊥ < σ ω → ∀ u : ℝ≥0, (u : WithTop ℝ≥0) ≤ σ ω → M' u ω = X' u ω := by
  obtain ⟨D, D_count, D_dense⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hco : ∀ᵐ ω ∂μ, ∀ d ∈ D, (d : WithTop ℝ≥0) ≤ σ ω → M' d ω = X' d ω :=
    (ae_ball_iff D_count).mpr fun d _ ↦ hagree d
  filter_upwards [hco] with ω hω hpos u hu
  have hUopen : IsOpen {t : ℝ≥0 | (t : WithTop ℝ≥0) < σ ω} :=
    isOpen_Iio.preimage WithTop.continuous_coe
  have hEqU : Set.EqOn (fun t ↦ M' t ω) (fun t ↦ X' t ω) {t | (t : WithTop ℝ≥0) < σ ω} :=
    Set.EqOn.of_subset_closure (fun d hd ↦ hω d hd.1 (le_of_lt hd.2))
      (hM'cont ω).continuousOn (hX'cont ω).continuousOn Set.inter_subset_right
      (subset_closure_dense_inter D_dense hUopen)
  have humem : u ∈ closure {t : ℝ≥0 | (t : WithTop ℝ≥0) < σ ω} := by
    rcases lt_or_eq_of_le hu with hlt | heq
    · exact subset_closure hlt
    · have hu0 : (0 : ℝ≥0) < u := by
        have h : (0 : WithTop ℝ≥0) < (u : WithTop ℝ≥0) := by
          rw [← heq] at hpos; simpa using hpos
        rwa [← WithTop.coe_zero, WithTop.coe_lt_coe] at h
      have hIio : Set.Iio u ⊆ {t : ℝ≥0 | (t : WithTop ℝ≥0) < σ ω} := fun s hs ↦ by
        rw [Set.mem_setOf_eq, ← heq, WithTop.coe_lt_coe]; exact hs
      exact closure_mono hIio ((closure_Iio' (a := u) ⟨0, hu0⟩).ge Set.self_mem_Iic)
  exact hEqU.closure (hM'cont ω) (hX'cont ω) humem

end MathFin
