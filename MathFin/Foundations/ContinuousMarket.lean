/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.NoArbitrageCore

/-!
# Continuous-time market vocabulary: `IsEMM`, simple strategies, no-arbitrage

A **model-agnostic** frame for the continuous-time first fundamental theorem of asset
pricing (FTAP), parametric over a finite-dimensional real inner-product-space-valued
discounted price process `S : ℝ≥0 → Ω → F`. The Black–Scholes model (`ContinuousFTAP.lean`)
instantiates it at `F = ℝ`; a multi-asset model would instantiate at `F = Fin n → ℝ`.

* `IsEMM S Q` — `Q` is an equivalent martingale measure for `S`: `Q ≈ P` (mutual absolute
  continuity) and `S` is a `Q`-martingale w.r.t. the filtration `𝓕`.
* `SimpleStrategy 𝓕 F` — a piecewise-constant, predictable, bounded trading strategy:
  finitely many trading dates `time : Fin (N+1) → ℝ≥0` and `𝓕`-measurable bounded holdings
  `hold : Fin N → Ω → F` between consecutive dates.
* `SimpleStrategy.gains` — the discounted terminal gains of a simple strategy against `S`.
* `NoArbitrageSimple S` — no simple strategy's gains are `P`-a.s. nonnegative and strictly
  positive on a `P`-non-null set.

## Scope: meaning-1 (operational) vs. meaning-2 (Delbaen–Schachermayer) FTAP

This file builds **meaning 1**: an EMM for a *given* process, restricted to the honest,
economically transparent class of *simple* (piecewise-constant) strategies. It deliberately
does **not** build meaning 2, the Delbaen–Schachermayer theorem (`NFLVR ⟺ ∃ EMM` for a
general locally-bounded semimartingale, admissible strategies over a continuum of trading
times, and the general stochastic integral `∫ φ dS`). Absent by design:

* general **admissible** strategies (not just piecewise-constant) and the general stochastic
  integral `∫ φ dS` against a semimartingale;
* **NFLVR** (no free lunch with vanishing risk) and its distinction from plain no-arbitrage;
* the **converse** direction `NoArbitrageSimple S → ∃ Q, IsEMM S Q`, and closedness of the
  set of claims super-replicable from zero wealth (the Kreps–Yan / Hahn–Banach core DS needs).

`IsEMM` here is stated *on a process* `S`, exactly the object Delbaen–Schachermayer's theorem
would produce — so this frame is a strict sub-object of the DS one, and extending it to
meaning 2 is additive (new strategy class + new theorem), not a rewrite.
-/

@[expose] public section

namespace MathFin.ContinuousMarket

open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `Q` is an **equivalent martingale measure (EMM)** for the discounted price process `S`:
`Q` is a probability measure mutually absolutely continuous with `P` (`Q ≈ P`), and `S` is a
`Q`-martingale w.r.t. the filtration `𝓕`. -/
structure IsEMM (S : ℝ≥0 → Ω → F) (Q : Measure Ω) : Prop where
  isProb : IsProbabilityMeasure Q
  ac : Q ≪ P
  ac' : P ≪ Q
  martingale : Martingale S 𝓕 Q

/-- A **simple strategy**: finitely many trading dates `time 0 ≤ time 1 ≤ ⋯ ≤ time N`, with
piecewise-constant, `𝓕`-predictable, bounded holdings `hold i` held over `(time i, time i+1]`.
Does not depend on any measure — it is a purely path-space/filtration object. -/
structure SimpleStrategy (𝓕 : Filtration ℝ≥0 mΩ) (F : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  N : ℕ
  time : Fin (N + 1) → ℝ≥0
  mono : Monotone time
  hold : Fin N → Ω → F
  meas : ∀ i : Fin N, StronglyMeasurable[𝓕 (time i.castSucc)] (hold i)
  bdd : ∃ K : ℝ, ∀ (i : Fin N) ω, ‖hold i ω‖ ≤ K

/-- The **discounted terminal gains** of a simple strategy `ψ` against the price process `S`:
`∑ᵢ ⟪hold i, S(time i+1) − S(time i)⟫`. -/
noncomputable def SimpleStrategy.gains (ψ : SimpleStrategy 𝓕 F)
    (S : ℝ≥0 → Ω → F) (ω : Ω) : ℝ :=
  ∑ i : Fin ψ.N, ⟪ψ.hold i ω, S (ψ.time i.succ) ω - S (ψ.time i.castSucc) ω⟫_ℝ

/-- **No simple-strategy arbitrage**: no simple strategy's gains against `S` are `P`-a.s.
nonnegative and strictly positive on a `P`-non-null set. -/
def NoArbitrageSimple (S : ℝ≥0 → Ω → F) : Prop :=
  ∀ ψ : SimpleStrategy 𝓕 F, (0 ≤ᵐ[P] fun ω ↦ ψ.gains S ω) →
    P {ω | 0 < ψ.gains S ω} = 0

/-- The discrete `ℕ`-filtration `n ↦ 𝓕 (t n)` obtained by **sampling** a continuous-time
filtration `𝓕` along a monotone schedule `t : ℕ → ℝ≥0`. -/
def sampledFiltration (𝓕 : Filtration ℝ≥0 mΩ) {t : ℕ → ℝ≥0} (ht : Monotone t) :
    Filtration ℕ mΩ where
  seq n := 𝓕 (t n)
  mono' _ _ hij := 𝓕.mono (ht hij)
  le' n := 𝓕.le (t n)

omit [FiniteDimensional ℝ F] in
/-- **A `Q`-martingale sampled along a monotone schedule is a discrete `Q`-martingale.**
Sampling `S` at the increasing times `t 0 ≤ t 1 ≤ ⋯` gives a martingale w.r.t. the sampled
filtration `sampledFiltration 𝓕 ht`: adaptedness and the tower property both restrict along
`t`. A general, standalone structural lemma (the discrete-time trace of a continuous-time
martingale). The forward theorem `isEMM_noArbitrageSimple` below takes a direct term-by-term
route and does not use this; it is kept as a reusable primitive (benchmarked as
`gir-martingale-reindex`) for sampled-model instances and the eventual meaning-2 development. -/
theorem martingale_comp_monotone {Q : Measure Ω} {S : ℝ≥0 → Ω → F}
    (hS : Martingale S 𝓕 Q) {t : ℕ → ℝ≥0} (ht : Monotone t) :
    Martingale (fun n ↦ S (t n)) (sampledFiltration 𝓕 ht) Q :=
  ⟨fun n ↦ hS.1 (t n), fun i j hij ↦ hS.2 (t i) (t j) (ht hij)⟩

/-- **A predictable-weighted increment `⟪φ, S t − S s⟫` is `Q`-integrable** when `φ` is bounded
and `S` is a `Q`-martingale (so `S t`, `S s` are integrable): Cauchy–Schwarz bounds the inner
product by `K · ‖S t − S s‖`, which is integrable. -/
private theorem increment_integrable {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S : ℝ≥0 → Ω → F} (hS : Martingale S 𝓕 Q) {φ : Ω → F} {s t : ℝ≥0}
    (hφ : StronglyMeasurable[𝓕 s] φ) {K : ℝ} (hφb : ∀ ω, ‖φ ω‖ ≤ K) :
    Integrable (fun ω ↦ ⟪φ ω, S t ω - S s ω⟫_ℝ) Q := by
  have hΔ : Integrable (fun ω ↦ S t ω - S s ω) Q := (hS.integrable t).sub (hS.integrable s)
  refine Integrable.mono' (hΔ.norm.const_mul K)
    (((hφ.mono (𝓕.le s)).aestronglyMeasurable).inner hΔ.aestronglyMeasurable) ?_
  filter_upwards with ω
  calc ‖⟪φ ω, S t ω - S s ω⟫_ℝ‖ ≤ ‖φ ω‖ * ‖S t ω - S s ω‖ := norm_inner_le_norm _ _
    _ ≤ K * ‖S t ω - S s ω‖ := mul_le_mul_of_nonneg_right (hφb ω) (norm_nonneg _)

/-- **A predictable-weighted martingale increment has zero `Q`-integral.** For a `Q`-martingale
`S`, a `𝓕 s`-measurable bounded weight `φ`, and `s ≤ t`, the increment gain `⟪φ, S t − S s⟫`
integrates to `0`: pull `φ` out of `Q[· | 𝓕 s]` and use `Q[S t − S s | 𝓕 s] = 0`. -/
private theorem increment_integral_zero {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S : ℝ≥0 → Ω → F} (hS : Martingale S 𝓕 Q) {φ : Ω → F} {s t : ℝ≥0} (hst : s ≤ t)
    (hφ : StronglyMeasurable[𝓕 s] φ) {K : ℝ} (hφb : ∀ ω, ‖φ ω‖ ≤ K) :
    ∫ ω, ⟪φ ω, S t ω - S s ω⟫_ℝ ∂Q = 0 := by
  have hm : 𝓕 s ≤ mΩ := 𝓕.le s
  have hΔ : Integrable (fun ω ↦ S t ω - S s ω) Q := (hS.integrable t).sub (hS.integrable s)
  -- `Q[S t − S s | 𝓕 s] = 0`.
  have hcond0 : Q[fun ω ↦ S t ω - S s ω | 𝓕 s] =ᵐ[Q] 0 := by
    have hsub : Q[fun ω ↦ S t ω - S s ω | 𝓕 s] =ᵐ[Q] Q[S t | 𝓕 s] - Q[S s | 𝓕 s] :=
      condExp_sub (hS.integrable t) (hS.integrable s) _
    have h1 : Q[S t | 𝓕 s] =ᵐ[Q] S s := hS.2 s t hst
    have h2 : Q[S s | 𝓕 s] = S s := condExp_of_stronglyMeasurable hm (hS.1 s) (hS.integrable s)
    filter_upwards [hsub, h1] with ω hω h1ω
    rw [hω, Pi.zero_apply, Pi.sub_apply, h1ω, h2, sub_self]
  -- Pull out `φ` and collapse.
  calc ∫ ω, ⟪φ ω, S t ω - S s ω⟫_ℝ ∂Q
      = ∫ ω, (Q[fun ω ↦ ⟪φ ω, S t ω - S s ω⟫_ℝ | 𝓕 s]) ω ∂Q := (integral_condExp hm).symm
    _ = ∫ ω, ⟪φ ω, (Q[fun ω ↦ S t ω - S s ω | 𝓕 s]) ω⟫_ℝ ∂Q :=
        integral_congr_ae (condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hφ
          (increment_integrable hS hφ hφb) hΔ)
    _ = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hcond0] with ω hω
        rw [hω]; simp

/-- **Forward continuous first FTAP: an equivalent martingale measure precludes simple-strategy
arbitrage.** If `Q` is an EMM for the discounted price `S`, then no simple strategy has gains that
are `P`-a.s. nonnegative and strictly positive on a `P`-non-null set. Each increment integrates to
`0` under `Q` (`increment_integral_zero`), so the whole gain does; transporting the `P`-nonnegativity
to `Q` (via `Q ≈ P`), the zero-mean nonnegative gain vanishes `Q`-a.s.
(`ae_zero_of_nonneg_of_integral_zero`), hence `P`-a.s. -/
theorem isEMM_noArbitrageSimple {S : ℝ≥0 → Ω → F} {Q : Measure Ω}
    (h : IsEMM (P := P) (𝓕 := 𝓕) S Q) : NoArbitrageSimple (P := P) (𝓕 := 𝓕) S := by
  intro ψ hnonneg
  haveI : IsProbabilityMeasure Q := h.isProb
  obtain ⟨K, hK⟩ := ψ.bdd
  have hterm_int : ∀ i : Fin ψ.N, Integrable
      (fun ω ↦ ⟪ψ.hold i ω, S (ψ.time i.succ) ω - S (ψ.time i.castSucc) ω⟫_ℝ) Q :=
    fun i ↦ increment_integrable h.martingale (ψ.meas i) (hK i)
  have hgains_int : Integrable (fun ω ↦ ψ.gains S ω) Q := by
    simp only [SimpleStrategy.gains]
    exact integrable_finsetSum _ fun i _ ↦ hterm_int i
  have hint0 : ∫ ω, ψ.gains S ω ∂Q = 0 := by
    simp only [SimpleStrategy.gains]
    rw [integral_finsetSum _ fun i _ ↦ hterm_int i]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    exact increment_integral_zero h.martingale (ψ.mono (Fin.castSucc_lt_succ (i := i)).le)
      (ψ.meas i) (hK i)
  have hnonneg_Q : 0 ≤ᵐ[Q] fun ω ↦ ψ.gains S ω :=
    Filter.Eventually.filter_mono h.ac.ae_le hnonneg
  exact h.ac' (ae_zero_of_nonneg_of_integral_zero hgains_int hnonneg_Q hint0)

end MathFin.ContinuousMarket
