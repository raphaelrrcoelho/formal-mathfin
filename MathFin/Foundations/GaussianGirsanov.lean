/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.Call
public import MathFin.BlackScholes.Forward

/-!
# Static Girsanov: the risk-neutral measure as a Gaussian change of measure

`BSCallHyp` — the lognormal risk-neutral hypothesis that 14 pricing files
take on faith — posits "the driver `Z` is standard normal under `Q`." This
file **derives** that hypothesis: it constructs the risk-neutral measure `Q`
from the physical measure `P` via an explicit Radon-Nikodym (Esscher)
density, and proves the recentred driver is standard normal under `Q`. The
EMM stops being an axiom.

The deductive chain:

1. `gaussian_esscher_pdf` — completing the square: `exp(c·x − c²/2)·φ₀,₁(x)
   = φ_c,₁(x)`.
2. `gaussianReal_withDensity_esscher` — measure level: tilting `N(0,1)` by
   the Esscher density gives `N(c,1)` (mean-shift by `c`, variance fixed).
3. `map_withDensity_comp` — pushforward commutes with a density factoring
   through the map (so the change of measure can be read at the level of the
   driver's law).
4. `hasLaw_esscher_tilt` — static Girsanov for a random variable: if `W` is
   standard normal under `P`, then under `Q := P.withDensity(exp(c·W−c²/2))`
   the same `W` has law `N(c,1)`.
5. `hasLaw_sub_const` — recentring: `W − c ~ N(0,1)` under `Q`.
6. `BSCallHyp.of_physical` — the capstone: `BSCallHyp` holds for `Q` and the
   recentred driver, with `Q` and the driver both *constructed* from the
   physical data. The economic instantiation is `c = (r − μ)·√T / σ`, i.e.
   the market price of risk `θ = (μ − r)/σ` enters as `c = −θ√T`; then the
   recentred driver `W − c = W + θ√T` is exactly the risk-neutral driver,
   and `bsTerminal` driven by it reprices the *same* asset with drift `μ → r`
   (see `bsTerminal_physical_eq_riskNeutral`).

This is the static (single-Gaussian) Girsanov theorem — the slice tractable
without the path-wise stochastic integral. The path-wise version is gated on
Mathlib's Itô integral (WIP in Degenne's BrownianMotion package).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- **Gaussian Esscher identity** (completing the square): tilting the
standard-normal density by the normalised exponential `exp(c·x − c²/2)`
yields the `N(c, 1)` density. This is the pointwise heart of the static
Girsanov change of measure. -/
theorem gaussian_esscher_pdf (c x : ℝ) :
    Real.exp (c * x - c ^ 2 / 2) * gaussianPDFReal 0 1 x = gaussianPDFReal c 1 x := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [← mul_assoc, mul_comm (Real.exp (c * x - c ^ 2 / 2)) _, mul_assoc,
      ← Real.exp_add]
  congr 2
  ring

/-- **Gaussian Esscher change of measure** (measure level): tilting the
standard normal `N(0,1)` by the Radon-Nikodym density `exp(c·x − c²/2)`
produces exactly `N(c, 1)`. The mean shifts by the tilt parameter `c`; the
variance is unchanged. This is the static (single-Gaussian) Girsanov
theorem. -/
theorem gaussianReal_withDensity_esscher (c : ℝ) :
    (gaussianReal 0 1).withDensity
      (fun x ↦ ENNReal.ofReal (Real.exp (c * x - c ^ 2 / 2))) = gaussianReal c 1 := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero), gaussianReal_of_var_ne_zero c (one_ne_zero)]
  rw [← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  show gaussianPDF 0 1 x * ENNReal.ofReal (Real.exp (c * x - c ^ 2 / 2)) = gaussianPDF c 1 x
  rw [gaussianPDF_def, gaussianPDF_def,
      ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x), mul_comm,
      gaussian_esscher_pdf]

/-- **Pushforward commutes with a density that factors through the map**:
for measurable `W : Ω → ℝ` and `g : ℝ → ℝ≥0∞`, the law of `W` under
`P.withDensity (g ∘ W)` is `(law of W under P).withDensity g`. This is the
plumbing that lets a change of measure defined on `Ω` (via a density in the
driver `W`) be read entirely at the level of `W`'s law. -/
theorem map_withDensity_comp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) {W : Ω → ℝ} (hW : Measurable W) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) :
    (P.withDensity (g ∘ W)).map W = (P.map W).withDensity g := by
  ext s hs
  rw [Measure.map_apply hW hs, withDensity_apply _ (hW hs),
      withDensity_apply _ hs, setLIntegral_map hs hg hW]
  rfl

/-- **Static Girsanov for a random variable**: if the driver `W` is standard
normal under the physical measure `P`, then under the Esscher-tilted measure
`Q := P.withDensity(exp(c·W − c²/2))`, the *same* `W` has law `N(c, 1)`. The
change of measure shifts the driver's mean by the tilt `c` and leaves the
variance fixed — exactly the static (single-Gaussian) Girsanov theorem,
stated at the level of the random variable. -/
theorem hasLaw_esscher_tilt {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : Ω → ℝ} (c : ℝ)
    (hWmeas : Measurable W) (hW : HasLaw W (gaussianReal 0 1) P) :
    HasLaw W (gaussianReal c 1)
      (P.withDensity (fun ω ↦ ENNReal.ofReal (Real.exp (c * W ω - c ^ 2 / 2)))) where
  aemeasurable := hWmeas.aemeasurable
  map_eq := by
    rw [show (fun ω ↦ ENNReal.ofReal (Real.exp (c * W ω - c ^ 2 / 2)))
          = (fun x ↦ ENNReal.ofReal (Real.exp (c * x - c ^ 2 / 2))) ∘ W from rfl,
        map_withDensity_comp P hWmeas (by fun_prop), hW.map_eq,
        gaussianReal_withDensity_esscher]

/-- **Shifting a Gaussian driver**: if `W ~ N(m, 1)` then `W − c ~ N(m − c, 1)`.
Recentering by a constant translates the mean. -/
theorem hasLaw_sub_const {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} {W : Ω → ℝ} (c m : ℝ)
    (hWmeas : Measurable W) (hW : HasLaw W (gaussianReal m 1) Q) :
    HasLaw (fun ω ↦ W ω - c) (gaussianReal (m - c) 1) Q where
  aemeasurable := (hWmeas.sub_const c).aemeasurable
  map_eq := by
    rw [show (fun ω ↦ W ω - c) = (fun y : ℝ ↦ y - c) ∘ W from rfl,
        ← Measure.map_map (show Measurable (fun y : ℝ ↦ y - c) by fun_prop) hWmeas,
        hW.map_eq,
        show (fun y : ℝ ↦ y - c) = (fun y ↦ y + (-c)) from by funext y; ring,
        gaussianReal_map_add_const, sub_eq_add_neg]

/-- **The Esscher-tilted measure is a probability measure.** Its total mass
is the standard-normal MGF evaluated to `1` (the Esscher density is
normalised), read off from the fact that `W` has a genuine law (`N(c,1)`)
under it. -/
theorem esscherTilt_isProbabilityMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : Ω → ℝ} (c : ℝ)
    (hWmeas : Measurable W) (hW : HasLaw W (gaussianReal 0 1) P) :
    IsProbabilityMeasure
      (P.withDensity (fun ω ↦ ENNReal.ofReal (Real.exp (c * W ω - c ^ 2 / 2)))) := by
  constructor
  rw [← Set.preimage_univ (f := W),
      ← Measure.map_apply hWmeas MeasurableSet.univ,
      (hasLaw_esscher_tilt c hWmeas hW).map_eq]
  exact measure_univ

/-- **The risk-neutral measure, derived** (static Girsanov capstone). Given a
standard-normal physical driver `W` under `P`, there **exists** a probability
measure `Q` — explicitly the Esscher tilt `Q = P.withDensity(exp(c·W − c²/2))`
— under which the recentred driver `W − c` satisfies the risk-neutral
hypothesis `BSCallHyp`. The risk-neutral hypothesis is thus a *theorem*: every
BS-family price, Greek, and bound that consumes `BSCallHyp` is founded on a
constructed EMM rather than an assumed one.

Economic instantiation: take `c = (r − μ)·√T / σ = −θ·√T` where `θ = (μ−r)/σ`
is the market price of risk; then `W − c = W + θ√T` is the risk-neutral
driver, and `Q` is the equivalent martingale measure — its martingale
property `E_Q[e^{−rT} S_T] = S_0` follows from the resulting `BSCallHyp` via
`discounted_terminal_eq_S0`. -/
theorem BSCallHyp.exists_of_physical {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {S_0 K r σ T : ℝ} {W : Ω → ℝ} (c : ℝ)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T)
    (hWmeas : Measurable W) (hW : HasLaw W (gaussianReal 0 1) P) :
    ∃ (Q : Measure Ω) (hQ : IsProbabilityMeasure Q),
      Q = P.withDensity (fun ω ↦ ENNReal.ofReal (Real.exp (c * W ω - c ^ 2 / 2))) ∧
      @BSCallHyp _ _ Q hQ S_0 K r σ T (fun ω ↦ W ω - c) := by
  have h_std : HasLaw (fun ω ↦ W ω - c) (gaussianReal 0 1)
      (P.withDensity (fun ω ↦ ENNReal.ofReal (Real.exp (c * W ω - c ^ 2 / 2)))) := by
    have h := hasLaw_sub_const c c hWmeas (hasLaw_esscher_tilt c hWmeas hW)
    rwa [sub_self] at h
  exact ⟨P.withDensity (fun ω ↦ ENNReal.ofReal (Real.exp (c * W ω - c ^ 2 / 2))),
    esscherTilt_isProbabilityMeasure c hWmeas hW, rfl,
    @BSCallHyp.mk _ _ _ (esscherTilt_isProbabilityMeasure c hWmeas hW)
      _ _ _ _ _ _ hS_0 hK hσ hT h_std⟩

/-- **The change of measure reprices the same asset** — the conceptual heart
of risk-neutral valuation. The Girsanov shift `c = (r − μ)·√T / σ` is exactly
the recentring under which the physical terminal `S_0·exp((μ−σ²/2)T + σ√T·W)`
equals the risk-neutral terminal `S_0·exp((r−σ²/2)T + σ√T·(W − c))`. The asset
`S_T` is invariant; only its *drift* changes `μ → r`. This is *why* the
Esscher tilt of `BSCallHyp.exists_of_physical` is the right change of
measure: it is the one that turns the real-world drift into the risk-free
rate while leaving the random variable `S_T` untouched. -/
theorem bsTerminal_physical_eq_riskNeutral
    (S_0 μ r σ T w : ℝ) (hσ : σ ≠ 0) (hT : 0 ≤ T) :
    bsTerminal S_0 μ σ T w
      = bsTerminal S_0 r σ T (w - (r - μ) * Real.sqrt T / σ) := by
  unfold bsTerminal
  have hexp : (μ - σ ^ 2 / 2) * T + σ * Real.sqrt T * w
      = (r - σ ^ 2 / 2) * T + σ * Real.sqrt T * (w - (r - μ) * Real.sqrt T / σ) := by
    have h1 : σ * Real.sqrt T * (w - (r - μ) * Real.sqrt T / σ)
        = σ * Real.sqrt T * w - (r - μ) * (Real.sqrt T * Real.sqrt T) := by
      field_simp
    rw [h1, Real.mul_self_sqrt hT]; ring
  rw [hexp]

/-! ## Wiring Girsanov into the pricing artifacts

The two composites below make `GaussianGirsanov` load-bearing: they drive the
prior pricing results from the *physical* measure through the constructed
EMM, rather than from an assumed `BSCallHyp`. This is the genesis-cascade
spine `physical measure → Girsanov → Q → pricing`. -/

/-- **The constructed measure is an equivalent martingale measure** (derived
from the physical measure). For the Esscher-tilted `Q` of
`BSCallHyp.exists_of_physical`, the discounted terminal asset is a
`Q`-martingale: `E_Q[e^{−rT}·S_T] = S_0`. This is the *defining* property of
an EMM — so the construction yields a genuine risk-neutral measure, not
merely one under which the driver is standard normal. Composes
`exists_of_physical` with `discounted_terminal_eq_S0`. -/
theorem discounted_terminal_eq_S0_of_physical {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {S_0 K r σ T : ℝ} {W : Ω → ℝ} (c : ℝ)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T)
    (hWmeas : Measurable W) (hW : HasLaw W (gaussianReal 0 1) P) :
    ∃ (Q : Measure Ω) (_ : IsProbabilityMeasure Q),
      Q = P.withDensity (fun ω ↦ ENNReal.ofReal (Real.exp (c * W ω - c ^ 2 / 2))) ∧
      ∫ ω, Real.exp (-(r * T)) * bsTerminal S_0 r σ T (W ω - c) ∂Q = S_0 := by
  obtain ⟨Q, hQ, hQeq, hbs⟩ :=
    BSCallHyp.exists_of_physical (S_0 := S_0) (K := K) (r := r) (σ := σ) (T := T)
      c hS_0 hK hσ hT hWmeas hW
  haveI := hQ
  exact ⟨Q, hQ, hQeq, discounted_terminal_eq_S0 hbs⟩

/-- **Black-Scholes call price from the physical measure** (full chain). For
the constructed EMM `Q`, the discounted expected payoff equals the
Black-Scholes closed form. Every other BS-family result composes the same
way; this one stands for the pipeline. Composes `exists_of_physical` with
`bs_call_formula`. -/
theorem bs_call_formula_of_physical {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {S_0 K r σ T : ℝ} {W : Ω → ℝ} (c : ℝ)
    (hS_0 : 0 < S_0) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T)
    (hWmeas : Measurable W) (hW : HasLaw W (gaussianReal 0 1) P) :
    ∃ (Q : Measure Ω) (_ : IsProbabilityMeasure Q),
      Q = P.withDensity (fun ω ↦ ENNReal.ofReal (Real.exp (c * W ω - c ^ 2 / 2))) ∧
      ∫ ω, Real.exp (-r * T) * max (bsTerminal S_0 r σ T (W ω - c) - K) 0 ∂Q
        = S_0 * Phi (bsd1 S_0 K r σ T)
          - K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) := by
  obtain ⟨Q, hQ, hQeq, hbs⟩ :=
    BSCallHyp.exists_of_physical (S_0 := S_0) (K := K) (r := r) (σ := σ) (T := T)
      c hS_0 hK hσ hT hWmeas hW
  haveI := hQ
  exact ⟨Q, hQ, hQeq, bs_call_formula hbs⟩

/-- **The physical-drift asset reprices to `S_0` under the constructed EMM** —
the `μ → r` drift elimination, *wired into the chain* (not merely asserted).
Instantiating the Girsanov shift at the market-price-of-risk value
`c = (r − μ)·√T/σ`, `bsTerminal_physical_eq_riskNeutral` identifies the physical
terminal `bsTerminal S_0 μ σ T W` (drift `μ`) with the risk-neutral one, and
`discounted_terminal_eq_S0_of_physical` supplies the martingale property — so
`E_Q[e^{−rT}·S_T] = S_0` holds for the asset carrying the *physical* drift `μ`.
This composes the previously-standalone drift-invariance identity into the EMM
pipeline, closing the `physical → EMM` step at the level of the physical model. -/
theorem discounted_physical_terminal_eq_S0 {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {S_0 r μ σ T : ℝ} {W : Ω → ℝ}
    (hS_0 : 0 < S_0) (hσ : 0 < σ) (hT : 0 < T)
    (hWmeas : Measurable W) (hW : HasLaw W (gaussianReal 0 1) P) :
    ∃ (Q : Measure Ω) (_ : IsProbabilityMeasure Q),
      ∫ ω, Real.exp (-(r * T)) * bsTerminal S_0 μ σ T (W ω) ∂Q = S_0 := by
  obtain ⟨Q, hQ, _, hbs⟩ :=
    discounted_terminal_eq_S0_of_physical (K := S_0) (r := r)
      ((r - μ) * Real.sqrt T / σ) hS_0 hS_0 hσ hT hWmeas hW
  haveI := hQ
  refine ⟨Q, hQ, ?_⟩
  have hfun : ∀ ω, Real.exp (-(r * T)) * bsTerminal S_0 μ σ T (W ω)
      = Real.exp (-(r * T)) * bsTerminal S_0 r σ T (W ω - (r - μ) * Real.sqrt T / σ) := by
    intro ω
    rw [bsTerminal_physical_eq_riskNeutral S_0 μ r σ T (W ω) (ne_of_gt hσ) hT.le]
  rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
  exact hbs

end MathFin
