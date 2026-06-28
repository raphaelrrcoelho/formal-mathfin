/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaLocalized

/-! # Itô formula for the exponential of Brownian motion — the GBM building block

The localized Itô formula `ito_formula_td_localized` applied to the (time-independent,
exponential-growth) value function `f(t, x) = exp(σx)` gives the Itô decomposition of
`exp(σ B_t)` — the diffusion core of geometric Brownian motion
`S_t = S₀ exp((r − σ²/2)t + σ B_t)`:

  `exp(σ B_T) − exp(σ B_0) =ᵐ ∫₀ᵀ σ·exp(σ B_s) dB_s + ∫₀ᵀ ½σ²·exp(σ B_s) ds`,

with the stochastic integral the genuine continuous Itô integral `itoIntegralCLM_T`. This is
the **first pricing-ward consumer of the analytic Itô tower** (which until now had none): the
diffusion `exp(σ B)` is decomposed by the real Itô integral, not an algebraic drift or a heat
kernel. It is the rung from which the discounted-GBM martingale — whose `−σ²/2` Itô correction
makes the drift vanish — is to be re-grounded on the Itô integral.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter ItoIntegralCLM
open scoped NNReal Topology

/-- On the plateau `|y| < 1` where `φ = id`, the smooth truncation has unit slope `φ'(y) = 1`
(uniqueness of derivative against `id`, which `φ` matches on the open interval). -/
lemma SmoothTrunc.phi'_eq_one_of_lt (S : SmoothTrunc) {y : ℝ} (hy : |y| < 1) : S.φ' y = 1 := by
  have h2 : HasDerivAt S.φ 1 y :=
    (hasDerivAt_id y).congr_of_eventuallyEq (by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hy] with z hz
      exact S.id_near z hz.le)
  exact (S.hasDeriv₁ y).unique h2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-- **Itô formula for `exp(σ·B)`.** For a pre-Brownian motion `B` with continuous paths,
`exp(σ B_T) − exp(σ B_0) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ ½σ²·exp(σ B_s) ds`, where the
trim-`L²` integrand `gfx` realizes `s ↦ σ·exp(σ B_s)`. The instantiation of
`ito_formula_td_localized` at the time-independent exponential-growth value function
`f(t, x) = exp(σx)` (whose partials `f_x = σ exp(σx)`, `f_xx = σ² exp(σx)` are unbounded —
out of reach of the bounded-derivative formula — but of exponential growth). -/
theorem ito_formula_expBrownian (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω) (T : ℝ≥0) (σ : ℝ) :
    ∃ gfx : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω => Real.exp (σ * B T ω) - Real.exp (σ * B 0 ω)) =ᵐ[μ]
        (fun ω => (itoIntegralCLM_T hB T hBmeas gfx) ω
          + ∫ s in Set.Ioc 0 T, (1 / 2) * (σ ^ 2 * Real.exp (σ * B s ω))
              ∂ItoIntegralL2.timeMeasure) := by
  -- the exponential-growth bound constant `C = |σ|³ + σ² + |σ|` dominates every partial
  set C : ℝ := |σ| ^ 3 + σ ^ 2 + |σ| with hC
  have hexpσ : ∀ x : ℝ, Real.exp (σ * x) ≤ Real.exp (|σ| * |x|) := fun x =>
    Real.exp_le_exp.mpr (le_trans (le_abs_self _) (by rw [abs_mul]))
  -- the six exp-growth bounds, with a single `C`, `lam = |σ|`
  have hbd : ∀ (k : ℝ), |k| ≤ C → ∀ x : ℝ,
      |k * Real.exp (σ * x)| ≤ C * Real.exp (|σ| * |x|) := by
    intro k hk x
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hk (hexpσ x) (Real.exp_nonneg _) (le_trans (abs_nonneg _) hk)
  have hkx : |σ| ≤ C := by rw [hC]; nlinarith [abs_nonneg σ, sq_nonneg σ, sq_abs σ]
  have hkxx : |σ ^ 2| ≤ C := by
    rw [hC, abs_pow, sq_abs]; nlinarith [abs_nonneg σ, pow_nonneg (abs_nonneg σ) 3, sq_nonneg σ]
  have hkxxx : |σ ^ 3| ≤ C := by
    rw [hC, abs_pow]; nlinarith [abs_nonneg σ, sq_nonneg σ, sq_abs σ, pow_nonneg (abs_nonneg σ) 3]
  have hlin : ∀ x : ℝ, HasDerivAt (fun u => σ * u) σ x :=
    fun x => by simpa using (hasDerivAt_id x).const_mul σ
  obtain ⟨gfx, hgfx⟩ := ito_formula_td_localized hB hBmeas hBcont T
    (f := fun _ x => Real.exp (σ * x)) (f_t := fun _ _ => 0)
    (f_x := fun _ x => σ * Real.exp (σ * x)) (f_xx := fun _ x => σ ^ 2 * Real.exp (σ * x))
    (f_tt := fun _ _ => 0) (f_tx := fun _ _ => 0)
    (f_xxx := fun _ x => σ ^ 3 * Real.exp (σ * x))
    (fun t x => hasDerivAt_const t _) (fun t x => hasDerivAt_const t _)
    (fun t x => hasDerivAt_const x _)
    (fun t x => by
      rw [show σ * Real.exp (σ * x) = Real.exp (σ * x) * σ by ring]
      exact (hlin x).exp)
    (fun t x => by
      rw [show σ ^ 2 * Real.exp (σ * x) = σ * (Real.exp (σ * x) * σ) by ring]
      exact ((hlin x).exp).const_mul σ)
    (fun t x => by
      rw [show σ ^ 3 * Real.exp (σ * x) = σ ^ 2 * (Real.exp (σ * x) * σ) by ring]
      exact ((hlin x).exp).const_mul (σ ^ 2))
    continuous_const
    ((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).const_mul σ)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).const_mul (σ ^ 2))
    (lam := |σ|) (C := C) (abs_nonneg σ)
    (fun t x => by simpa using mul_nonneg (le_trans (abs_nonneg _) hkx) (Real.exp_nonneg _))
    (fun t x => hbd σ hkx x) (fun t x => hbd (σ ^ 2) hkxx x)
    (fun t x => by simpa using mul_nonneg (le_trans (abs_nonneg _) hkx) (Real.exp_nonneg _))
    (fun t x => by simpa using mul_nonneg (le_trans (abs_nonneg _) hkx) (Real.exp_nonneg _))
    (fun t x => hbd (σ ^ 3) hkxxx x)
  refine ⟨gfx, ?_⟩
  filter_upwards [hgfx] with ω hω
  rw [hω, add_right_inj]
  exact integral_congr_ae (ae_of_all _ fun s => zero_add _)

/-- **Itô formula for geometric Brownian motion.** Writing `Ŝ(t) = S₀ exp((m − σ²/2)t + σ B_t)`
for the GBM value function, the localized Itô formula — applied to the *time-localized* value
function `(t, x) ↦ S₀ exp((m − σ²/2)·φₙ(t) + σx)` with `φₙ = S.cut n`, `n = ⌈T⌉₊` (the cutoff
equals the identity on `[0, T]`, so it is the genuine GBM exponent there, yet is globally bounded,
so the localized formula's exponential-in-`x` growth hypotheses hold *uniformly in time*) — yields

  `Ŝ(T) − Ŝ(0) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ m·Ŝ(s) ds`,

with the genuine continuous Itô integral `itoIntegralCLM_T` carrying the `σ Ŝ` diffusion. The drift
is `m·Ŝ` because the time-localization contributes `(m − σ²/2)·Ŝ` and the Itô second-order term
`½σ²·Ŝ`, summing to `m·Ŝ`. **Setting `m = 0` makes the drift vanish** — the Itô-integral reading
of the discounted-GBM martingale, grounding it on the continuous Itô integral rather than the
explicit Wald exponential. -/
theorem ito_formula_gbm (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω) (T : ℝ≥0) (S₀ m σ : ℝ) :
    ∃ gfx : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω => S₀ * Real.exp ((m - σ ^ 2 / 2) * (T : ℝ) + σ * B T ω)
              - S₀ * Real.exp ((m - σ ^ 2 / 2) * (0 : ℝ) + σ * B 0 ω)) =ᵐ[μ]
        (fun ω => (itoIntegralCLM_T hB T hBmeas gfx) ω
          + ∫ s in Set.Ioc 0 T, m * (S₀ * Real.exp ((m - σ ^ 2 / 2) * (s : ℝ) + σ * B s ω))
              ∂ItoIntegralL2.timeMeasure) := by
  obtain ⟨S⟩ := smoothTrunc_exists
  set a : ℝ := m - σ ^ 2 / 2 with ha
  set n : ℕ := ⌈(T : ℝ)⌉₊ with hn
  have hM1 : (0 : ℝ) ≤ S.M₁ := le_trans (abs_nonneg _) (S.bdd₁ 0)
  have hM2 : (0 : ℝ) ≤ S.M₂ := le_trans (abs_nonneg _) (S.bdd₂ 0)
  have hTn : (T : ℝ) ≤ (n : ℝ) := by rw [hn]; exact Nat.le_ceil _
  -- on `[0, T]` the cutoff is the identity with unit slope
  have hcut_id : ∀ y : ℝ, |y| ≤ (n : ℝ) + 1 → S.cut n y = y := by
    intro y hy
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : |y / ((n : ℝ) + 1)| ≤ 1 := by rw [abs_div, abs_of_pos hn1, div_le_one hn1]; exact hy
    rw [SmoothTrunc.cut, S.id_near _ hle]; field_simp
  have hcutD1_one : ∀ y : ℝ, |y| < (n : ℝ) + 1 → S.cutD1 n y = 1 := by
    intro y hy
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [SmoothTrunc.cutD1]
    exact S.phi'_eq_one_of_lt (by rw [abs_div, abs_of_pos hn1, div_lt_one hn1]; exact hy)
  -- the exponential-growth constant `C = Cs · K0`, `lam = |σ|`
  set K0 : ℝ := |S₀| * Real.exp (|a| * S.M₀ * ((n : ℝ) + 1)) with hK0
  set Cs : ℝ := |a| * S.M₁ + |σ| + σ ^ 2 + (|a| * S.M₂ + a ^ 2 * S.M₁ ^ 2)
      + |a| * |σ| * S.M₁ + |σ| ^ 3 with hCs
  set C : ℝ := Cs * K0 with hC
  have t1 : (0 : ℝ) ≤ |a| * S.M₁ := mul_nonneg (abs_nonneg _) hM1
  have t2 : (0 : ℝ) ≤ |σ| := abs_nonneg _
  have t3 : (0 : ℝ) ≤ σ ^ 2 := sq_nonneg _
  have t4 : (0 : ℝ) ≤ |a| * S.M₂ + a ^ 2 * S.M₁ ^ 2 :=
    add_nonneg (mul_nonneg (abs_nonneg _) hM2) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have t5 : (0 : ℝ) ≤ |a| * |σ| * S.M₁ := mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hM1
  have t6 : (0 : ℝ) ≤ |σ| ^ 3 := by positivity
  have hCs_nonneg : (0 : ℝ) ≤ Cs := by rw [hCs]; linarith [t1, t2, t3, t4, t5, t6]
  -- the uniform dominator `|Ŝ(t, x)| ≤ K0 · exp(|σ| |x|)`
  have hDbd : ∀ t x : ℝ, |S₀ * Real.exp (a * S.cut n t + σ * x)| ≤ K0 * Real.exp (|σ| * |x|) := by
    intro t x
    rw [abs_mul, abs_of_pos (Real.exp_pos _), hK0, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg S₀)
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    calc a * S.cut n t + σ * x
        ≤ |a * S.cut n t| + |σ * x| := add_le_add (le_abs_self _) (le_abs_self _)
      _ = |a| * |S.cut n t| + |σ| * |x| := by rw [abs_mul, abs_mul]
      _ ≤ |a| * (S.M₀ * ((n : ℝ) + 1)) + |σ| * |x| := by
          linarith [mul_le_mul_of_nonneg_left (S.cut_bdd n t) (abs_nonneg a)]
      _ = |a| * S.M₀ * ((n : ℝ) + 1) + |σ| * |x| := by ring
  -- the slot helper: a `Cs`-bounded coefficient times `Ŝ` is exp-growth dominated by `C`
  have hbound : ∀ cf : ℝ → ℝ, (∀ t, |cf t| ≤ Cs) →
      ∀ t x : ℝ, |cf t * (S₀ * Real.exp (a * S.cut n t + σ * x))| ≤ C * Real.exp (|σ| * |x|) := by
    intro cf hcf t x
    rw [abs_mul, hC]
    calc |cf t| * |S₀ * Real.exp (a * S.cut n t + σ * x)|
        ≤ Cs * (K0 * Real.exp (|σ| * |x|)) := mul_le_mul (hcf t) (hDbd t x) (abs_nonneg _) hCs_nonneg
      _ = Cs * K0 * Real.exp (|σ| * |x|) := by ring
  -- the six coefficient bounds `|cf t| ≤ Cs`
  have hcoef_t : ∀ t : ℝ, |a * S.cutD1 n t| ≤ Cs := fun t => by
    rw [abs_mul, hCs]
    have h := mul_le_mul_of_nonneg_left (S.cutD1_bdd n t) (abs_nonneg a)
    linarith [h, t2, t3, t4, t5, t6]
  have hcoef_x : ∀ _t : ℝ, |σ| ≤ Cs := fun _ => by rw [hCs]; linarith [t1, t3, t4, t5, t6]
  have hcoef_xx : ∀ _t : ℝ, |σ ^ 2| ≤ Cs := fun _ => by
    rw [abs_of_nonneg (sq_nonneg σ), hCs]; linarith [t1, t2, t4, t5, t6]
  have hcoef_tt : ∀ t : ℝ, |a * S.cutD2 n t + a ^ 2 * S.cutD1 n t ^ 2| ≤ Cs := fun t => by
    have hb1 : |a * S.cutD2 n t| ≤ |a| * S.M₂ := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (S.cutD2_bdd n t) (abs_nonneg a)
    have hb2 : |a ^ 2 * S.cutD1 n t ^ 2| ≤ a ^ 2 * S.M₁ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg a), abs_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (S.cutD1_bdd n t) 2) (sq_nonneg a)
    refine (abs_add_le _ _).trans ?_
    rw [hCs]; linarith [hb1, hb2, t1, t2, t3, t5, t6]
  have hcoef_tx : ∀ t : ℝ, |a * σ * S.cutD1 n t| ≤ Cs := fun t => by
    rw [abs_mul, abs_mul, hCs]
    have h := mul_le_mul_of_nonneg_left (S.cutD1_bdd n t) (mul_nonneg (abs_nonneg a) (abs_nonneg σ))
    linarith [h, t1, t2, t3, t4, t6]
  have hcoef_xxx : ∀ _t : ℝ, |σ ^ 3| ≤ Cs := fun _ => by
    rw [abs_pow, hCs]; linarith [t1, t2, t3, t4, t5]
  -- the clean `x`-exponent derivative (avoids the `σ * 1` artifact of `const_mul`)
  have hlinx : ∀ b y : ℝ, HasDerivAt (fun u => b + σ * u) σ y :=
    fun b y => by simpa using ((hasDerivAt_id y).const_mul σ).const_add b
  -- the GBM value `Ŝ(t, x) = S₀ exp(a·φₙ(t) + σx)` is jointly continuous (shared by the three
  -- partials, each `(const)·Ŝ`)
  have hScont : Continuous fun p : ℝ × ℝ => S₀ * Real.exp (a * S.cut n p.1 + σ * p.2) :=
    continuous_const.mul (Real.continuous_exp.comp
      ((continuous_const.mul ((S.continuous_cut n).comp continuous_fst)).add
        (continuous_const.mul continuous_snd)))
  obtain ⟨gfx, hgfx⟩ := ito_formula_td_localized hB hBmeas hBcont T
    (f := fun t x => S₀ * Real.exp (a * S.cut n t + σ * x))
    (f_t := fun t x => a * S.cutD1 n t * (S₀ * Real.exp (a * S.cut n t + σ * x)))
    (f_x := fun t x => σ * (S₀ * Real.exp (a * S.cut n t + σ * x)))
    (f_xx := fun t x => σ ^ 2 * (S₀ * Real.exp (a * S.cut n t + σ * x)))
    (f_tt := fun t x => (a * S.cutD2 n t + a ^ 2 * S.cutD1 n t ^ 2)
      * (S₀ * Real.exp (a * S.cut n t + σ * x)))
    (f_tx := fun t x => a * σ * S.cutD1 n t * (S₀ * Real.exp (a * S.cut n t + σ * x)))
    (f_xxx := fun t x => σ ^ 3 * (S₀ * Real.exp (a * S.cut n t + σ * x)))
    (fun t x => by
      rw [show a * S.cutD1 n t * (S₀ * Real.exp (a * S.cut n t + σ * x))
            = S₀ * (Real.exp (a * S.cut n t + σ * x) * (a * S.cutD1 n t)) by ring]
      exact (((S.cut_hasDerivAt n t).const_mul a).add_const (σ * x)).exp.const_mul S₀)
    (fun t x => by
      rw [show (a * S.cutD2 n t + a ^ 2 * S.cutD1 n t ^ 2) * (S₀ * Real.exp (a * S.cut n t + σ * x))
            = (a * S.cutD2 n t) * (S₀ * Real.exp (a * S.cut n t + σ * x))
              + (a * S.cutD1 n t)
                * (S₀ * (Real.exp (a * S.cut n t + σ * x) * (a * S.cutD1 n t))) by ring]
      exact ((S.cutD1_hasDerivAt n t).const_mul a).mul
        ((((S.cut_hasDerivAt n t).const_mul a).add_const (σ * x)).exp.const_mul S₀))
    (fun t x => by
      rw [show a * σ * S.cutD1 n t * (S₀ * Real.exp (a * S.cut n t + σ * x))
            = (a * S.cutD1 n t) * (S₀ * (Real.exp (a * S.cut n t + σ * x) * σ)) by ring]
      exact (((hlinx (a * S.cut n t) x).exp).const_mul S₀).const_mul (a * S.cutD1 n t))
    (fun t x => by
      rw [show σ * (S₀ * Real.exp (a * S.cut n t + σ * x))
            = S₀ * (Real.exp (a * S.cut n t + σ * x) * σ) by ring]
      exact ((hlinx (a * S.cut n t) x).exp).const_mul S₀)
    (fun t x => by
      rw [show σ ^ 2 * (S₀ * Real.exp (a * S.cut n t + σ * x))
            = σ * (S₀ * (Real.exp (a * S.cut n t + σ * x) * σ)) by ring]
      exact (((hlinx (a * S.cut n t) x).exp).const_mul S₀).const_mul σ)
    (fun t x => by
      rw [show σ ^ 3 * (S₀ * Real.exp (a * S.cut n t + σ * x))
            = σ ^ 2 * (S₀ * (Real.exp (a * S.cut n t + σ * x) * σ)) by ring]
      exact (((hlinx (a * S.cut n t) x).exp).const_mul S₀).const_mul (σ ^ 2))
    ((continuous_const.mul ((S.continuous_cutD1 n).comp continuous_fst)).mul hScont)
    (continuous_const.mul hScont)
    (continuous_const.mul hScont)
    (lam := |σ|) (C := C) (abs_nonneg σ)
    (fun t x => hbound (fun t => a * S.cutD1 n t) hcoef_t t x)
    (fun t x => hbound (fun _ => σ) hcoef_x t x)
    (fun t x => hbound (fun _ => σ ^ 2) hcoef_xx t x)
    (fun t x => hbound (fun t => a * S.cutD2 n t + a ^ 2 * S.cutD1 n t ^ 2) hcoef_tt t x)
    (fun t x => hbound (fun t => a * σ * S.cutD1 n t) hcoef_tx t x)
    (fun t x => hbound (fun _ => σ ^ 3) hcoef_xxx t x)
  -- reduce off `[0, T]`: the cutoff is the identity, with unit slope, so the drift is `m·Ŝ`
  refine ⟨gfx, ?_⟩
  filter_upwards [hgfx] with ω hω
  rw [hcut_id (T : ℝ) (by rw [abs_of_nonneg (NNReal.coe_nonneg T)]; linarith),
      hcut_id (0 : ℝ) (by rw [abs_zero]; positivity)] at hω
  rw [hω, add_right_inj]
  refine integral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs => ?_))
  have hsn : (s : ℝ) ≤ (n : ℝ) := le_trans (by exact_mod_cast hs.2) hTn
  dsimp only
  rw [hcut_id (s : ℝ) (by rw [abs_of_nonneg (NNReal.coe_nonneg s)]; linarith),
      hcutD1_one (s : ℝ) (by rw [abs_of_nonneg (NNReal.coe_nonneg s)]; linarith), ha]
  ring

/-- **The discounted GBM increment is a pure Itô integral (zero drift).** Specializing
`ito_formula_gbm` at the risk-neutral drift `m = 0`: the discounted geometric Brownian motion
`Ŝ(t) = S₀ exp(−(σ²/2)·t + σ B_t)` satisfies

  `Ŝ(T) − Ŝ(0) =ᵐ itoIntegralCLM_T gfx`,

the drift vanishing because the localization drift `−σ²/2` exactly cancels the Itô second-order
correction `½σ²`. This is the **Itô-integral content of the discounted-GBM martingale**
(`discountedGBM_isMartingale`, there obtained via the Wald exponential): the discounted price
moves only through its `σ Ŝ` diffusion against `dB`, with no drift — so the increment is a pure
Itô integral, and the martingale property is the martingale property of that integral. -/
theorem discountedGBM_eq_itoIntegral (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun s : ℝ≥0 => B s ω) (T : ℝ≥0) (S₀ σ : ℝ) :
    ∃ gfx : Lp ℝ 2 (trimMeasure_T (μ := μ) T hBmeas),
      (fun ω => S₀ * Real.exp (-(σ ^ 2 / 2) * (T : ℝ) + σ * B T ω)
              - S₀ * Real.exp (σ * B 0 ω)) =ᵐ[μ]
        (fun ω => (itoIntegralCLM_T hB T hBmeas gfx) ω) := by
  obtain ⟨gfx, hgfx⟩ := ito_formula_gbm hB hBmeas hBcont T S₀ 0 σ
  refine ⟨gfx, ?_⟩
  filter_upwards [hgfx] with ω hω
  rw [show -(σ ^ 2 / 2) * (T : ℝ) = (0 - σ ^ 2 / 2) * (T : ℝ) by ring,
      show σ * B 0 ω = (0 - σ ^ 2 / 2) * (0 : ℝ) + σ * B 0 ω by ring, hω]
  simp

end MathFin
