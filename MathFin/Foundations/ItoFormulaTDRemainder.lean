/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoFormulaRemainder
public import MathFin.Foundations.ItoLemma2D

/-! # The time-dependent Itô–Taylor remainder vanishes in `L²`

The remainder term of the discrete 2D Itô formula `discrete_ito_formula_2d`, summed along
the uniform partition of `[0,T]` (time grid and Brownian path evaluated at the same
nodes), converges to `0` in `L²(μ)` for `f(t,x)` with bounded `f_tt, f_tx, f_xxx`. This
is the term the continuous-time time-dependent Itô formula discards.

The per-step remainder splits exactly into time, cross, and space pieces
(`abs_discreteTaylorRemainder2D_le`):

  `R = [f(t₁,y) − f(t₀,y) − f_t(t₀,y)Δt] + [f_t(t₀,y) − f_t(t₀,x)]·Δt + R_space(t₀; x,y)`,

bounded by `C_tt·Δt² + C_tx·|Δx|·Δt + C_xxx·|Δx|³` — first-order time Taylor at frozen
space (`abs_taylor1_le`), a mean-value bound on the space-section of `f_t`
(`abs_sub_le_of_hasDerivAt`), and the 1D cubic bound `abs_discreteTaylorRemainder_le`
applied to the `t₀`-section. Under Brownian scaling `E[R²] = O(Δt³)` (the Gaussian
moments `E[ΔB²] = Δt`, `E[ΔB⁶] = 15Δt³`), so Cauchy–Schwarz on the sum gives
`E[(∑ₖ Rₖ)²] ≤ n·∑ₖ E[Rₖ²] = O(n⁻¹) → 0` — the same rate as the time-independent
remainder `tendsto_ito_remainder`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter QuadraticVariationL2
open scoped NNReal Topology

/-- **Mean-value bound**: a function with derivative bounded by `M` moves at most
`M·|y − x|` across `[x, y]`. The one-level convex mean-value estimate; the space-section
of `f_t` consumes it with `M = sup |f_tx|`. -/
theorem abs_sub_le_of_hasDerivAt {g g' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) {M : ℝ} (hM : ∀ x, |g' x| ≤ M) (x y : ℝ) :
    |g y - g x| ≤ M * |y - x| := by
  have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hg u).hasDerivWithinAt) (fun u _ => by rw [Real.norm_eq_abs]; exact hM u)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using h

/-- **Quadratic bound on the order-1 Taylor remainder.** For `g ∈ C²` with `|g″| ≤ M`,
`|g y − g x − g′(x)(y − x)| ≤ M·|y − x|²`. Two levels of the convex mean-value bound —
first on `g′ − g′(x)`, then on the primitive defect — each gaining one power of `|y − x|`.
The time direction of the 2D Itô remainder consumes it with `g = f(·, y)`. -/
theorem abs_taylor1_le {g g' g'' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : ∀ x, HasDerivAt g' (g'' x) x)
    {M : ℝ} (hM : ∀ x, |g'' x| ≤ M) (x y : ℝ) :
    |g y - g x - g' x * (y - x)| ≤ M * |y - x| ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hmem : ∀ t ∈ Set.uIcc x y, |t - x| ≤ |y - x| := by
    intro t ht
    rcases le_total x y with hxy | hyx
    · rw [Set.uIcc_of_le hxy] at ht
      rw [abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - x),
        abs_of_nonneg (by linarith [hxy] : (0 : ℝ) ≤ y - x)]
      linarith [ht.2]
    · rw [Set.uIcc_of_ge hyx] at ht
      rw [abs_of_nonpos (by linarith [ht.2] : t - x ≤ 0),
        abs_of_nonpos (by linarith [hyx] : y - x ≤ 0)]
      linarith [ht.1]
  -- Level 1: `|g′ t − g′ x| ≤ M·|y−x|` on the segment
  have hL1 : ∀ t ∈ Set.uIcc x y, |g' t - g' x| ≤ M * |y - x| := fun t ht =>
    (abs_sub_le_of_hasDerivAt hg' hM x t).trans
      (mul_le_mul_of_nonneg_left (hmem t ht) hM0)
  -- Level 0: the remainder itself
  have hd0 : ∀ u, HasDerivAt (fun s => g s - g x - g' x * (s - x)) (g' u - g' x) u := fun u => by
    have h := ((hg u).sub_const (g x)).sub
      (((hasDerivAt_id u).sub_const x).const_mul (g' x))
    convert h using 1 <;> first | rfl | ring
  have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hd0 u).hasDerivWithinAt)
    (fun u hu => by rw [Real.norm_eq_abs]; exact hL1 u hu)
    Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.norm_eq_abs, sub_self, mul_zero, sub_zero] at h
  calc |g y - g x - g' x * (y - x)| ≤ M * |y - x| * |y - x| := h
    _ = M * |y - x| ^ 2 := by ring

/-- **Time–cross–space bound on the 2D discrete remainder.** For `f(t, x)` with time
chain `f_t, f_tt`, mixed `f_tx = ∂ₓ f_t`, and space chain `f_x, f_xx, f_xxx`, all with
the displayed bounds,

  `|R₂D(t₀,t₁;x,y)| ≤ C_tt·|t₁−t₀|² + C_tx·|y−x|·|t₁−t₀| + C_xxx·|y−x|³`.

The remainder splits exactly (by `ring`) into a time-Taylor piece at frozen space `y`, a
cross piece `(f_t(t₀,y) − f_t(t₀,x))·Δt`, and the 1D space remainder of the `t₀`-section;
each piece is bounded by the corresponding mean-value estimate. -/
theorem abs_discreteTaylorRemainder2D_le
    {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s => f s x) (f_t t x) t)
    (hf_tt : ∀ t x, HasDerivAt (fun s => f_t s x) (f_tt t x) t)
    (hf_tx : ∀ t x, HasDerivAt (fun u => f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u => f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u => f_x t u) (f_xx t x) x)
    (hf_xxx : ∀ t x, HasDerivAt (fun u => f_xx t u) (f_xxx t x) x)
    {Ctt Ctx Cxxx : ℝ}
    (hbd_tt : ∀ t x, |f_tt t x| ≤ Ctt) (hbd_tx : ∀ t x, |f_tx t x| ≤ Ctx)
    (hbd_xxx : ∀ t x, |f_xxx t x| ≤ Cxxx) (t₀ t₁ x y : ℝ) :
    |discreteTaylorRemainder2D f f_t f_x f_xx t₀ t₁ x y|
      ≤ Ctt * |t₁ - t₀| ^ 2 + Ctx * |y - x| * |t₁ - t₀| + Cxxx * |y - x| ^ 3 := by
  have hsplit : discreteTaylorRemainder2D f f_t f_x f_xx t₀ t₁ x y
      = (f t₁ y - f t₀ y - f_t t₀ y * (t₁ - t₀))
        + (f_t t₀ y - f_t t₀ x) * (t₁ - t₀)
        + discreteTaylorRemainder (fun u => f t₀ u) (fun u => f_x t₀ u)
            (fun u => f_xx t₀ u) x y := by
    unfold discreteTaylorRemainder2D discreteTaylorRemainder
    ring
  have h1 : |f t₁ y - f t₀ y - f_t t₀ y * (t₁ - t₀)| ≤ Ctt * |t₁ - t₀| ^ 2 :=
    abs_taylor1_le (g := fun s => f s y) (g' := fun s => f_t s y) (g'' := fun s => f_tt s y)
      (fun s => hf_t s y) (fun s => hf_tt s y) (fun s => hbd_tt s y) t₀ t₁
  have h2 : |(f_t t₀ y - f_t t₀ x) * (t₁ - t₀)| ≤ Ctx * |y - x| * |t₁ - t₀| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (abs_sub_le_of_hasDerivAt (g := fun u => f_t t₀ u) (g' := fun u => f_tx t₀ u)
        (fun u => hf_tx t₀ u) (fun u => hbd_tx t₀ u) x y) (abs_nonneg _)
  have h3 : |discreteTaylorRemainder (fun u => f t₀ u) (fun u => f_x t₀ u)
      (fun u => f_xx t₀ u) x y| ≤ Cxxx * |y - x| ^ 3 :=
    abs_discreteTaylorRemainder_le (fun u => hf_x t₀ u) (fun u => hf_xx t₀ u)
      (fun u => hf_xxx t₀ u) (fun u => hbd_xxx t₀ u) x y
  calc |discreteTaylorRemainder2D f f_t f_x f_xx t₀ t₁ x y|
      ≤ |f t₁ y - f t₀ y - f_t t₀ y * (t₁ - t₀)|
        + |(f_t t₀ y - f_t t₀ x) * (t₁ - t₀)|
        + |discreteTaylorRemainder (fun u => f t₀ u) (fun u => f_x t₀ u)
            (fun u => f_xx t₀ u) x y| := by
        rw [hsplit]; exact abs_add_three _ _ _
    _ ≤ Ctt * |t₁ - t₀| ^ 2 + Ctx * |y - x| * |t₁ - t₀| + Cxxx * |y - x| ^ 3 := by
        gcongr

/-- **Squared form of the remainder bound**:
`R² ≤ 3C_tt²·Δt⁴ + 3C_tx²·Δt²·Δx² + 3C_xxx²·Δx⁶` — the three-term bound
`abs_discreteTaylorRemainder2D_le` squared via `(u+v+w)² ≤ 3(u²+v²+w²)`, with the even
powers absorbing the absolute values. The shape the Gaussian moments integrate: `Δt⁴` is
deterministic, `E[Δx²] = Δt`, `E[Δx⁶] = 15Δt³` — every term is `O(Δt³)`. -/
theorem sq_discreteTaylorRemainder2D_le
    {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s => f s x) (f_t t x) t)
    (hf_tt : ∀ t x, HasDerivAt (fun s => f_t s x) (f_tt t x) t)
    (hf_tx : ∀ t x, HasDerivAt (fun u => f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u => f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u => f_x t u) (f_xx t x) x)
    (hf_xxx : ∀ t x, HasDerivAt (fun u => f_xx t u) (f_xxx t x) x)
    {Ctt Ctx Cxxx : ℝ}
    (hbd_tt : ∀ t x, |f_tt t x| ≤ Ctt) (hbd_tx : ∀ t x, |f_tx t x| ≤ Ctx)
    (hbd_xxx : ∀ t x, |f_xxx t x| ≤ Cxxx) (t₀ t₁ x y : ℝ) :
    discreteTaylorRemainder2D f f_t f_x f_xx t₀ t₁ x y ^ 2
      ≤ 3 * Ctt ^ 2 * (t₁ - t₀) ^ 4 + 3 * Ctx ^ 2 * (t₁ - t₀) ^ 2 * (y - x) ^ 2
        + 3 * Cxxx ^ 2 * (y - x) ^ 6 := by
  have habs := abs_discreteTaylorRemainder2D_le hf_t hf_tt hf_tx hf_x hf_xx hf_xxx
    hbd_tt hbd_tx hbd_xxx t₀ t₁ x y
  have hkey : ∀ u v w : ℝ, (u + v + w) ^ 2 ≤ 3 * u ^ 2 + 3 * v ^ 2 + 3 * w ^ 2 := by
    intro u v w
    nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (u - w)]
  have h4 : (|t₁ - t₀| ^ 2) ^ 2 = (t₁ - t₀) ^ 4 := by rw [sq_abs]; ring
  have h6 : (|y - x| ^ 3) ^ 2 = (y - x) ^ 6 := by
    have h36 : (|y - x| ^ 3) ^ 2 = |y - x| ^ 6 := by ring
    rw [h36, ← abs_pow]
    exact abs_of_nonneg (by positivity)
  calc discreteTaylorRemainder2D f f_t f_x f_xx t₀ t₁ x y ^ 2
      = |discreteTaylorRemainder2D f f_t f_x f_xx t₀ t₁ x y| ^ 2 := (sq_abs _).symm
    _ ≤ (Ctt * |t₁ - t₀| ^ 2 + Ctx * |y - x| * |t₁ - t₀| + Cxxx * |y - x| ^ 3) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ 3 * (Ctt * |t₁ - t₀| ^ 2) ^ 2 + 3 * (Ctx * |y - x| * |t₁ - t₀|) ^ 2
          + 3 * (Cxxx * |y - x| ^ 3) ^ 2 := hkey _ _ _
    _ = 3 * Ctt ^ 2 * ((|t₁ - t₀| ^ 2) ^ 2)
          + 3 * Ctx ^ 2 * ((|t₁ - t₀| ^ 2) * (|y - x| ^ 2))
          + 3 * Cxxx ^ 2 * ((|y - x| ^ 3) ^ 2) := by ring
    _ = 3 * Ctt ^ 2 * (t₁ - t₀) ^ 4 + 3 * Ctx ^ 2 * (t₁ - t₀) ^ 2 * (y - x) ^ 2
          + 3 * Cxxx ^ 2 * (y - x) ^ 6 := by
        rw [h4, h6, sq_abs, sq_abs]; ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  (hB : IsPreBrownianReal B μ)

include hB

/-- A squared Brownian increment is integrable: `(ΔB)² = ((ΔB)² − Δt) + Δt`, the centered
part being `L²` (`memLp_increment_sq_centered_two`) over a probability space. -/
theorem integrable_increment_sq (t₀ t₁ : ℝ≥0) :
    Integrable (fun ω => (B t₁ ω - B t₀ ω) ^ 2) μ := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have h := (memLp_increment_sq_centered_two (B := B) (μ := μ) hB t₀ t₁
      ((t₁ : ℝ) - t₀)).integrable one_le_two
  refine (h.add (integrable_const ((t₁ : ℝ) - t₀))).congr
    (Eventually.of_forall fun ω => ?_)
  show (B t₁ ω - B t₀ ω) ^ 2 - ((t₁ : ℝ) - t₀) + ((t₁ : ℝ) - t₀) = (B t₁ ω - B t₀ ω) ^ 2
  ring

/-- **The per-step 2D remainder along Brownian nodes is `L²(μ)`**: its square is dominated
by the integrable `3C_tt²·Δt⁴ + 3C_tx²·Δt²·(ΔB)² + 3C_xxx²·(ΔB)⁶`
(`sq_discreteTaylorRemainder2D_le` + the Gaussian moment integrability). Consumed here for
the per-step expectation bound, and by the Itô-formula assembly (`ItoFormulaTD`), where
the remainder sum must be an `L²` function for the squeeze's integrability side
conditions. -/
theorem memLp_discreteTaylorRemainder2D_two
    (hBmeas : ∀ t, Measurable (B t))
    {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s => f s x) (f_t t x) t)
    (hf_tt : ∀ t x, HasDerivAt (fun s => f_t s x) (f_tt t x) t)
    (hf_tx : ∀ t x, HasDerivAt (fun u => f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u => f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u => f_x t u) (f_xx t x) x)
    (hf_xxx : ∀ t x, HasDerivAt (fun u => f_xx t u) (f_xxx t x) x)
    {Ctt Ctx Cxxx : ℝ}
    (hbd_tt : ∀ t x, |f_tt t x| ≤ Ctt) (hbd_tx : ∀ t x, |f_tx t x| ≤ Ctx)
    (hbd_xxx : ∀ t x, |f_xxx t x| ≤ Cxxx) (t₀ t₁ : ℝ≥0) :
    MemLp (fun ω => discreteTaylorRemainder2D f f_t f_x f_xx t₀ t₁ (B t₀ ω) (B t₁ ω)) 2 μ := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  -- section measurability (each section is differentiable, hence continuous)
  have hfm : ∀ c : ℝ, Measurable (f c) := fun c =>
    (continuous_iff_continuousAt.mpr fun x => (hf_x c x).continuousAt).measurable
  have hf_tm : ∀ c : ℝ, Measurable (f_t c) := fun c =>
    (continuous_iff_continuousAt.mpr fun x => (hf_tx c x).continuousAt).measurable
  have hf_xm : ∀ c : ℝ, Measurable (f_x c) := fun c =>
    (continuous_iff_continuousAt.mpr fun x => (hf_xx c x).continuousAt).measurable
  have hf_xxm : ∀ c : ℝ, Measurable (f_xx c) := fun c =>
    (continuous_iff_continuousAt.mpr fun x => (hf_xxx c x).continuousAt).measurable
  have hmeas : Measurable (fun ω => discreteTaylorRemainder2D f f_t f_x f_xx
      t₀ t₁ (B t₀ ω) (B t₁ ω)) := by
    unfold discreteTaylorRemainder2D
    exact (((((hfm _).comp (hBmeas _)).sub ((hfm _).comp (hBmeas _))).sub
      (((hf_tm _).comp (hBmeas _)).mul_const _)).sub
      (((hf_xm _).comp (hBmeas _)).mul ((hBmeas _).sub (hBmeas _)))).sub
      ((((hf_xxm _).comp (hBmeas _)).mul
        (((hBmeas _).sub (hBmeas _)).pow_const 2)).const_mul (1 / 2))
  have hdom : Integrable (fun ω =>
      3 * Ctt ^ 2 * ((t₁ : ℝ) - t₀) ^ 4
        + 3 * Ctx ^ 2 * ((t₁ : ℝ) - t₀) ^ 2 * (B t₁ ω - B t₀ ω) ^ 2
        + 3 * Cxxx ^ 2 * (B t₁ ω - B t₀ ω) ^ 6) μ :=
    ((integrable_const _).add
      ((integrable_increment_sq hB _ _).const_mul _)).add
      ((integrable_increment_pow6 (B := B) hB _ _).const_mul _)
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
  refine Integrable.mono' hdom (hmeas.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_discreteTaylorRemainder2D_le hf_t hf_tt hf_tx hf_x hf_xx hf_xxx
    hbd_tt hbd_tx hbd_xxx t₀ t₁ (B t₀ ω) (B t₁ ω)

/-- **The time-dependent Itô–Taylor remainder vanishes in `L²`.** For `f(t,x)` with
bounded `f_tt, f_tx, f_xxx`, the sum of 2D discrete remainders along the uniform
partition of `[0,T]` converges to `0` in `L²(μ)`, with rate `O(1/n)`. -/
theorem tendsto_ito_remainder_td
    (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    {f f_t f_x f_xx f_tt f_tx f_xxx : ℝ → ℝ → ℝ}
    (hf_t : ∀ t x, HasDerivAt (fun s => f s x) (f_t t x) t)
    (hf_tt : ∀ t x, HasDerivAt (fun s => f_t s x) (f_tt t x) t)
    (hf_tx : ∀ t x, HasDerivAt (fun u => f_t t u) (f_tx t x) x)
    (hf_x : ∀ t x, HasDerivAt (fun u => f t u) (f_x t x) x)
    (hf_xx : ∀ t x, HasDerivAt (fun u => f_x t u) (f_xx t x) x)
    (hf_xxx : ∀ t x, HasDerivAt (fun u => f_xx t u) (f_xxx t x) x)
    {Ctt Ctx Cxxx : ℝ}
    (hbd_tt : ∀ t x, |f_tt t x| ≤ Ctt) (hbd_tx : ∀ t x, |f_tx t x| ≤ Ctx)
    (hbd_xxx : ∀ t x, |f_xxx t x| ≤ Cxxx) :
    Tendsto (fun n : ℕ => ∫ ω, (∑ k ∈ Finset.range n,
        discreteTaylorRemainder2D f f_t f_x f_xx
          (unifPart T n k) (unifPart T n (k + 1))
          (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2 ∂μ) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hmono : ∀ n, Monotone (unifPart T n) := fun n a b hab => by simp only [unifPart]; gcongr
  -- integrability of the dominator, hence of the squared remainder (per-step `L²`)
  have hdom_int : ∀ n k, Integrable (fun ω =>
      3 * Ctt ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 4
        + 3 * Ctx ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2
            * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
        + 3 * Cxxx ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 6) μ :=
    fun n k =>
      ((integrable_const _).add
        ((integrable_increment_sq hB _ _).const_mul _)).add
        ((integrable_increment_pow6 (B := B) hB _ _).const_mul _)
  have hRsq_int : ∀ n k, Integrable (fun ω => (discreteTaylorRemainder2D f f_t f_x f_xx
      (unifPart T n k) (unifPart T n (k + 1))
      (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2) μ := fun n k =>
    (memLp_discreteTaylorRemainder2D_two hB hBmeas hf_t hf_tt hf_tx hf_x hf_xx hf_xxx
      hbd_tt hbd_tx hbd_xxx _ _ |>.integrable_sq)
  -- squeeze: `∫ (∑ₖ Rₖ)² ≤ K·T³/n → 0`, `K = 3C_tt²T + 3C_tx² + 45C_xxx²`
  set K : ℝ := 3 * Ctt ^ 2 * T + 3 * Ctx ^ 2 + 45 * Cxxx ^ 2 with hK_def
  refine squeeze_zero' (g := fun n : ℕ => K * (T : ℝ) ^ 3 / n)
    (Eventually.of_forall fun n => integral_nonneg fun ω => sq_nonneg _) ?_
    (by simpa using tendsto_const_div_atTop_nhds_zero_nat (K * (T : ℝ) ^ 3))
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hΔ : ∀ k ∈ Finset.range n, ((unifPart T n (k + 1) : ℝ) - unifPart T n k) = (T : ℝ) / n :=
    fun k _ => by simp only [unifPart]; push_cast; field_simp; ring
  have hTn_nn : (0 : ℝ) ≤ (T : ℝ) / n := div_nonneg (NNReal.coe_nonneg T) (Nat.cast_nonneg n)
  have hTn_le : (T : ℝ) / n ≤ T := div_le_self (NNReal.coe_nonneg T) hn1
  -- per-step expectation bound `E[Rₖ²] ≤ K·(T/n)³`
  have hstep : ∀ k ∈ Finset.range n,
      ∫ ω, (discreteTaylorRemainder2D f f_t f_x f_xx
        (unifPart T n k) (unifPart T n (k + 1))
        (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2 ∂μ
      ≤ K * ((T : ℝ) / n) ^ 3 := by
    intro k hk
    have hle := hmono n (Nat.le_succ k)
    have hi1 : Integrable (fun _ω : Ω =>
        3 * Ctt ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 4) μ :=
      integrable_const _
    have hi2 : Integrable (fun ω =>
        3 * Ctx ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2
          * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) μ :=
      (integrable_increment_sq hB _ _).const_mul _
    have hi3 : Integrable (fun ω =>
        3 * Cxxx ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 6) μ :=
      (integrable_increment_pow6 (B := B) hB _ _).const_mul _
    have hi12 : Integrable (fun ω =>
        3 * Ctt ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 4
          + 3 * Ctx ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2
              * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2) μ := hi1.add hi2
    calc ∫ ω, (discreteTaylorRemainder2D f f_t f_x f_xx
          (unifPart T n k) (unifPart T n (k + 1))
          (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2 ∂μ
        ≤ ∫ ω, (3 * Ctt ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 4
            + 3 * Ctx ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2
                * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 2
            + 3 * Cxxx ^ 2 * (B (unifPart T n (k + 1)) ω - B (unifPart T n k) ω) ^ 6) ∂μ :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
            (hdom_int n k) (Eventually.of_forall fun ω =>
              sq_discreteTaylorRemainder2D_le hf_t hf_tt hf_tx hf_x hf_xx hf_xxx
                hbd_tt hbd_tx hbd_xxx _ _ _ _)
      _ = 3 * Ctt ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 4
            + 3 * Ctx ^ 2 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 2
                * (((unifPart T n (k + 1) : ℝ)) - unifPart T n k)
            + 3 * Cxxx ^ 2 * (15 * ((unifPart T n (k + 1) : ℝ) - unifPart T n k) ^ 3) := by
          rw [integral_add hi12 hi3, integral_add hi1 hi2,
            integral_const, probReal_univ, one_smul,
            integral_const_mul, integral_const_mul,
            ItoIsometryAdapted.integral_increment_sq (B := B) hB hle,
            integral_increment_pow6 (B := B) hB hle]
      _ ≤ K * ((T : ℝ) / n) ^ 3 := by
          rw [hΔ k hk, hK_def]
          have h4 : ((T : ℝ) / n) ^ 4 ≤ (T : ℝ) * ((T : ℝ) / n) ^ 3 := by
            calc ((T : ℝ) / n) ^ 4 = ((T : ℝ) / n) * ((T : ℝ) / n) ^ 3 := by ring
              _ ≤ (T : ℝ) * ((T : ℝ) / n) ^ 3 :=
                  mul_le_mul_of_nonneg_right hTn_le (by positivity)
          have h5 : 3 * Ctt ^ 2 * ((T : ℝ) / n) ^ 4
              ≤ 3 * Ctt ^ 2 * ((T : ℝ) * ((T : ℝ) / n) ^ 3) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
          nlinarith [h5]
  -- Cauchy–Schwarz on the sum, then the per-step bound
  calc ∫ ω, (∑ k ∈ Finset.range n, discreteTaylorRemainder2D f f_t f_x f_xx
        (unifPart T n k) (unifPart T n (k + 1))
        (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2 ∂μ
      ≤ ∫ ω, (n : ℝ) * ∑ k ∈ Finset.range n, (discreteTaylorRemainder2D f f_t f_x f_xx
          (unifPart T n k) (unifPart T n (k + 1))
          (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2 ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
          ((integrable_finsetSum _ fun k _ => hRsq_int n k).const_mul _)
          (Eventually.of_forall fun ω => ?_)
        have := sq_sum_le_card_mul_sum_sq (s := Finset.range n)
          (f := fun k => discreteTaylorRemainder2D f f_t f_x f_xx
            (unifPart T n k) (unifPart T n (k + 1))
            (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω))
        rwa [Finset.card_range] at this
    _ = (n : ℝ) * ∑ k ∈ Finset.range n, ∫ ω, (discreteTaylorRemainder2D f f_t f_x f_xx
          (unifPart T n k) (unifPart T n (k + 1))
          (B (unifPart T n k) ω) (B (unifPart T n (k + 1)) ω)) ^ 2 ∂μ := by
        rw [integral_const_mul, integral_finsetSum _ fun k _ => hRsq_int n k]
    _ ≤ (n : ℝ) * ∑ k ∈ Finset.range n, K * ((T : ℝ) / n) ^ 3 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) (Nat.cast_nonneg n)
    _ = K * (T : ℝ) ^ 3 / n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

end MathFin
