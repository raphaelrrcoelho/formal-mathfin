/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.Binomial.DriftLimit

/-!
# CRR characteristic-function convergence (the CLT heart of CRR → Black–Scholes)

The deterministic-analytic correspondence in `CRRConvergence.lean` /
`DriftLimit.lean` (`crrProb_tendsto_half`, `crr_drift_limit_n`) pins down the
mean and variance of one CRR log-return increment. This file converts those
moment limits into the **distributional** statement that drives CRR → BS: the
characteristic function of the `n`-step risk-neutral log-return,

  `φₙ(t)ⁿ`  where  `φₙ(t) = pₙ e^{i (σ√Δt) t} + (1−pₙ) e^{i(−σ√Δt) t}`,

converges pointwise to the Gaussian characteristic function
`exp(i t (r − σ²/2) T − ½ t² σ² T)`, i.e. the charFun of
`N((r − σ²/2)T, σ²T)`.

The crux is `crr_charFun_pow_tendsto`. The argument:

* Since the per-step value `±σ√Δt` is real, `φₙ(t) = cos θₙ + i (2pₙ−1) sin θₙ`
  with `θₙ = σ √(T/n) · t` real (`crrStepCharFun_eq`).
* `n (φₙ − 1) → i t (r−σ²/2)T − ½ t²σ²T =: L`, splitting real/imag parts:
  - real: `n (cos θₙ − 1) = ((cos θₙ−1)/θₙ²)·(n θₙ²) → (−½)·σ²t²T`, since
    `n θₙ² = σ² t² T` exactly and `(cos u−1)/u² → −½`;
  - imag: `n (2pₙ−1) sin θₙ = [n(2pₙ−1)σ√(T/n)]·t·(sin θₙ/θₙ) → (r−σ²/2)T·t`,
    feeding `crr_drift_limit_n` and `sin u/u → 1`.
* `φₙ(t)ⁿ = (1 + (φₙ−1))ⁿ → exp L` via Mathlib's
  `Complex.tendsto_one_add_pow_exp_of_tendsto`.

Both real trig limits reduce to `sin u / u → 1` (the half-angle identity
`1 − cos u = 2 sin²(u/2)` handles the cosine).
-/

namespace QuantFin

open Filter Complex
open scoped Topology

/-! ### Real second-order trig limits at `0` -/

/-- `sin u / u → 1` as `u → 0` (`u ≠ 0`): the slope of `sin` at `0`,
where `sin' 0 = cos 0 = 1`. -/
lemma tendsto_sin_div_one :
    Tendsto (fun u : ℝ => Real.sin u / u) (𝓝[≠] 0) (𝓝 1) := by
  have h_deriv : HasDerivAt Real.sin 1 0 := by simpa using Real.hasDerivAt_sin 0
  have h_slope := h_deriv.tendsto_slope
  refine h_slope.congr' (Eventually.of_forall fun u => ?_)
  rw [slope_def_field]
  simp [Real.sin_zero]

/-- `(1 − cos u)/u² → 1/2` as `u → 0` (`u ≠ 0`), via the half-angle identity
`1 − cos u = 2 sin²(u/2)` and `sin v / v → 1`. -/
lemma tendsto_one_sub_cos_div_sq :
    Tendsto (fun u : ℝ => (1 - Real.cos u) / u ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have h_half : Tendsto (fun u : ℝ => u / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun u : ℝ => u / 2) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_id.div_const (2 : ℝ)).tendsto 0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact div_ne_zero hu (by norm_num)
  have h_s : Tendsto (fun u : ℝ => Real.sin (u / 2) / (u / 2)) (𝓝[≠] 0) (𝓝 1) :=
    tendsto_sin_div_one.comp h_half
  have h_sq : Tendsto (fun u : ℝ => (1 / 2) * (Real.sin (u / 2) / (u / 2)) ^ 2)
      (𝓝[≠] 0) (𝓝 ((1 / 2) * 1 ^ 2)) := (h_s.pow 2).const_mul (1 / 2)
  rw [show ((1 : ℝ) / 2 * 1 ^ 2) = 1 / 2 from by norm_num] at h_sq
  refine h_sq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu_ne : u ≠ 0 := hu
  have hid : 1 - Real.cos u = 2 * Real.sin (u / 2) ^ 2 := by
    have h2 : Real.cos u = 2 * Real.cos (u / 2) ^ 2 - 1 := by
      have := Real.cos_two_mul (u / 2)
      rwa [show 2 * (u / 2) = u from by ring] at this
    have h3 : Real.sin (u / 2) ^ 2 + Real.cos (u / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (u / 2)
    nlinarith [h2, h3]
  rw [hid]
  have h2ne : u / 2 ≠ 0 := div_ne_zero hu_ne (by norm_num)
  field_simp

/-! ### The per-step CRR characteristic function -/

/-- Real → complex exponential: `exp(↑x · I) = cos x + (sin x) i`. -/
private lemma cexp_ofReal_mul_I (x : ℝ) :
    Complex.exp (↑x * I) = ↑(Real.cos x) + ↑(Real.sin x) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The characteristic function of one CRR risk-neutral log-return increment,
evaluated at `t`: `φₙ(t) = pₙ e^{i (σ√Δt) t} + (1−pₙ) e^{i (−σ√Δt) t}`,
with `Δt = T/n` and `pₙ = crrProb`. -/
noncomputable def crrStepCharFun (r σ T : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (crrProb r σ T n : ℂ) * Complex.exp (I * ↑(σ * Real.sqrt (T / n) * t))
    + (1 - (crrProb r σ T n : ℂ)) * Complex.exp (I * ↑(-(σ * Real.sqrt (T / n)) * t))

/-- **Real/imaginary form of the per-step charFun**: since the increment takes
the real values `±σ√Δt`, `φₙ(t) = cos θₙ + i (2pₙ−1) sin θₙ` with
`θₙ = σ √(T/n) · t`. -/
lemma crrStepCharFun_eq (r σ T : ℝ) (n : ℕ) (t : ℝ) :
    crrStepCharFun r σ T n t
      = ↑(Real.cos (σ * Real.sqrt (T / n) * t))
        + ↑((2 * crrProb r σ T n - 1) * Real.sin (σ * Real.sqrt (T / n) * t)) * I := by
  unfold crrStepCharFun
  rw [mul_comm I (↑(σ * Real.sqrt (T / n) * t)),
      mul_comm I (↑(-(σ * Real.sqrt (T / n)) * t)),
      cexp_ofReal_mul_I, cexp_ofReal_mul_I,
      show (-(σ * Real.sqrt (T / n)) * t) = -(σ * Real.sqrt (T / n) * t) from by ring,
      Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-! ### The two scalar limits feeding the exponent `L` -/

variable {σ T r : ℝ}

/-- For `t ≠ 0`, the rescaled angle `θₙ = σ √(T/n) · t` tends to `0` through
nonzero values — so it can feed the punctured-neighbourhood trig limits. -/
private lemma tendsto_crrAngle_punctured (hσ : 0 < σ) (hT : 0 < T) {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => σ * Real.sqrt (T / n) * t) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h0 : Tendsto (fun n : ℕ => Real.sqrt (T / n)) atTop (𝓝 0) := by
      simpa [crrStep] using tendsto_sqrt_crrStep_zero T
    have h1 : Tendsto (fun n : ℕ => σ * Real.sqrt (T / n) * t) atTop (𝓝 (σ * 0 * t)) :=
      (h0.const_mul σ).mul_const t
    simpa using h1
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have h_sqrt_pos : 0 < Real.sqrt (T / n) := Real.sqrt_pos.mpr (div_pos hT hn_pos)
    exact mul_ne_zero (mul_ne_zero hσ.ne' h_sqrt_pos.ne') ht

/-- **Real part of `n(φₙ−1)`**: `n (cos θₙ − 1) → −½ σ² t² T`, with
`θₙ = σ√(T/n) t`. Uses `n θₙ² = σ² t² T` (exact, `n ≥ 1`) and `(1−cos u)/u² → ½`. -/
private lemma tendsto_n_mul_cos_sub_one (hσ : 0 < σ) (hT : 0 < T) {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => (n : ℝ) * (Real.cos (σ * Real.sqrt (T / n) * t) - 1))
      atTop (𝓝 (-(σ ^ 2 * t ^ 2 * T) / 2)) := by
  have hθ := tendsto_crrAngle_punctured hσ hT ht
  have h_cos : Tendsto (fun n : ℕ =>
      (1 - Real.cos (σ * Real.sqrt (T / n) * t)) / (σ * Real.sqrt (T / n) * t) ^ 2)
      atTop (𝓝 (1 / 2)) := tendsto_one_sub_cos_div_sq.comp hθ
  have h_main : Tendsto (fun n : ℕ =>
      -((1 - Real.cos (σ * Real.sqrt (T / n) * t)) / (σ * Real.sqrt (T / n) * t) ^ 2
        * (σ ^ 2 * t ^ 2 * T)))
      atTop (𝓝 (-(1 / 2 * (σ ^ 2 * t ^ 2 * T)))) := (h_cos.mul_const (σ ^ 2 * t ^ 2 * T)).neg
  rw [show -(1 / 2 * (σ ^ 2 * t ^ 2 * T)) = -(σ ^ 2 * t ^ 2 * T) / 2 from by ring] at h_main
  refine h_main.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
  have h_step_pos : 0 < T / n := div_pos hT hn_pos
  have h_sqrt_sq : Real.sqrt (T / n) ^ 2 = T / n := Real.sq_sqrt h_step_pos.le
  have hθsq : (σ * Real.sqrt (T / n) * t) ^ 2 = σ ^ 2 * (T / n) * t ^ 2 := by
    rw [mul_pow, mul_pow, h_sqrt_sq]
  rw [hθsq]
  field_simp
  ring

/-- **Imaginary part of `n(φₙ−1)`**: `n (2pₙ−1) sin θₙ → (r − σ²/2) T t`, with
`θₙ = σ√(T/n) t`. Feeds `crr_drift_limit_n` and `sin u/u → 1`. -/
private lemma tendsto_n_mul_two_p_sub_one_mul_sin
    (hσ : 0 < σ) (hT : 0 < T) {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ =>
      (n : ℝ) * (2 * crrProb r σ T n - 1) * Real.sin (σ * Real.sqrt (T / n) * t))
      atTop (𝓝 ((r - σ ^ 2 / 2) * T * t)) := by
  have hθ := tendsto_crrAngle_punctured hσ hT ht
  have h_sin : Tendsto (fun n : ℕ =>
      Real.sin (σ * Real.sqrt (T / n) * t) / (σ * Real.sqrt (T / n) * t))
      atTop (𝓝 1) := tendsto_sin_div_one.comp hθ
  have h_dt : Tendsto (fun n : ℕ =>
      (n : ℝ) * (2 * crrProb r σ T n - 1) * σ * Real.sqrt (T / n) * t)
      atTop (𝓝 ((r - σ ^ 2 / 2) * T * t)) := (crr_drift_limit_n (r := r) hσ hT).mul_const t
  have h_prod := h_dt.mul h_sin
  rw [mul_one] at h_prod
  refine h_prod.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_sqrt_pos : 0 < Real.sqrt (T / n) := Real.sqrt_pos.mpr (div_pos hT hn_pos)
  have hθ_ne : σ * Real.sqrt (T / n) * t ≠ 0 :=
    mul_ne_zero (mul_ne_zero hσ.ne' h_sqrt_pos.ne') ht
  field_simp

/-! ### The characteristic-function convergence -/

/-- **CRR → BS characteristic-function convergence.** For `σ, T > 0`, the
characteristic function of the `n`-step CRR risk-neutral log-return,
`crrStepCharFun r σ T n t ^ n`, converges to the Gaussian characteristic
function `exp(i t (r − σ²/2) T − ½ t² σ² T)` — the charFun of
`N((r − σ²/2) T, σ² T)`. This is the distributional heart of the
Cox–Ross–Rubinstein → Black–Scholes convergence theorem.

The increment is real-valued (`±σ√Δt`), so `φₙ = cos θₙ + i (2pₙ−1) sin θₙ`;
`n (φₙ − 1) → L := i t (r−σ²/2)T − ½ t²σ²T` (real and imaginary parts via the
two scalar limits above), and `φₙⁿ = (1 + (φₙ−1))ⁿ → exp L` by Mathlib's
`Complex.tendsto_one_add_pow_exp_of_tendsto`. -/
theorem crr_charFun_pow_tendsto (hσ : 0 < σ) (hT : 0 < T) (t : ℝ) :
    Tendsto (fun n : ℕ => crrStepCharFun r σ T n t ^ n) atTop
      (𝓝 (Complex.exp (I * Complex.ofReal ((r - σ ^ 2 / 2) * T) * Complex.ofReal t
        - Complex.ofReal (σ ^ 2 * T) * Complex.ofReal t ^ 2 / 2))) := by
  rcases eq_or_ne t 0 with rfl | ht
  · -- `t = 0`: `φₙ = 1` and the exponent is `0`, so both sides are the constant `1`.
    have hφ1 : ∀ n : ℕ, crrStepCharFun r σ T n 0 = 1 := by
      intro n; rw [crrStepCharFun_eq]; simp
    have h0 : I * Complex.ofReal ((r - σ ^ 2 / 2) * T) * Complex.ofReal (0 : ℝ)
        - Complex.ofReal (σ ^ 2 * T) * Complex.ofReal (0 : ℝ) ^ 2 / 2 = 0 := by simp
    simp only [hφ1, one_pow, h0, Complex.exp_zero]
    exact tendsto_const_nhds
  · -- `t ≠ 0`: `n (φₙ − 1) → L := i t (r−σ²/2)T − ½ t²σ²T`, then `(1 + (φₙ−1))ⁿ → exp L`.
    have hA := tendsto_n_mul_cos_sub_one hσ hT ht
    have hB := tendsto_n_mul_two_p_sub_one_mul_sin (r := r) hσ hT ht
    have h_ng : Tendsto (fun n : ℕ => (n : ℂ) * (crrStepCharFun r σ T n t - 1)) atTop
        (𝓝 (I * Complex.ofReal ((r - σ ^ 2 / 2) * T) * Complex.ofReal t
          - Complex.ofReal (σ ^ 2 * T) * Complex.ofReal t ^ 2 / 2)) := by
      have h_sum := ((Complex.continuous_ofReal.tendsto _).comp hA).add
        (((Complex.continuous_ofReal.tendsto _).comp hB).mul_const I)
      rw [show (Complex.ofReal (-(σ ^ 2 * t ^ 2 * T) / 2)
            + Complex.ofReal ((r - σ ^ 2 / 2) * T * t) * I)
          = I * Complex.ofReal ((r - σ ^ 2 / 2) * T) * Complex.ofReal t
            - Complex.ofReal (σ ^ 2 * T) * Complex.ofReal t ^ 2 / 2
        from by push_cast; ring] at h_sum
      refine h_sum.congr' (Eventually.of_forall fun n => ?_)
      simp only [Function.comp_apply, crrStepCharFun_eq]
      push_cast [-Complex.ofReal_cos, -Complex.ofReal_sin]
      ring
    have h_pow := Complex.tendsto_one_add_pow_exp_of_tendsto
      (g := fun n => crrStepCharFun r σ T n t - 1) h_ng
    refine h_pow.congr (fun n => ?_)
    show (1 + (crrStepCharFun r σ T n t - 1)) ^ n = crrStepCharFun r σ T n t ^ n
    rw [show (1 : ℂ) + (crrStepCharFun r σ T n t - 1) = crrStepCharFun r σ T n t from by ring]

/-- **CRR → BS, Gaussian-characteristic-function form.** The same limit as
`crr_charFun_pow_tendsto`, with the target written explicitly as the characteristic
function of the Black–Scholes Gaussian `N((r − σ²/2)T, σ²T)`
(`MeasureTheory.charFun (gaussianReal ((r−σ²/2)T) (σ²T))`).

This is the precise hypothesis Lévy's continuity theorem consumes: once the `n`-step
CRR log-return law is identified as the `n`-fold convolution of the step law — whose
characteristic function is `crrStepCharFun`, so the convolution's is `crrStepCharFun ^ n`
(`MeasureTheory.charFun_conv`) — `ProbabilityMeasure.tendsto_iff_tendsto_charFun`
upgrades this pointwise charFun convergence to convergence in distribution, i.e. the
CRR risk-neutral log-return converges in law to the Black–Scholes normal. -/
theorem crr_charFun_pow_tendsto_gaussian (hσ : 0 < σ) (hT : 0 < T) (t : ℝ) :
    Tendsto (fun n : ℕ => crrStepCharFun r σ T n t ^ n) atTop
      (𝓝 (MeasureTheory.charFun
        (ProbabilityTheory.gaussianReal ((r - σ ^ 2 / 2) * T) (σ ^ 2 * T).toNNReal) t)) := by
  have hgauss : MeasureTheory.charFun
      (ProbabilityTheory.gaussianReal ((r - σ ^ 2 / 2) * T) (σ ^ 2 * T).toNNReal) t
      = Complex.exp (I * Complex.ofReal ((r - σ ^ 2 / 2) * T) * Complex.ofReal t
        - Complex.ofReal (σ ^ 2 * T) * Complex.ofReal t ^ 2 / 2) := by
    rw [ProbabilityTheory.charFun_gaussianReal,
        Real.coe_toNNReal (σ ^ 2 * T) (mul_nonneg (sq_nonneg σ) hT.le)]
    congr 1
    push_cast
    ring
  rw [hgauss]
  exact crr_charFun_pow_tendsto hσ hT t

/-! ### Convergence in distribution to the Black–Scholes Gaussian -/

section Distributional

open MeasureTheory ProbabilityTheory

/-- `n`-fold additive convolution of `ν` with itself: `convPow ν 0 = δ₀`,
`convPow ν (n+1) = convPow ν n ∗ ν`. This is the law of `∑_{k < n} Xₖ` for
`Xₖ` i.i.d. `∼ ν` — in particular the law of an `n`-step sum of i.i.d. increments. -/
noncomputable def convPow (ν : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => convPow ν n ∗ ν

/-- A convolution power of a probability measure is a probability measure. -/
lemma convPow_isProbabilityMeasure (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∀ n, IsProbabilityMeasure (convPow ν n)
  | 0 => by unfold convPow; infer_instance
  | n + 1 => by
    unfold convPow
    haveI := convPow_isProbabilityMeasure ν n
    infer_instance

/-- **The characteristic function of an `n`-fold convolution is the `n`-th power**
of the characteristic function — the measure-level statement that the charFun of a
sum of `n` i.i.d. variables is `(charFun)ⁿ`. -/
lemma charFun_convPow (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (t : ℝ) :
    charFun (convPow ν n) t = (charFun ν t) ^ n := by
  induction n with
  | zero => simp [convPow, charFun_dirac]
  | succ k ih =>
    haveI := convPow_isProbabilityMeasure ν k
    rw [convPow, charFun_conv, ih, pow_succ]

/-- The law of one CRR risk-neutral log-return increment: mass `pₙ` at the up-move
`+σ√Δt` and `1−pₙ` at the down-move `−σ√Δt` (`pₙ = crrProb`, `Δt = T/n`). -/
noncomputable def crrStepMeasure (r σ T : ℝ) (n : ℕ) : Measure ℝ :=
  ENNReal.ofReal (crrProb r σ T n) • Measure.dirac (σ * Real.sqrt (T / n))
    + ENNReal.ofReal (1 - crrProb r σ T n) • Measure.dirac (-(σ * Real.sqrt (T / n)))

/-- `crrStepMeasure` is a probability measure exactly when the step is arbitrage-free
(`0 ≤ pₙ ≤ 1`). -/
lemma isProbabilityMeasure_crrStepMeasure {r σ T : ℝ} {n : ℕ}
    (hp0 : 0 ≤ crrProb r σ T n) (hp1 : crrProb r σ T n ≤ 1) :
    IsProbabilityMeasure (crrStepMeasure r σ T n) := by
  refine ⟨?_⟩
  unfold crrStepMeasure
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_add hp0 (by linarith), show crrProb r σ T n + (1 - crrProb r σ T n) = 1
    from by ring, ENNReal.ofReal_one]

/-- **`crrStepCharFun` is the characteristic function of `crrStepMeasure`** (the
actual CRR per-step log-return law), under no-arbitrage `0 ≤ pₙ ≤ 1`. -/
lemma charFun_crrStepMeasure {r σ T : ℝ} {n : ℕ} (t : ℝ)
    (hp0 : 0 ≤ crrProb r σ T n) (hp1 : crrProb r σ T n ≤ 1) :
    charFun (crrStepMeasure r σ T n) t = crrStepCharFun r σ T n t := by
  unfold crrStepMeasure
  rw [charFun_apply,
      integral_add_measure ((integrable_dirac (by finiteness)).smul_measure (by finiteness))
        ((integrable_dirac (by finiteness)).smul_measure (by finiteness)),
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
      ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith)]
  unfold crrStepCharFun
  simp only [RCLike.inner_apply', conj_trivial, Complex.real_smul, mul_comm Complex.I]
  push_cast
  ring

/-- The `n`-step CRR risk-neutral log-return law (the `n`-fold convolution of the
per-step law), bundled as a `ProbabilityMeasure` — needs no-arbitrage `0 ≤ pₙ ≤ 1`. -/
noncomputable def crrRowProbMeasure (r σ T : ℝ) (n : ℕ)
    (h0 : 0 ≤ crrProb r σ T n) (h1 : crrProb r σ T n ≤ 1) : ProbabilityMeasure ℝ :=
  haveI := isProbabilityMeasure_crrStepMeasure h0 h1
  haveI := convPow_isProbabilityMeasure (crrStepMeasure r σ T n) n
  ⟨convPow (crrStepMeasure r σ T n) n, inferInstance⟩

/-- The Black–Scholes limiting normal `N((r−σ²/2)T, σ²T)`, bundled as a
`ProbabilityMeasure`. -/
noncomputable def bsLimitProbMeasure (r σ T : ℝ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal ((r - σ ^ 2 / 2) * T) (σ ^ 2 * T).toNNReal, inferInstance⟩

/-- **Cox–Ross–Rubinstein → Black–Scholes, convergence in distribution.** Under
no-arbitrage at every step (`0 ≤ pₙ ≤ 1`), the law of the `n`-step CRR risk-neutral
log-return converges weakly to the Black–Scholes normal `N((r − σ²/2)T, σ²T)`.

This is the genuine distributional CLT for the binomial tree: the charFun-power
convergence `crr_charFun_pow_tendsto_gaussian` is upgraded to weak convergence of
probability measures by Lévy's continuity theorem
(`ProbabilityMeasure.tendsto_of_tendsto_charFun`), using
`charFun (convPow ν n) = (charFun ν)ⁿ` and `charFun (crrStepMeasure) = crrStepCharFun`. -/
theorem crr_tendsto_gaussian_inDistribution {r σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T)
    (hp : ∀ n, 0 ≤ crrProb r σ T n ∧ crrProb r σ T n ≤ 1) :
    Tendsto (fun n : ℕ => crrRowProbMeasure r σ T n (hp n).1 (hp n).2) atTop
      (𝓝 (bsLimitProbMeasure r σ T)) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun (fun t => ?_)
  have heq : (fun n : ℕ => charFun (convPow (crrStepMeasure r σ T n) n) t)
      = (fun n => crrStepCharFun r σ T n t ^ n) := by
    funext n
    haveI := isProbabilityMeasure_crrStepMeasure (hp n).1 (hp n).2
    rw [charFun_convPow, charFun_crrStepMeasure t (hp n).1 (hp n).2]
  show Tendsto (fun n : ℕ => charFun (convPow (crrStepMeasure r σ T n) n) t) atTop
    (𝓝 (charFun (gaussianReal ((r - σ ^ 2 / 2) * T) (σ ^ 2 * T).toNNReal) t))
  rw [heq]
  exact crr_charFun_pow_tendsto_gaussian hσ hT t

/-! ### CRR → BS price convergence (`binomialPrice → bs_call_price`) -/

/-- A bounded measurable payoff composed with `x ↦ a·eˣ` is integrable against any
finite measure. -/
lemma integrable_comp_exp_of_bdd {μ : Measure ℝ} [IsFiniteMeasure μ] {g : ℝ → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) (a : ℝ) :
    Integrable (fun x => g (a * Real.exp x)) μ :=
  Integrable.of_bound ((hg.comp (by fun_prop)).aestronglyMeasurable) C
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC _)

/-- **Two-point integral against the CRR step law** (real-valued): for any `h`,
`∫ h ∂(crrStepMeasure) = pₙ·h(σ√Δt) + (1−pₙ)·h(−σ√Δt)` under no-arbitrage `0 ≤ pₙ ≤ 1`. -/
lemma integral_crrStepMeasure {r σ T : ℝ} {n : ℕ}
    (hp0 : 0 ≤ crrProb r σ T n) (hp1 : crrProb r σ T n ≤ 1) (h : ℝ → ℝ) :
    ∫ z, h z ∂(crrStepMeasure r σ T n)
      = crrProb r σ T n * h (σ * Real.sqrt (T / n))
        + (1 - crrProb r σ T n) * h (-(σ * Real.sqrt (T / n))) := by
  unfold crrStepMeasure
  rw [integral_add_measure ((integrable_dirac (by finiteness)).smul_measure (by finiteness))
        ((integrable_dirac (by finiteness)).smul_measure (by finiteness)),
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
      ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith)]
  simp [smul_eq_mul]

/-- **The binomial price is the discounted risk-neutral expectation** (the bridge from
the backward-recursion pricer to the probabilistic row-law form). For a bounded
measurable payoff `g`, the `k`-step CRR binomial price of `g` equals `e^{−r'k}` times
the expectation of `g(S·eˣ)` over the `k`-fold convolution of the per-step log-return
law (`r' = crrPerStepRate`). Proof: induction on `k`, the recursion step matched to one
convolution via `integral_conv` + the two-point step integral. -/
lemma binomialPrice_eq_integral_convPow {r σ T : ℝ} {n : ℕ}
    (hp0 : 0 ≤ crrProb r σ T n) (hp1 : crrProb r σ T n ≤ 1)
    {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) (k : ℕ) (S : ℝ) :
    binomialPrice (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n) g k S
      = Real.exp (-(crrPerStepRate r T n) * k) *
        ∫ x, g (S * Real.exp x) ∂(convPow (crrStepMeasure r σ T n) k) := by
  haveI : IsProbabilityMeasure (crrStepMeasure r σ T n) :=
    isProbabilityMeasure_crrStepMeasure hp0 hp1
  induction k generalizing S with
  | zero =>
    simp only [binomialPrice_zero, Nat.cast_zero, mul_zero, Real.exp_zero, one_mul,
      convPow, integral_dirac, mul_one]
  | succ k ih =>
    haveI : IsProbabilityMeasure (convPow (crrStepMeasure r σ T n) k) :=
      convPow_isProbabilityMeasure _ k
    have hprob : crrUpProb (crrUp σ T n) (crrDown σ T n) (crrPerStepRate r T n)
        = crrProb r σ T n := rfl
    have hinner : ∀ x : ℝ, (∫ z, g (S * Real.exp (x + z)) ∂(crrStepMeasure r σ T n))
        = crrProb r σ T n * g (S * crrUp σ T n * Real.exp x)
          + (1 - crrProb r σ T n) * g (S * crrDown σ T n * Real.exp x) := by
      intro x
      rw [integral_crrStepMeasure hp0 hp1 (fun z => g (S * Real.exp (x + z))),
          show S * Real.exp (x + σ * Real.sqrt (T / n)) = S * crrUp σ T n * Real.exp x from by
            rw [Real.exp_add, crrUp, crrStep]; ring,
          show S * Real.exp (x + -(σ * Real.sqrt (T / n))) = S * crrDown σ T n * Real.exp x from by
            rw [Real.exp_add, crrDown, crrStep]; ring]
    rw [binomialPrice_succ, hprob, ih (S * crrUp σ T n), ih (S * crrDown σ T n), convPow,
        integral_conv (integrable_comp_exp_of_bdd hg hC S)]
    simp_rw [hinner]
    rw [integral_add ((integrable_comp_exp_of_bdd hg hC _).const_mul _)
          ((integrable_comp_exp_of_bdd hg hC _).const_mul _),
        integral_const_mul, integral_const_mul]
    have hexp : Real.exp (-(crrPerStepRate r T n) * (↑(k + 1) : ℝ))
        = Real.exp (-(crrPerStepRate r T n)) * Real.exp (-(crrPerStepRate r T n) * (k : ℝ)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [hexp]
    ring

/-- **Put-call parity at the binomial level**: `call = put + (S − K·e^{−nr})`, from
linearity of `binomialPrice` plus the stock-price (`binomialPrice_id`) and constant
(`binomialPrice_const`) values. -/
lemma binomialPrice_callPut_parity {u d r K : ℝ} (h : BinomialNoArb u d r) (n : ℕ) (S : ℝ) :
    binomialPrice u d r (fun x => max (x - K) 0) n S
      = binomialPrice u d r (fun x => max (K - x) 0) n S
        + (S - K * Real.exp (-(n : ℝ) * r)) := by
  have hpay : (fun x : ℝ => max (x - K) 0) = (fun x => max (K - x) 0 + (x - K)) := by
    funext x
    rcases le_total x K with hx | hx
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  rw [hpay,
      show (fun x : ℝ => max (K - x) 0 + (x - K))
        = (fun x => (fun y => max (K - y) 0) x + (fun y => y - K) x) from rfl,
      binomialPrice_add,
      show (fun y : ℝ => y - K) = (fun x => (fun y : ℝ => y) x + (fun _ => -K) x) from by
        funext x; ring,
      binomialPrice_add, binomialPrice_id u d r h, binomialPrice_const u d r (-K) h]
  ring

/-- **Stock-price MGF under the BS Gaussian**: `∫ S₀·eˣ d N((r−σ²/2)T, σ²T) = S₀·e^{rT}`
(the martingale/forward identity for the discounted stock). -/
lemma integral_const_mul_exp_gaussian {r σ T S₀ : ℝ} (hT : 0 < T) :
    ∫ x, S₀ * Real.exp x ∂(gaussianReal ((r - σ ^ 2 / 2) * T) (σ ^ 2 * T).toNNReal)
      = S₀ * Real.exp (r * T) := by
  rw [integral_const_mul]
  have hmgf := congr_fun (mgf_id_gaussianReal (μ := (r - σ ^ 2 / 2) * T)
    (v := (σ ^ 2 * T).toNNReal)) 1
  rw [mgf] at hmgf
  simp only [one_mul, id_eq] at hmgf
  rw [hmgf,
      show ((σ ^ 2 * T).toNNReal : ℝ) = σ ^ 2 * T from
        Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) hT.le),
      show (r - σ ^ 2 / 2) * T * 1 + σ ^ 2 * T * 1 ^ 2 / 2 = r * T from by ring]

end Distributional

end QuantFin
