/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- `import Mathlib` comes transitively through `ItoLemma`; this file's surface
-- needs only the `Real.exp` chain rule + `Finset` sum lemmas it already pulls.
import MathFin.Foundations.ItoLemma

/-! # Itô's lemma for `f(t, x)` — time-dependent (2D), items 4 & 5

The classical Itô formula for a `C^{1,2}` function `f(t, x)` of time and a
diffusion `X_t` with `dX_t = μ_X dt + σ_X dB_t`:

  `df(t, X_t) = [∂_t f + μ_X · ∂_x f + ½ σ_X² · ∂_xx f] dt + σ_X · ∂_x f dB_t`.

This file gives:

* **Item 4** — the *pathwise discrete* 2D Itô formula
  (`discrete_ito_formula_2d`): an exact-by-construction telescoping
  identity for `f(t_N, X_N) − f(t_0, X_0)`, with a 2D Taylor remainder
  (`discreteTaylorRemainder2D`) absorbing the higher-order time/mixed
  terms. Mirrors the 1D `discrete_ito_formula` (`DiscreteIto.lean`), now
  carrying the `∂_t f · Δt` term. The 2D drift coefficient `itoDrift2D`.

* **Item 5** — **geometric Brownian motion solves the GBM SDE**
  (`gbm_solves_sde`, `gbm_diffusion`). For the exp value function
  `S(t, x) = S₀ · exp((μ − ½σ²) t + σ x)`, the *genuine partial
  derivatives* (`hasDerivAt_gbmValue_time`, `_space`, `_space_space`,
  proved from `Real.exp` chain rule) plug into `itoDrift2D` with the
  Brownian generator `(μ_X, σ_X) = (0, 1)` to give Itô drift `μ · S` and
  diffusion `σ · S` — i.e., `S_t = S(t, B_t)` satisfies
  `dS_t = μ S_t dt + σ S_t dB_t`. The famous `−½σ²` in the exponent is
  exactly the Itô correction that makes the drift `μ` (not `μ + ½σ²`).

The continuous-time L² statement (dropping the remainder in the partition
limit via the third-moment bound) is deferred; the discrete identity +
the GBM partials are the algebraic and analytic content that the limit
argument consumes.
-/

namespace MathFin

open scoped NNReal

/-! ## Item 4 — the discrete 2D Itô formula -/

/-- **2D discrete Taylor remainder** over a step from `(tk, Xk)` to
`(tk1, Xk1)`: the deviation of `f(tk1, Xk1) − f(tk, Xk)` from its
first-order-in-time, second-order-in-space Taylor expansion around
`(tk, Xk)`. *Defined* so the 2D discrete Itô formula is a definitional
identity:

  `R := f(tk1, Xk1) − f(tk, Xk) − f_t·Δt − f_x·ΔX − ½ f_xx·ΔX²`.

The substantive content is the *bound* on `R` under `f ∈ C^{1,2}` plus
the Brownian third-moment estimate (`|ΔX|³` and `Δt·|ΔX|` are both
`o(Δt)` in sum), which governs the continuous limit and is deferred. -/
noncomputable def discreteTaylorRemainder2D
    (f f_t f_x f_xx : ℝ → ℝ → ℝ) (tk tk1 Xk Xk1 : ℝ) : ℝ :=
  f tk1 Xk1 - f tk Xk
    - f_t tk Xk * (tk1 - tk)
    - f_x tk Xk * (Xk1 - Xk)
    - (1 / 2) * (f_xx tk Xk * (Xk1 - Xk) ^ 2)

/-- **Discrete 2D Itô formula** (time + space). For any time grid `t : ℕ → ℝ`,
space path `X : ℕ → ℝ`, and formal partials `f_t, f_x, f_xx`,

  `f(t_N, X_N) − f(t_0, X_0)
     = ∑ f_t(t_k,X_k)·Δt_k
       + ∑ f_x(t_k,X_k)·ΔX_k
       + ½ ∑ f_xx(t_k,X_k)·(ΔX_k)²
       + ∑ R_k`,

where `R_k = discreteTaylorRemainder2D …`. Proof: telescoping
`f(t_N,X_N) − f(t_0,X_0) = ∑ (f(t_{k+1},X_{k+1}) − f(t_k,X_k))` via
`Finset.sum_range_sub`, then substituting the definition of `R_k` into
each summand. No probabilistic content; the time-drift term `∑ f_t·Δt`
joins the 1D Itô structure purely algebraically. -/
theorem discrete_ito_formula_2d
    (N : ℕ) (t X : ℕ → ℝ) (f f_t f_x f_xx : ℝ → ℝ → ℝ) :
    f (t N) (X N) - f (t 0) (X 0) =
      (∑ k ∈ Finset.range N, f_t (t k) (X k) * (t (k + 1) - t k)) +
      (∑ k ∈ Finset.range N, f_x (t k) (X k) * (X (k + 1) - X k)) +
      (1 / 2) *
        (∑ k ∈ Finset.range N, f_xx (t k) (X k) * (X (k + 1) - X k) ^ 2) +
      ∑ k ∈ Finset.range N,
        discreteTaylorRemainder2D f f_t f_x f_xx (t k) (t (k + 1)) (X k) (X (k + 1)) := by
  -- Telescoping.
  have h_tele : f (t N) (X N) - f (t 0) (X 0) =
      ∑ k ∈ Finset.range N, (f (t (k + 1)) (X (k + 1)) - f (t k) (X k)) :=
    (Finset.sum_range_sub (fun n => f (t n) (X n)) N).symm
  rw [h_tele]
  -- Per-summand 2D Taylor decomposition (definitional).
  have h_summand : ∀ k,
      f (t (k + 1)) (X (k + 1)) - f (t k) (X k) =
        f_t (t k) (X k) * (t (k + 1) - t k) +
        f_x (t k) (X k) * (X (k + 1) - X k) +
        (1 / 2) * (f_xx (t k) (X k) * (X (k + 1) - X k) ^ 2) +
        discreteTaylorRemainder2D f f_t f_x f_xx (t k) (t (k + 1)) (X k) (X (k + 1)) := by
    intro k
    unfold discreteTaylorRemainder2D
    ring
  rw [Finset.sum_congr rfl (fun k _ => h_summand k)]
  -- Distribute the four-term sum and pull the (1/2) constant out.
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]

/-- **2D Itô drift coefficient** of `f(t, X_t)` for `X_t` with local drift
`μ_X` and local volatility `σ_X`:

  `itoDrift2D f_t f_x f_xx μ_X σ_X := f_t + μ_X · f_x + ½ σ_X² · f_xx`.

This is the per-time-unit `dt` coefficient in
`df(t, X_t) = itoDrift2D … dt + σ_X · f_x dB_t`. The `f_t` summand is
the new time-dependent term over the 1D `itoDrift`. -/
noncomputable def itoDrift2D (f_t f_x f_xx μ_X σ_X : ℝ) : ℝ :=
  f_t + μ_X * f_x + (1 / 2) * σ_X ^ 2 * f_xx

/-- With no time dependence (`f_t = 0`), `itoDrift2D` collapses to the 1D
`itoDrift`. The two layers agree where they overlap. -/
lemma itoDrift2D_no_time (f_x f_xx μ_X σ_X : ℝ) :
    itoDrift2D 0 f_x f_xx μ_X σ_X = itoDrift f_x f_xx μ_X σ_X := by
  unfold itoDrift2D itoDrift
  ring

/-! ## Item 5 — geometric Brownian motion solves the GBM SDE

`S(t, x) := S₀ · exp((μ − ½σ²) t + σ x)`. With `X_t = B_t` (so `μ_X = 0`,
`σ_X = 1`), the Itô drift of `S(t, B_t)` is `μ · S` and the diffusion is
`σ · S`: i.e. `S_t := S(t, B_t)` solves `dS_t = μ S_t dt + σ S_t dB_t`. -/

/-- **GBM exponential value function** `S(t, x) = S₀ · exp((μ − ½σ²) t + σ x)`.
Evaluated at `x = B_t`, this is geometric Brownian motion. -/
noncomputable def gbmValue (S₀ μ σ t x : ℝ) : ℝ :=
  S₀ * Real.exp ((μ - σ ^ 2 / 2) * t + σ * x)

/-- **Space partial** `∂_x S = σ · S` — genuine `HasDerivAt`, via the
`Real.exp` chain rule on the affine exponent. -/
lemma hasDerivAt_gbmValue_space (S₀ μ σ t x : ℝ) :
    HasDerivAt (fun y => gbmValue S₀ μ σ t y) (σ * gbmValue S₀ μ σ t x) x := by
  -- inner exponent `y ↦ (μ − ½σ²) t + σ y` has derivative `σ`
  have h_lin : HasDerivAt (fun y => (μ - σ ^ 2 / 2) * t + σ * y) σ x := by
    simpa using ((hasDerivAt_id x).const_mul σ).const_add ((μ - σ ^ 2 / 2) * t)
  have h_exp := h_lin.exp
  have h := h_exp.const_mul S₀
  -- `h : HasDerivAt (fun y => S₀ * exp(...)) (S₀ * (exp(...) * σ)) x`
  unfold gbmValue
  convert h using 1
  ring

/-- **Time partial** `∂_t S = (μ − ½σ²) · S` — genuine `HasDerivAt`. -/
lemma hasDerivAt_gbmValue_time (S₀ μ σ t x : ℝ) :
    HasDerivAt (fun s => gbmValue S₀ μ σ s x)
      ((μ - σ ^ 2 / 2) * gbmValue S₀ μ σ t x) t := by
  have h_lin : HasDerivAt (fun s => (μ - σ ^ 2 / 2) * s + σ * x) (μ - σ ^ 2 / 2) t := by
    simpa using ((hasDerivAt_id t).const_mul (μ - σ ^ 2 / 2)).add_const (σ * x)
  have h := (h_lin.exp).const_mul S₀
  unfold gbmValue
  convert h using 1
  ring

/-- **Second space partial** `∂_xx S = σ² · S` — the derivative of
`∂_x S = σ · S` is `σ · (σ · S) = σ² · S`. -/
lemma hasDerivAt_gbmValue_space_space (S₀ μ σ t x : ℝ) :
    HasDerivAt (fun y => σ * gbmValue S₀ μ σ t y)
      (σ ^ 2 * gbmValue S₀ μ σ t x) x := by
  have h := (hasDerivAt_gbmValue_space S₀ μ σ t x).const_mul σ
  convert h using 1
  ring

/-- **Geometric Brownian motion solves the GBM SDE (drift + diffusion).** The
partials enter as `HasDerivAt` hypotheses — so by `HasDerivAt.unique` they are
*forced* to be the genuine derivatives of `gbmValue` (`∂_t = (μ−½σ²)S`,
`∂_x = σS`, `∂_xx = σ²S`), not free parameters a caller could fake. Under the
Brownian generator `(μ_X, σ_X) = (0, 1)`, the 2D Itô drift of `f(t, B_t)` is

  `(μ − ½σ²) S + 0 · σS + ½ · 1² · σ²S = μ S`,

and the diffusion coefficient `σ_X · ∂_x S = σ S`. Reading both off:
`S_t := S(t, B_t)` matches `dS_t = μ S_t dt + σ S_t dB_t` at the level of Itô
coefficients (the coefficient-matching the continuous Itô lemma turns into a
genuine SDE solution; that limit step is deferred — see module header).

The `−½σ²` carried in the exponent cancels the `+½σ²` of the Itô second-order
term — this cancellation *is* the Itô correction, and the reason a GBM with
exponent drift `μ − ½σ²` has physical drift rate `μ`. -/
theorem gbm_solves_sde (S₀ μ σ t x : ℝ) {f_t f_x f_xx : ℝ}
    (h_t : HasDerivAt (fun s => gbmValue S₀ μ σ s x) f_t t)
    (h_x : HasDerivAt (fun y => gbmValue S₀ μ σ t y) f_x x)
    (h_xx : HasDerivAt (fun y => σ * gbmValue S₀ μ σ t y) f_xx x) :
    itoDrift2D f_t f_x f_xx 0 1 = μ * gbmValue S₀ μ σ t x
      ∧ (1 : ℝ) * f_x = σ * gbmValue S₀ μ σ t x := by
  -- The `HasDerivAt` hypotheses pin the partials to their computed values.
  obtain rfl := h_t.unique (hasDerivAt_gbmValue_time S₀ μ σ t x)
  obtain rfl := h_x.unique (hasDerivAt_gbmValue_space S₀ μ σ t x)
  obtain rfl := h_xx.unique (hasDerivAt_gbmValue_space_space S₀ μ σ t x)
  refine ⟨?_, ?_⟩
  · unfold itoDrift2D; ring
  · ring

/-- **Sanity check via the 1D `itoDrift_log_gbm`**: the GBM drift identity
is consistent with the log-price drift `μ − ½σ²` (`ItoLemma.itoDrift_log_gbm`).
Here we see the *forward* direction — the exp-form recovers physical drift
`μ` — as the inverse of the log-form's `μ − ½σ²`. -/
lemma gbm_drift_inverts_log (μ σ S : ℝ) (hS : S ≠ 0) :
    itoDrift (1 / S) (-1 / S ^ 2) (μ * S) (σ * S) + σ ^ 2 / 2 = μ := by
  rw [itoDrift_log_gbm μ σ S hS]
  ring

end MathFin
