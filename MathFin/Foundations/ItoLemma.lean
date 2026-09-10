/-
This file builds on the **discrete Itô formula** (`Foundations/DiscreteIto.lean`,
phase 35, adapted from Nagy 2026) to give the *structural drift formula*
for `f(X_t)` when `X_t` is an Itô process. The full L²-limit Itô lemma
requires the Taylor-remainder bound + simple-process density argument,
which is gated on Mathlib's Itô-integral completeness (currently
incomplete; see `docs/bridges.md`).

The structural drift formula — `μ_X · f' + (1/2) σ_X² · f''` — is the
*per-unit-time* coefficient of `dt` in `df(X_t)` and is everything you
need for the canonical applications (GBM log-drift, BS PDE derivation).
It is also what Nagy uses downstream (his §5).

Adapted from Theorem 5.1 ("Itô's Lemma") and Theorem 5.2 ("GBM Drift") of:

  Tamás Nagy, "From Itô to Black–Scholes: A Machine-Verified Derivation in
  Lean 4", SSRN Working Paper 6336503, March 2026.
  <https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6336503>

Author of this MathFin Lean 4 adaptation: Raphael Coelho.
Original Lean derivation: Tamás Nagy (SSRN 6336503, 2026).
Copyright (c) 2026 Raphael Coelho (this adaptation).
Mathematical content and original Lean code © Tamás Nagy 2026, used here
under academic fair use for derivative work with attribution.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import MathFin.Foundations.DiscreteIto

/-!
# Itô's lemma structural drift formula (phase 39, after Nagy 2026)

For an Itô process `dX_t = μ_X dt + σ_X dB_t` and a `C²` function `f`,
Itô's lemma gives

  `df(X_t) = f'(X_t) dX_t + (1/2) f''(X_t) σ_X² dt
          = [μ_X · f'(X_t) + (1/2) · σ_X² · f''(X_t)] dt + σ_X · f'(X_t) dB_t`.

The **drift coefficient** of `df` is therefore `μ_X · f' + (1/2) · σ_X² · f''`,
a purely algebraic per-time-unit formula independent of the Brownian
motion `B`. This file formalises this drift coefficient as `itoDrift` and
proves the canonical specialisations:

* `itoDrift_id`: with `f = id`, drift is just `μ_X` (identity preservation).
* `itoDrift_log_gbm` (after Nagy Theorem 5.2): with `f = log`, `X = S`,
  and `μ_X = μ S`, `σ_X = σ S` (geometric BM), drift is `μ − σ²/2`.

These are the structural identities used downstream (BS PDE via Itô,
variance-swap log payoff, etc.).

## What this file is *not*

This is the **drift coefficient identity**, not the full Itô-lemma
integral identity `f(X_T) − f(X_0) = ∫ f' dX + (1/2) ∫ f'' σ_X² dt`. The
integral identity follows from `Foundations/DiscreteIto.lean` (phase 35)
plus a limit argument bounding the Taylor remainder (Nagy §5, marked
†, structurally verified). The full L²-limit construction is gated on
Mathlib's complete Itô-integral pipeline; see `docs/bridges.md`.

The drift formula here is *all that is needed* for the downstream
applications in this library (GBM drift derivation, BS PDE, log-payoff
variance swap).
-/

@[expose] public section

namespace MathFin

/-- **Itô drift coefficient**: for `f` `C²` and `X_t` an Itô process with
local drift `μ_X` and local volatility `σ_X`, the drift coefficient of
`f(X_t)` under Itô's lemma is

  `itoDrift f' f'' μ_X σ_X := μ_X · f' + (1/2) · σ_X² · f''`.

This is the per-time-unit `dt` coefficient in `df(X_t) = itoDrift … dt
+ σ_X · f'(X_t) dB_t`. Definition matches Nagy 2026 §5 (the `ito_drift`
abbreviation). -/
noncomputable def itoDrift (f' f'' μ_X σ_X : ℝ) : ℝ :=
  μ_X * f' + (1 / 2) * σ_X ^ 2 * f''

/-- **Sanity check: identity function**. With `f = id` (so `f' = 1`,
`f'' = 0`), the Itô drift collapses to the underlying process's local
drift `μ_X`. -/
lemma itoDrift_id (μ_X σ_X : ℝ) :
    itoDrift 1 0 μ_X σ_X = μ_X := by
  unfold itoDrift
  ring

/-- **GBM log-drift** (Nagy 2026, Theorem 5.2). For geometric Brownian
motion `dS_t = μ S_t dt + σ S_t dB_t` and `f = log`, so `f'(S) = 1/S` and
`f''(S) = −1/S²`, the Itô drift of `log S_t` is

  `μ S · (1/S) + (1/2) · (σ S)² · (−1/S²) = μ − σ²/2`.

This is the celebrated `−σ²/2` Itô correction that distinguishes
stochastic from ordinary calculus, and the reason BS uses `r − σ²/2` in
the `d_2` argument (vs `r + σ²/2` for `d_1`). -/
theorem itoDrift_log_gbm (μ σ S : ℝ) (hS : S ≠ 0) :
    itoDrift (1 / S) (-1 / S ^ 2) (μ * S) (σ * S) = μ - σ ^ 2 / 2 := by
  unfold itoDrift
  field_simp
  ring

/-- The scalar identity `σ·S·(1/S) = σ` for `S ≠ 0`. Named for the step it marks in the
GBM log-price computation — the `dB_t` coefficient of `d(log S_t)` is `σ_X · f'(X)`, which
at `σ_X = σS`, `f' = 1/S` is the constant `σ`. The statement itself is only the algebra;
the process content lives in `itoDrift_log_gbm` and the Itô-formula layer. -/
lemma gbm_log_volatility (σ S : ℝ) (hS : S ≠ 0) :
    σ * S * (1 / S) = σ := by
  field_simp

end MathFin
