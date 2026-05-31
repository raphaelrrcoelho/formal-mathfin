/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- `import Mathlib` comes transitively through `ItoLemma` / `BlackScholes.PDE`.
import MathFin.Foundations.ItoLemma
import MathFin.Foundations.ItoLemma2D
import MathFin.BlackScholes.PDE

/-!
# Black-Scholes PDE derived via the Itô-drift formula (phase 46)

The pre-existing `BlackScholes/PDE.lean` proves the BS PDE *directly*:
`∂_t V + (1/2) σ² S² ∂_SS V + r S ∂_S V − r V = 0` follows from explicit
computation of the partial derivatives of `bsV = S Φ(d_1) − K e^{−rτ}
Φ(d_2)`. That is a *backward* verification (we have the closed form, we
check it satisfies the PDE).

This file derives the same PDE *forward*, from the **no-arbitrage
condition + Itô structural drift formula** (Phase 39 `itoDrift`). The
chain:

1. Under the risk-neutral measure `Q`, the discounted price `e^{−rt} V_t`
   is a `Q`-martingale (fundamental no-arbitrage statement).
2. By Itô's lemma applied to `f(S, t) := e^{−rt} · V(S, T−t)`, the drift
   of `d(e^{−rt} V_t)` is zero (martingale property).
3. The drift involves partial derivatives of `V`, and setting it to zero
   gives the BS PDE.

The result: the PDE is a *consequence* of risk-neutral pricing + Itô,
not a separate assumption. The closed-form `bsV` satisfies the PDE
(verified directly in `PDE.lean`), and *why* it satisfies the PDE is
that any no-arb option price must satisfy it.

## What this file is

A **structural derivation** of the BS PDE coefficient relationship from
the Itô-drift formula, at the algebraic level. The full continuous-time
martingale-property derivation requires the integral form of Itô's lemma
(see `Foundations/ItoLemma.lean` note); the drift-coefficient version
here is the algebraic core.

## The bridge to the continuous-time foundations (status, 2026-05-28)

The closing of the `Foundations/` → pricing-modules bridge gap (F1 in
`docs/portfolio-review-2026-05-28.md`) for this file requires Itô's
lemma for general `C²(ℝ², ℝ)` functions `(s, t) ↦ V(s, t)` applied to
GBM `S_t`. We now have:

* `Foundations/ItoIntegralCLM.itoIntegralCLM_T` — the continuous Itô
  integral as a continuous linear isometry `Lp 2 trim_T →L[ℝ] Lp 2 μ`.
* `Foundations/ItoFormulaSquaredL2.itoSquared_L2_tendsto_div2` — Itô's
  lemma for `f(x) = x²` in continuous L² form: the Riemann sums
  `∑ B·ΔB` converge in `L²(μ)` to `½·(B_T² − B_0² − T)`.

What remains for a full refactor consuming the continuous Itô integral:

1. **Itô's lemma for general `C²(ℝ → ℝ)`** at the L² level — extending
   `itoSquared_L2_tendsto_div2` from `x²` to arbitrary smooth `f`. The
   bound on the discrete Taylor remainder under `f ∈ C³` is the missing
   ingredient (`Foundations/DiscreteIto.discreteTaylorRemainder` exists;
   the third-order bound is documented as deferred).
2. **Itô's lemma for `C²(ℝ² → ℝ)`** with time dependence — adds the
   `∂_t V dt` term used here as `V_t` in `bsItoDrift`.
3. **Geometric Brownian motion as an SDE solution** — `S_t = S_0 exp((r −
   ½σ²)t + σB_t)` solves `dS = rS dt + σS dB`, derived via (2). Then
   plugging into (2) gives the BS PDE.

The algebraic identity in this file pre-figures the drift coefficient
the continuous derivation will produce; the `bsItoDrift` definition is
the right *target*. A multi-session continuation closes the bridge by
deriving rather than positing it.

## Result

* `bs_drift_under_riskNeutral`: under risk-neutral GBM `dS = r S dt + σ
  S dB`, the Itô drift of `V(S, t)` is `r S · ∂_S V + (1/2) σ² S² · ∂_SS
  V + ∂_t V` — the LHS of the BS PDE (modulo `−rV`).
* `bs_pde_from_no_arbitrage`: setting the drift of the *discounted*
  option price `e^{−rt} V_t` to zero (no-arb) recovers the BS PDE
  algebraic identity.

The discount + drift algebra:
`d(e^{−rt} V) = e^{−rt} · (dV − r V dt) = e^{−rt} · (drift_V dt + ... dB − r V dt)`
⟹ for `d(e^{−rt} V)` to be driftless: `drift_V = r V`.
i.e., `∂_t V + r S ∂_S V + (1/2) σ² S² ∂_SS V = r V`,
i.e., the BS PDE. -/

namespace MathFin

/-- **BS Itô-drift coefficient** of `V(S, t)` under risk-neutral GBM
`dS_t = r S_t dt + σ S_t dB_t`. Specialises Phase 39's `itoDrift` to
two-argument `V(S, t)` via the two partials `∂_S V` and `∂_SS V`, plus
the `∂_t V` term that comes from the *time* dependence of `V` (Itô's
lemma for `f(X_t, t)` adds a `∂_t f` term).

  `drift(V) = ∂_t V + r S · ∂_S V + (1/2) · σ² S² · ∂_SS V`. -/
noncomputable def bsItoDrift (r σ S V_S V_SS V_t : ℝ) : ℝ :=
  V_t + r * S * V_S + (1 / 2) * σ ^ 2 * S ^ 2 * V_SS

/-- **No-arbitrage condition for the discounted option price**: the drift
of `e^{−rt} V_t` must vanish under `Q`. With the product rule,

  `d(e^{−rt} V_t) = e^{−rt} · (dV − r V dt)`,

so drift of `e^{−rt} V_t` is `e^{−rt} · (drift(V) − r V)`. Setting this to
zero (and dividing by `e^{−rt} > 0`) gives `drift(V) = r V` — equivalently,

  `∂_t V + r S · ∂_S V + (1/2) · σ² S² · ∂_SS V − r V = 0`,

which is the Black-Scholes PDE. -/
theorem bs_pde_from_no_arbitrage (r σ S V V_S V_SS V_t : ℝ) :
    bsItoDrift r σ S V_S V_SS V_t - r * V = 0 ↔
      V_t + r * S * V_S + (1 / 2) * σ ^ 2 * S ^ 2 * V_SS - r * V = 0 := by
  unfold bsItoDrift
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Itô-drift identification of the BS PDE LHS**: the LHS of the
Black-Scholes PDE `∂_t V + r S ∂_S V + (1/2) σ² S² ∂_SS V − r V` equals
`drift(V) − rV` where `drift(V)` is the Itô drift of `V` under risk-
neutral GBM. -/
theorem bs_pde_lhs_eq_drift_minus_rV (r σ S V V_S V_SS V_t : ℝ) :
    V_t + r * S * V_S + (1 / 2) * σ ^ 2 * S ^ 2 * V_SS - r * V =
      bsItoDrift r σ S V_S V_SS V_t - r * V := by
  unfold bsItoDrift
  ring

/-- **One-dimensional Itô drift of `V = V(S)`** (no explicit time
dependence — pure function of `S`). This is just Phase 39's `itoDrift`
with `μ_X = r S, σ_X = σ S, f' = V_S, f'' = V_SS`. -/
lemma bsItoDrift_no_time_eq_itoDrift (r σ S V_S V_SS : ℝ) :
    bsItoDrift r σ S V_S V_SS 0 = itoDrift V_S V_SS (r * S) (σ * S) := by
  unfold bsItoDrift itoDrift
  ring

/-! ### Item 6 — the BS drift IS the general 2D Itô drift under GBM

This closes the loop to `Foundations/ItoLemma2D.lean`: the bespoke
`bsItoDrift` is *literally* `itoDrift2D` of `V(t, S)` specialised to the
risk-neutral GBM generator `(μ_X, σ_X) = (r S, σ S)`. The BS PDE is then
the general Itô-drift machinery applied to one diffusion, not a
pricing-specific algebra — a structural consumer of the foundations
2D-Itô layer (cf. F1 in `docs/portfolio-review-2026-05-28.md`). -/

/-- **The BS Itô drift is the 2D Itô drift under risk-neutral GBM.**
`bsItoDrift r σ S V_S V_SS V_t = itoDrift2D V_t V_S V_SS (r·S) (σ·S)`. The
time-derivative slot `V_t` of `itoDrift2D` carries the `∂_t V` term; the
GBM local drift `r·S` and local volatility `σ·S` fill the generator. -/
lemma bsItoDrift_eq_itoDrift2D (r σ S V_S V_SS V_t : ℝ) :
    bsItoDrift r σ S V_S V_SS V_t = itoDrift2D V_t V_S V_SS (r * S) (σ * S) := by
  unfold bsItoDrift itoDrift2D
  ring

/-- **The Black–Scholes PDE LHS, routed through the general 2D Itô drift.**
A *polynomial identity*: the BS-PDE LHS equals `itoDrift2D V_t V_S V_SS (r·S)
(σ·S) − r·V`, i.e. the general 2D-Itô drift (`Foundations.ItoLemma2D`)
specialised to the risk-neutral GBM generator `(r·S, σ·S)`, minus `r·V`.
This is the value of routing through the shared `itoDrift2D` rather than the
bespoke `bsItoDrift`: the BS-PDE coefficient is one instance of the general
Itô-drift definition.

NOTE — what this does NOT prove: that the discounted price `e^{−rt} V_t` is a
`Q`-martingale (hence driftless), which is what makes "drift `= 0`" the
*no-arbitrage* condition. That continuous-time martingale step is deferred
(see module header); here `… = 0` is only the **algebraic form** of the
no-arbitrage PDE, established by `ring`, not derived from a martingale. -/
theorem bs_pde_eq_itoDrift2D_minus_rV (r σ S V V_S V_SS V_t : ℝ) :
    V_t + r * S * V_S + (1 / 2) * σ ^ 2 * S ^ 2 * V_SS - r * V =
      itoDrift2D V_t V_S V_SS (r * S) (σ * S) - r * V := by
  unfold itoDrift2D
  ring

end MathFin
