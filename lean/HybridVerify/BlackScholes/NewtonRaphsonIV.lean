/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Newton-Raphson iteration for implied volatility

For root-finding `f(σ) = 0` (where, in the IV context, `f(σ) = bsV(σ) − C_obs`),
the Newton-Raphson update is

  `σ_{n+1} := σ_n − f(σ_n) / f'(σ_n)`.

Two foundational facts that hold without smoothness hypotheses:

* **Fixed point at a root**: if `f(σ*) = 0`, then `σ*` is a fixed point of
  the Newton iteration: `newtonStep f f' σ* = σ*`.
* **Error formula**: `newtonStep f f' σ − σ* = (σ − σ*) − f(σ) / f'(σ)`
  (when `f(σ*) = 0`).

These don't give convergence rates — quadratic convergence
(`|σ_{n+1} − σ*| ≤ C |σ_n − σ*|²`) requires `|f''|` bounded and `|f'| ≥ m > 0`
on a neighbourhood, plus a Taylor expansion. We record those as future
work; the BS implied-vol setting has `f' = vega > 0` and `f''` bounded on
any neighbourhood of `σ* > 0`, so the convergence theorem applies.

For the bisection method (which converges linearly without smoothness), see
`BisectionIV.lean`.

## Results

* `newtonStep`: the Newton iteration map.
* `newtonStep_fixed_at_root`: roots are fixed points.
* `newtonStep_error_via_root`: error decomposition.
-/

namespace HybridVerify

open Real

/-- **Newton-Raphson iteration step**: `σ_{n+1} = σ_n − f(σ_n) / f'(σ_n)`.

In the BS implied-vol setting, `f σ = bsV σ − C_obs` and
`f' σ = vega(σ)`; the iteration is well-defined whenever vega is non-zero
(which holds for `σ > 0`). -/
noncomputable def newtonStep (f f' : ℝ → ℝ) (σ : ℝ) : ℝ := σ - f σ / f' σ

/-- **A root is a fixed point of the Newton iteration**: if `f σ = 0`,
then `newtonStep f f' σ = σ`. -/
theorem newtonStep_fixed_at_root (f f' : ℝ → ℝ) {σ : ℝ} (h_root : f σ = 0) :
    newtonStep f f' σ = σ := by
  unfold newtonStep
  rw [h_root, zero_div, sub_zero]

/-- **Error decomposition for one Newton step**: when `σ*` is a root of `f`,
`newtonStep f f' σ − σ* = (σ − σ*) − f(σ) / f'(σ)`. The right-hand side is
the linear part of the Taylor expansion of `(σ_{n+1} − σ*)` in `σ − σ*`;
quadratic convergence requires bounding the residual `f''(η)/(2 f'(σ)) ·
(σ − σ*)²` via smoothness, which we do not formalise here. -/
theorem newtonStep_error_via_root
    (f f' : ℝ → ℝ) {σ_star σ : ℝ} (_h_root : f σ_star = 0) :
    newtonStep f f' σ - σ_star = (σ - σ_star) - f σ / f' σ := by
  unfold newtonStep
  ring

end HybridVerify
