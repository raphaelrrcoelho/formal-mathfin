# Feynman–Kac (growth-controlled heat equation) — explored, deferred, then SUPERSEDED

> **SUPERSEDED 2026-06-08 — the kernel-differentiation FK route landed.** The chain
> sketched in *What this was* (`∂ₓ/∂ₓₓ/∂ₜ feynmanU` under the integral + the kernel PDE
> `∂ₜ K = ½ ∂_yy K` ⟹ the BS PDE) is now **built and load-bearing**, not deferred.
> `MathFin/Foundations/FeynmanKacHeatEquation.lean` proves
> `hasDerivAt_feynmanU_{t,x,xx}` (routed through the parametric skeleton
> `hasDerivAt_integral_mul_kernelFamily`) and `feynmanU_heat_equation`;
> `MathFin/BlackScholes/PDEFromFeynmanKac.lean` composes them into the keystone
> `bsV_satisfies_bs_pde_via_feynmanKac` (the BS PDE derived *independently* of Itô, via the
> heat kernel's joint Fréchet-differentiability `hasFDerivAt_heatKernel`), wired to the
> corpus as `sc-bs-pde-feynman-kac`. So `feynmanU` is no longer an orphan — it is the heat
> flow the Black–Scholes Theta/Delta/Gamma and the PDE all consume. What the
> *Why deferred* section below got right is the **boundary**: this is the
> constant-coefficient (closed-form) case; the genuinely-open work is the
> **variable-coefficient** FK on the general-Itô/SDE layer (local vol, Heston), plus the
> fully-general continuous-`g` PDE + uniqueness. The text below is kept as the historical
> record of the deferral and as the design notes whose plan was ultimately executed.

**Status:** built + verified, then **reverted on 2026-05-29** (commit `9b016b1`; the
lemmas lived in-tree at `eaa5c59`), then **revived and completed 2026-06-08** as the
Feynman–Kac → BS-PDE keystone (see the superseded banner above). The three verified
foundation lemmas are preserved verbatim below for posterity / revival.

This follows the same convention as [`ito-integral-clm-deferred.md`](ito-integral-clm-deferred.md):
a design + working-code record for a direction that is sound but not currently
load-bearing, kept so it can be revived cheaply rather than re-derived.

## What this was

A **growth-controlled heat-equation Feynman–Kac** result, via the *kernel-differentiation*
route: for the convolution `u(t,x) = feynmanU g t x = ∫ z, g z · K(t, z−x) dz` (already in
`FeynmanKacHeatEquation.lean`), move the `x`/`t`-derivatives onto the **smooth kernel** `K`
rather than onto `g`. Then `g` need only be **continuous + growth-controlled** (the call
payoff `g(z) = max(eᶻ−K, 0) ≤ eᶻ`), never differentiated — so the call's kink is sidestepped,
the obstruction that blocks the existing bounded-`C²` FK proof
(`heatConvolution_eq_add_integral_deriv`). The target chain:

```
∂ₓ feynmanU, ∂ₓₓ feynmanU, ∂ₜ feynmanU   (dominated differentiation under the integral)
  + kernel PDE  ∂ₜ K = ½ ∂_yy K = ½ ∂ₓₓ K(t, z−x)
  ⟹  ∂ₜ u = ½ ∂ₓₓ u   (growth-controlled heat-equation Feynman–Kac)
  + BS log-transform (S = eˣ, discount e^{−r(T−t)})
  ⟹  V(t,S) = e^{−r(T−t)} E_Q[payoff(S_T)]  solves the BS PDE  (the call, structurally)
```

## Why deferred (not needed — ever, for the BS world)

1. **Permanently redundant for the BS model.** `BlackScholes/PDE.lean` `bs_pde_holds`
   already proves the closed-form price `bsV` satisfies the BS PDE (via genuine
   `HasDerivAt` Greeks), and `Foundations/PricingFromBrownian.bs_call_formula_via_brownian`
   proves the risk-neutral expectation equals `bsV`. Compose them ⇒ "risk-neutral price
   solves the BS PDE" is already a theorem. A second, structural derivation of the same
   fact adds depth but fills no capability gap.
2. **Doesn't reach where FK earns its keep.** FK's real mathematical-finance job is pricing
   things with **no closed form** — local vol `σ(S,t)`, stochastic vol (Heston), exotics —
   which are **variable-coefficient** parabolic PDEs needing FK for *general diffusions*
   (built on the general Itô/SDE layer). That is a different, much harder theorem. The
   constant-coefficient heat equation here is exactly the case that already has a closed
   form. So it is redundant where it applies and absent where it would matter.

By the project's load-bearing-only rule (the same that flagged the `ItoIntegralProcess`
R5 scaffold), three unconsumed lemmas are premature infra — hence the revert.

## Revival trigger

Revisit only if the library pivots toward **PDE / numerical pricing of payoffs or models
without closed forms**. At that point the genuinely useful object is a *general
variable-coefficient* Feynman–Kac on the general-Itô layer; the lemmas below are the
constant-coefficient warm-up and the integrability backbone (the Gaussian-moment
majorants), reusable as-is.

## The verified foundation lemmas (verbatim)

These were `private` lemmas **inside `MathFin/Foundations/FeynmanKacHeatEquation.lean`**
and reuse its private kernel helpers (`heatKernel`, `hasDerivAt_heatKernel_y`,
`integrable_heatKernel`, `continuous_heatKernel`, `heatKernel_nonneg`,
`integrable_mul_heatKernel_of_gaussian`) plus Mathlib's
`integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet` /
`integrableExpSet_fun_id_gaussianReal`. To revive: paste back after
`integrable_poly_heatKernel`. All three were green (lean-check, 0 sorry) on the
2026-05-29 toolchain pin.

```lean
/-- **One-sided exponential growth is dominated by the heat kernel.** `e^w · K(t, w)` is
integrable: dominated by `(e^t·√2)·K(2t, w)`, since completing the square gives
`w − w²/(4t) − t = −(w−2t)²/(4t) ≤ 0`, i.e. `e^w·e^{−w²/2t} ≤ e^t·e^{−w²/4t}`. This is the
integrability backbone for growth-controlled payoffs (the call satisfies `|g(z)| ≤ e^z`). -/
private lemma integrable_exp_mul_heatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun w => Real.exp w * heatKernel t w) volume := by
  have h2t : (0 : ℝ) < 2 * t := by positivity
  refine Integrable.mono' ((integrable_heatKernel h2t).const_mul (Real.exp t * Real.sqrt 2))
    ((Real.continuous_exp.mul (continuous_heatKernel t)).aestronglyMeasurable)
    (ae_of_all _ fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg w) (heatKernel_nonneg ht w))]
  have hsqrt : Real.sqrt (2 * Real.pi * (2 * t)) = Real.sqrt 2 * Real.sqrt (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * (2 * t) = 2 * (2 * Real.pi * t) from by ring,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hexp : Real.exp w * Real.exp (-(w ^ 2) / (2 * t))
      ≤ Real.exp t * Real.exp (-(w ^ 2) / (2 * (2 * t))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hkey : (0:ℝ) ≤ (w - 2 * t) ^ 2 / (4 * t) := by positivity
    have hexpand : (w - 2 * t) ^ 2 / (4 * t)
        = (t + -(w ^ 2) / (2 * (2 * t))) - (w + -(w ^ 2) / (2 * t)) := by
      field_simp
      ring
    linarith [hexpand ▸ hkey]
  rw [heatKernel, heatKernel, hsqrt]
  rw [show Real.exp t * Real.sqrt 2 * ((Real.sqrt 2 * Real.sqrt (2 * Real.pi * t))⁻¹
        * Real.exp (-(w ^ 2) / (2 * (2 * t))))
      = (Real.sqrt (2 * Real.pi * t))⁻¹ * (Real.exp t * Real.exp (-(w ^ 2) / (2 * (2 * t)))) from by
    rw [mul_inv]
    have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp]
  rw [show Real.exp w * ((Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-(w ^ 2) / (2 * t)))
      = (Real.sqrt (2 * Real.pi * t))⁻¹ * (Real.exp w * Real.exp (-(w ^ 2) / (2 * t))) from by ring]
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- `x`-derivative of the kernel `x ↦ K(t, z − x)`: `∂_x K(t, z−x) = ((z−x)/t)·K(t, z−x)`.
The chain rule on `hasDerivAt_heatKernel_y` (`∂_y K = −(y/t)K`) composed with `∂_x(z−x) = −1`.
This is what lets us differentiate `feynmanU g t x = ∫ g(z)·K(t,z−x) dz` in `x` by moving the
derivative onto the (smooth) kernel — so `g` need only be continuous, never differentiated. -/
private lemma hasDerivAt_heatKernel_sub {t : ℝ} (ht : 0 < t) (z x : ℝ) :
    HasDerivAt (fun x => heatKernel t (z - x))
      ((z - x) / t * heatKernel t (z - x)) x := by
  have h := (hasDerivAt_heatKernel_y ht (z - x)).comp x ((hasDerivAt_id x).const_sub z)
  simpa using h

/-- **`e^w · |w|ⁿ · K(t, w)` is integrable** for every `n`. Via the Gaussian MGF: the set of
exponential moments of `id` under `gaussianReal 0 t` is all of `ℝ`
(`integrableExpSet_id_gaussianReal`), so `|w|ⁿ · e^{1·w}` is `gaussianReal`-integrable
(`integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet`); transfer to the heat kernel
via `integrable_mul_heatKernel_of_gaussian`. Supplies the `∂ₓ`/`∂ₓₓ`-domination majorants for
growth-controlled payoffs. -/
private lemma integrable_exp_mul_abs_pow_heatKernel {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Integrable (fun w => Real.exp w * |w| ^ n * heatKernel t w) volume := by
  have hg : Integrable (fun w => |w| ^ n * Real.exp (1 * w)) (gaussianReal 0 t.toNNReal) :=
    integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
      (by rw [integrableExpSet_fun_id_gaussianReal, interior_univ]; exact Set.mem_univ 1) n
  refine (integrable_mul_heatKernel_of_gaussian ht hg).congr
    (Filter.Eventually.of_forall fun w => ?_)
  show (|w| ^ n * Real.exp (1 * w)) * heatKernel t w = Real.exp w * |w| ^ n * heatKernel t w
  rw [one_mul]; ring
```

## The unbuilt engine (design, for the reviver)

The three differentiation passes mirror the existing `hasDerivAt_phi` (which does the
*time*-derivative under the integral) but in `x`, using
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The one new ingredient is a
**spatial** Gaussian-shift majorant: for `|x − x₀| ≤ δ`,

```
K(t, z−x) ≤ (√2 · e^{δ²/t}) · K(2t, z−x₀)      [complete the square in the shift]
```

so the `∂ₓ` integrand `g(z)·((z−x)/t)·K(t,z−x)` is dominated, uniformly over the `δ`-ball,
by `const · eᶻ · (|z−x₀|+δ) · K(2t, z−x₀)` — integrable by the shift of
`integrable_exp_mul_abs_pow_heatKernel` (`n = 0, 1`). `∂ₓₓ` needs `n ≤ 2`. Then the kernel
PDE `∂ₜ K = ½ ∂_yy K` (already proved: `heatKernel_t_eq_half_y_y`) with `∂ₓ K(t,z−x) =
−∂_y K(t,z−x)` gives `∂ₜ u = ½ ∂ₓₓ u`. The BS log-transform + discount factor then routes
the BS operator onto the heat operator at the call payoff.
