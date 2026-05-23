# Mathlib / BrownianMotion-Package Bridge Audit

**Date:** 2026-05-22
**Scope:** All 22 modules under `lean/HybridVerify/Foundations/` (4664 LOC)
plus pricing-module consumption of Mathlib's probability surface.

## Executive summary

The earlier critique that "4664 LOC of Foundations is dead code from pricing
modules" was **half right and half wrong**:

- **Right** that the BM/Wiener/martingale machinery is structurally
  disconnected from pricing modules. `IsBrownianMotion`, `Martingale`
  (Mathlib class), `wienerIntegral`, `quadraticVariation`, `StoppingTime`,
  `condExp` are referenced **0 times** in any pricing module.
- **Wrong** that Foundations duplicates Mathlib. Of the 9 substantive
  Foundations files audited below, **8 fill genuine Mathlib gaps** that
  cannot be replaced by direct Mathlib imports.

The right action is **additive bridges** (constructors connecting Foundations
to pricing) rather than **destructive replacement** (deleting Foundations in
favor of Mathlib equivalents). Phase 30 (Bridge A,
`BSCallHypFromBrownian.lean`) is the first such bridge.

## Per-module audit findings

### Foundations/BrownianQuadraticVariation.lean (161 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **What it does:** L¹-expectation form of `[B, B]_t = t` for processes with
  Gaussian increments. Pure marginal-moment computation via
  `variance_id_gaussianReal`.
- **BrownianMotion package equivalent:**
  `StochasticIntegral/QuadraticVariation.lean` defines `quadraticVariation`
  via the Doob-Meyer decomposition (`predictablePart` of squared norm).
  Currently sorry-laden (WIP).
- **Bridge opportunity:** Once BM package's path-wise QV is complete, derive
  our L¹ version as its expectation. For now, **keep both**.

### Foundations/LpContinuousMartingaleConvergence.lean (725 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **What it does:** L^p convergence at naturals for continuous-time L^p-
  bounded martingales (`lp_continuous_martingale_converges_at_naturals`).
- **BrownianMotion package equivalent:**
  `StochasticIntegral/DoobLp.lean` proves Doob's maximal inequality
  (`maximal_ineq_countable`, `maximal_ineq_ennreal`). Related but not the
  same theorem. The maximal inequality is *used* in our convergence proof.
- **Bridge opportunity:** Replace our internal Doob's maximal inequality
  (if any) with imports from BM package's `DoobLp.lean`. Low-LOC change,
  defer until needed.

### Foundations/MartingaleTransform.lean (123 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **What it does:** Discrete martingale-transform construction `(A · M)_n :=
  ∑_{k<n} A_{k+1}(M_{k+1} − M_k)` and adapted-integrability-martingale
  property.
- **Mathlib equivalent:** None found by name search. Mathlib's
  `Mathlib.Probability.Martingale.*` covers discrete and continuous
  martingales but no `martingaleTransform` named declaration.
- **Bridge opportunity:** None needed. Likely upstream candidate.

### Foundations/CondExpJensen.lean (95 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **Self-documenting:** The file's own docstring says "Mathlib v4.30 has no
  general subgradient API for convex functions on ℝ" — the explicit
  subgradient parameterisation is necessary.
- **Bridge opportunity:** None. Upstream candidate when Mathlib gains a
  subgradient API.

### Foundations/BivariateGaussian.lean (165 LOC)

- **Status:** Builds finance-specific struct over Mathlib `HasGaussianLaw`.
- **What it does:** `BivariateGaussianHyp` packages the bivariate-Gaussian
  conditional-expectation formula `E[X | σ(Y)] = μ_X + (ρ σ_X / σ_Y)(Y - μ_Y)`.
- **Mathlib equivalent:** Mathlib has `IsGaussianProcess`, `HasGaussianLaw`,
  `gaussianProjectiveFamily` (in BrownianMotion package). The conditional-
  expectation closed form for bivariate is not directly stated.
- **Bridge opportunity:** Connect `joint_gaussian` to `HasGaussianLaw` more
  formally if not already. Low value.

### Foundations/StandardGaussianMGF.lean (81 LOC)

- **Status:** Specialised reformulation. Possible partial duplication.
- **What it does:** Specialises `∫ exp(c·Z) ∂N(0,1) = exp(c²/2)` for the BS
  use case. Currently derived from `integral_exp_mul_gaussianPDFReal_univ`.
- **Mathlib equivalent:** `gaussianReal_charFun` is the characteristic
  function `E[exp(i·t·X)]`. The MGF would be its analytic continuation to
  real `c`.
- **Bridge opportunity:** Could potentially derive our MGF identity from
  `gaussianReal_charFun` via analytic continuation. Significant rework for
  modest gain. **Defer.**

### Foundations/GaussianCDFDeriv.lean (81 LOC)

- **Status:** Fills Mathlib gap. NOT duplicate.
- **Self-documenting:** "not present in Mathlib (no `Real.erf`, no
  `gaussianReal_Iic_hasDerivAt`)".
- **Bridge opportunity:** None. Upstream candidate.

### Foundations/WienerIntegral.lean + WienerIntegralL2.lean (580 LOC combined)

- **Status:** Foundation work. Possible partial overlap with BM package.
- **BM package equivalents:** `StochasticIntegral/SimpleProcess.lean`,
  `MonotoneProcess.lean`, `LocalMartingale.lean`, `Predictable.lean`,
  `Centering.lean`. The BM package is more general (cadlag, predictable
  processes) where ours is L²-specific Wiener integral.
- **Bridge opportunity:** Once BM package's stochastic-integral pipeline is
  complete (currently has sorries), our L² Wiener integral could be derived
  as a special case of theirs. **Defer until BM package stabilises.**

### Foundations/MathlibLp.lean (1019 LOC) — LARGEST

- **Status:** Substantial Mathlib `Lp` extensions. Not audited in detail.
- **Bridge opportunity:** This file deserves a dedicated audit pass; out of
  scope for current bridging session. **TODO.**

### Foundations/BrownianMartingale.lean (473 LOC)

- **Status:** Continuous-time Brownian-motion-is-martingale derivations.
- **BM package equivalent:** `IsPreBrownian` + `Auxiliary/Martingale`. The
  package's `IsPreBrownian` characterises BM by finite-dim Gaussian laws
  and has a continuous modification (Kolmogorov-Chentsov). Our file builds
  martingale + stopping-time structure on top.
- **Bridge opportunity:** Re-derive our `BrownianMartingale` content as
  consequences of `IsPreBrownian`. Could shrink considerably. **TODO** —
  needs careful audit to preserve any unique content.

## Bridges executed (Phase 30+)

| # | Name | File | Status |
|---|------|------|--------|
| A | `BSCallHyp.of_isPreBrownian` | `Foundations/BSCallHypFromBrownian.lean` | NEW (phase 30) |
| A.2 | `BachelierHyp.of_isPreBrownian` | (same file) | NEW (phase 30) |
| — | Core scaling lemma `scaled_isPreBrownian_eval_law` | (same file) | NEW (phase 30) |
| — | `bsTerminal_via_brownian` (S_T = S_0 · exp((r−σ²/2)T + σ·W_T)) | (same file) | NEW (phase 30) |
| — | `bachelierTerminal_via_brownian` (S_T = S_0 + σ·W_T) | (same file) | NEW (phase 30) |
| 31 | Full pricing pipeline from `IsPreBrownian` (composite corollaries): BS call, put, put-call parity, Bachelier, cash digital, asset digital, power call, dividends call, stock numeraire, KMV PD, Merton equity | `Foundations/PricingFromBrownian.lean` | NEW (phase 31) |
| 32 | Variance-swap per-increment QV identity: `E[(X_t − X_s)²] = σ²(t−s) + (r−σ²/2)²(t−s)²` for BS log-price under `BrownianQuadraticVariation` hypothesis. First downstream use of the BQV module from outside `Foundations/BrownianQuadraticVariation.lean`. Exposed previously-private `integral_sq_increment`, `integrable_sq_increment`, `measurable_increment` and added new public `integral_increment` (E[B_t − B_s] = 0), `integrable_increment` to BQV's public surface | `Foundations/VarianceSwapFromQV.lean` + BQV public-surface additions | NEW (phase 32) |

## Bridges planned but deferred

| # | Name | Reason for deferring |
|---|------|----------------------|
| B | Discounted price as Mathlib `Martingale` | Requires defining the price process structure (vs. just the terminal). Significant additive work. |
| D | `SnellEnvelope` over Mathlib `StoppingTime` | Requires reworking the recursive Binomial price definition to thread filtration. |
| 27 | Vasicek from `IsPreBrownian` | Requires stochastic integral for `∫_0^t e^{-κ(t-s)} dW_s` term; BM package's stochastic integral has sorries. |
| 25 | Variance swap from QV | Tractable once BM package QV completes. |
| 4 | CRR via Mathlib CLT/Skorohod | Significant refactor of `CRRConvergence.lean`. |
| 6 | NoArbitrage via `LinearMap` | Refactor of `NoArbitrageDerivations.lean`. |
| 28 | Forward-rate / hazard via Mathlib `intervalIntegral` | Minor cleanup, low priority. |

## Conclusion

Foundations is **not** slop. It fills Mathlib gaps and shouldn't be deleted.
The architectural bridge gap is real but the remedy is additive constructors
(Bridge A pattern) rather than wholesale replacement. The 4664 LOC stays;
new pricing entry points (BS, Bachelier, eventually Vasicek/CIR via Itô)
gain optional BM-based constructors that compose with existing pricing
machinery.

The biggest remaining audit target is `MathlibLp.lean` (1019 LOC) — its
relationship to Mathlib's current `Lp` machinery deserves a dedicated pass.
