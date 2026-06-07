/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

import MathFin.Foundations.QuadraticVariationL2
import MathFin.Foundations.WienerIntegralL2
import MathFin.Foundations.ItoIsometryAdapted
import MathFin.Foundations.ItoIntegralCLM
import MathFin.Foundations.ItoIntegralBrownian
import MathFin.Foundations.DiscreteIto
import MathFin.Foundations.ItoFormulaSquaredL2
import MathFin.Foundations.ItoFormulaCLM
import MathFin.Foundations.ItoLemma2D
import MathFin.Foundations.FeynmanKacHeatEquation
import MathFin.Foundations.GaussianGirsanov
import MathFin.Foundations.BSCallHypFromBrownian
import MathFin.Foundations.ContinuousFTAP
import MathFin.Foundations.CarrMadan
import MathFin.BlackScholes.Call
import MathFin.BlackScholes.PDE
import MathFin.BlackScholes.PDEFromIto
import MathFin.BlackScholes.MargrabeGrounding
import MathFin.Binomial.MartingaleRepresentation
import MathFin.Binomial.CRRCharFun
import MathFin.BlackScholes.MertonDominance
import MathFin.Foundations.MarkovPathMeasure
import Architect

/-!
# Blueprint spine — post-hoc `@[blueprint]` tagging

Declares the blueprint nodes of the deductive spine (`docs/blueprint.md`) by
tagging existing declarations **post hoc** with LeanArchitect's
`attribute [blueprint …]`. The tags live HERE, in a leaf module nothing
imports, so the proof modules are untouched: their sources keep their
verification-ledger hashes (zero restale), and the spine's dependency edges
are *inferred from the proof terms* (`Architect.collectUsed` — a transitive
walk that stops at tagged constants, so edges pass through untagged helpers).
The graph in `docs/blueprint.md` is generated ground truth, never hand-drawn.

Regenerate after touching the spine:

  `lake build MathFin.Blueprint && lake exe blueprint_export MathFin.Blueprint`
  then `python3 tools/blueprint_render.py` (see that file's header).

Node prose lives in `(statement := …)`: one honest sentence per node — what
the mathematics says, with deferrals named, never papered over.
-/

@[expose] public section

-- ===== root: the driving noise (upstream — Degenne's brownian-motion) =====

attribute [blueprint "def:brownian-motion" (title := "Brownian motion (Degenne, upstream)")
  (statement := /-- The driving noise: independent stationary Gaussian increments,
  $B_t \sim N(0,t)$ — `IsPreBrownian`, consumed from Rémy Degenne's
  `brownian-motion` package, on which this library builds. -/)]
  ProbabilityTheory.IsPreBrownian

-- ===== foundations =====

attribute [blueprint "thm:quadratic-variation" (title := "Quadratic variation: ∑(ΔB)² → T in L²")
  (statement := /-- Along refining partitions, $\sum_k (B_{t_{k+1}}-B_{t_k})^2 \to T$
  in $L^2$: realized variance accumulates linearly in time at unit rate — the
  root of the "$\sigma^2 \cdot$ time" that pervades pricing. -/)]
  MathFin.QuadraticVariationL2.tendsto_qv

attribute [blueprint "thm:wiener-isometry" (title := "Wiener isometry (deterministic L²)")
  (statement := /-- For deterministic step integrands,
  $E[(\int \varphi\,dB)^2] = \int \varphi^2\,dt$: the $L^2$ geometry of a fixed
  (non-reacting) position in Brownian noise. -/)]
  MathFin.WienerIntegralL2.wiener_assembly_isometry

attribute [blueprint "thm:ito-isometry-adapted" (title := "Adapted Itô isometry")
  (statement := /-- For random *adapted* simple integrands,
  $E[(\sum_k \varphi_k \Delta B_k)^2] = \sum_k E[\varphi_k^2]\,\Delta t_k$ — the
  cross terms vanish by the weak Markov property, the exact point where Itô
  departs from Wiener. -/)]
  MathFin.ItoIsometryAdapted.ito_isometry_discrete

attribute [blueprint "def:ito-integral-clm" (title := "Continuous Itô integral (CLM on [0,T])")
  (statement := /-- The discrete isometry extended to a continuous linear isometry
  on predictable $L^2$ integrands over $[0,T]$, via density of simple processes
  (Dynkin π-λ on predictable rectangles) and `LinearMap.extendOfNorm`. -/)]
  MathFin.ItoIntegralCLM.itoIntegralCLM_T

attribute [blueprint "thm:ito-integral-brownian" (title := "∫₀ᵀ B dB = ½(B_T² − B₀² − T)")
  (statement := /-- The CLM's first genuine consumer: $\int_0^T B\,dB$ computed
  *through the abstract integral*, agreeing with the quadratic-variation limit —
  the clamp-truncation + isometry-Cauchy template any unbounded-coefficient
  consumer would reuse. -/)]
  MathFin.ItoIntegralBrownian.itoIntegralCLM_T_brownian

attribute [blueprint "thm:discrete-ito" (title := "Discrete Itô formula (pathwise)")
  (statement := /-- The exact pathwise identity
  $f(X_N) - f(X_0) = \sum f'(X_k)\Delta X_k + \tfrac12 \sum f''(X_k)(\Delta X_k)^2
  + \sum R_k$ — Itô's lemma before any limit is taken. -/)]
  MathFin.discrete_ito_formula

attribute [blueprint "thm:ito-squared-l2" (title := "Itô for x² in L²: ∑B·ΔB → ½(B_T²−B₀²−T)")
  (statement := /-- The continuous $L^2$ form for $x^2$: Riemann sums of
  $B\,dB$ converge along the uniform partition — one algebraic step from the
  discrete identity plus the $L^2$ quadratic variation. The
  $B_t^2 = 2\int B\,dB + t$ keystone behind variance-swap pricing. -/)]
  MathFin.itoSquared_L2_tendsto_div2

attribute [blueprint "thm:ito-formula-l2" (title := "Itô formula, L² (C³ bounded — Summit A)")
  (statement := /-- The continuous-time $L^2$ Itô formula
  $f(B_T) - f(B_0) = \int_0^T f'(B_s)\,dB_s + \tfrac12\int_0^T f''(B_s)\,ds$ for
  $C^3$ functions with bounded derivatives, proved from primitives (weighted QV,
  Taylor remainder, Riemann↔CLM bridge). Unbounded coefficients (e.g. GBM's
  exponential) are honestly out of scope — the named gap. -/)]
  MathFin.ito_formula_L2_bddDeriv

attribute [blueprint "thm:expectation-ito" (title := "Expectation-form Itô / Feynman–Kac")
  (statement := /-- $E[f(B_t)] = f(0) + \tfrac12 \int_0^t E[f''(B_s)]\,ds$, proved
  via the heat equation: the $\tfrac12\sigma^2$ second-order term that drives the
  Black–Scholes PDE. -/)]
  MathFin.FeynmanKacHeatEquation.expectation_ito

attribute [blueprint "thm:gbm-sde" (title := "GBM coefficient matching (algebraic)")
  (statement := /-- $S(t,B_t)$ with $S = S_0 e^{(\mu-\sigma^2/2)t+\sigma x}$ matches
  the Itô coefficients of $dS = \mu S\,dt + \sigma S\,dB$: genuine `HasDerivAt`
  partials + the 2D Itô drift. Honestly *coefficient matching*, not a continuous
  SDE-solution theorem — the $-\sigma^2/2$ cancellation IS the Itô correction. -/)]
  MathFin.gbm_solves_sde

-- ===== change of measure — the centerpiece =====

attribute [blueprint "thm:esscher-tilt" (title := "Esscher tilt is the Gaussian Girsanov")
  (statement := /-- Tilting the physical Gaussian by an exponential density yields
  an equivalent probability measure with shifted mean — static Girsanov,
  constructed, not assumed. -/)]
  MathFin.hasLaw_esscher_tilt

attribute [blueprint "thm:girsanov-call" (title := "Call price from the physical measure")
  (statement := /-- Under the Esscher-derived risk-neutral measure the call price
  is the discounted expectation: **the risk-neutral measure is a theorem, not an
  axiom** — `BSCallHyp` stops being a hypothesis. -/)]
  MathFin.bs_call_formula_of_physical

attribute [blueprint "thm:bscallhyp-brownian" (title := "BSCallHyp from a Brownian model")
  (statement := /-- A concrete Brownian-driven physical model produces the pricing
  hypothesis directly — the second route into `BSCallHyp`. -/)]
  MathFin.BSCallHyp.of_isPreBrownian

attribute [blueprint "thm:continuous-ftap" (title := "Continuous-time first FTAP (EMM)")
  (statement := /-- Under the risk-neutral measure the discounted price
  $e^{-rt}S_t$ is a continuous-time martingale, straight from the Wald
  exponential — the defining EMM property, with no stochastic-integral
  machinery. -/)]
  MathFin.discountedGBM_isMartingale

-- ===== pricing =====

attribute [blueprint "thm:bs-call" (title := "Black–Scholes call formula")
  (statement := /-- Under `BSCallHyp`, the call price is
  $S_0\Phi(d_1) - Ke^{-rT}\Phi(d_2)$. -/)]
  MathFin.bs_call_formula

attribute [blueprint "thm:bs-identity" (title := "bs_identity: S·φ(d₁) = Ke^{−rτ}·φ(d₂)")
  (statement := /-- The algebraic collapse that cancels the pdf cross-terms —
  a self-contained root (only the $d_1/d_2$ definitions and the Gaussian
  density), feeding every clean Greek formula and the PDE. -/)]
  MathFin.bs_identity

attribute [blueprint "thm:bs-delta" (title := "Greeks (δ shown; γ vega θ ρ alongside)")
  (statement := /-- $\partial V/\partial S = \Phi(d_1)$ — delta, the hedge ratio;
  representative of the five Greeks ($\delta, \gamma, \text{vega}, \theta, \rho$),
  each a real `HasDerivAt` derivation through `bs_identity`. -/)]
  MathFin.hasDerivAt_bsV_S

attribute [blueprint "thm:bs-pde" (title := "Black–Scholes PDE (from the closed form)")
  (statement := /-- The closed-form price satisfies
  $\theta + rS\delta + \tfrac12\sigma^2S^2\gamma - rV = 0$, verified through the
  Greeks and `bs_identity`. -/)]
  MathFin.bs_pde_holds

attribute [blueprint "thm:bs-pde-no-arb" (title := "BS PDE ↔ Itô-drift balance (algebraic)")
  (statement := /-- The PDE is *algebraically equivalent* to the Itô-drift balance
  $\text{drift} - rV = 0$, routed through the shared `itoDrift2D`. Deferred, by
  name: deriving drift $=0$ *from* the no-arbitrage $Q$-martingale (needs the
  time-dependent Itô formula on the unbounded-Γ value function). -/)]
  MathFin.bs_pde_from_no_arbitrage

attribute [blueprint "thm:margrabe" (title := "Margrabe exchange option")
  (statement := /-- The option to exchange one asset for another prices as a BS
  call on the ratio with effective volatility
  $\sqrt{\sigma_1^2 + \sigma_2^2 - 2\rho\sigma_1\sigma_2}$ — the multivariate
  corollary. -/)]
  MathFin.margrabe_price_of_gaussian

attribute [blueprint "thm:carr-madan" (title := "Carr–Madan static replication")
  (statement := /-- Every twice-differentiable payoff decomposes as cash, a
  forward, and a static book of OTM options weighted by its convexity $f''$ —
  one integration by parts plus a positive-part case split. The log payoff
  specializes to the variance-swap $1/K^2$ strip. -/)]
  MathFin.carrMadan_spanning

attribute [blueprint "thm:binomial-representation" (title := "Binomial martingale representation (completeness)")
  (statement := /-- On the binomial tree every martingale is the discrete
  stochastic integral of a *predictable* hedge: $H = \Delta M/\Delta S$, fixed
  before the flip — completeness, the second pillar of the FTAP, purely
  algebraic and pathwise. -/)]
  MathFin.binomial_martingale_representation

attribute [blueprint "thm:crr-bs-convergence" (title := "CRR → Black–Scholes convergence")
  (statement := /-- The binomial call price converges to the Black–Scholes call
  price: charFun → Lévy continuity → weak convergence, with put–call parity
  lifting the (bounded) put's convergence to the call. -/)]
  MathFin.binomialPrice_call_tendsto_bs

attribute [blueprint "thm:merton-dominance" (title := "Merton dominance: jump risk is never free")
  (statement := /-- The Merton (1976) jump-diffusion call price dominates the
  Black–Scholes price at the diffusion vol, for every intensity, mean jump
  size $k > -1$, and jump vol: vega prices the jump-size channel (conditional
  vols exceed $\sigma$), gamma prices the jump-count channel — spot convexity
  gives a supporting tangent at $S_0$ whose linear term integrates to zero by
  the compensation identity $E[\mathrm{spot}_N] = S_0$. -/)]
  MathFin.bsV_le_mertonCallPrice

attribute [blueprint "thm:markov-path-law" (title := "Markov path law (Ionescu–Tulcea)")
  (statement := /-- The law of a countable-state Markov chain, constructed on
  infinite trajectories by Mathlib's Ionescu–Tulcea trajectory kernels from
  kernels reading only the last history coordinate; the finite-path
  factorization $P(X_0{=}i_0,\dots,X_n{=}i_n) = \mathrm{init}(i_0)\prod_k
  P(i_k,i_{k+1})$ is derived by induction through the comp-product recursion
  of the marginals (Saporito 1.1.2). -/)]
  MathFin.markovPathMeasure_cylinder
