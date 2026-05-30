# Architecture

The library's shape is deliberate. Three principles drive every decision:

1. **Name the structural fact, don't repeat the algebra.** When a single
   mathematical principle generates many theorems, that principle gets its
   own module and the consumers delegate. Where a principle is
   load-bearing, downstream proofs collapse to one or two lines.
2. **Be honest about the proof depth.** Not every lemma is a deep theorem.
   Algebraic closed-form bookkeeping is necessary but not sufficient — the
   library is organised in three tiers so the difference is visible.
3. **Build bridges, not replacements.** Foundations machinery becomes
   load-bearing only when downstream modules can consume it. New work
   *adds* an alternative constructor (`X.of_isPreBrownian`) rather than
   replacing existing entry points; existing consumers keep working.

The rest of this document spells out these three principles and catalogues
the modules that implement them.

## The three-tier honesty model

The library divides cleanly into three tiers. Their proof shape makes the
tier visible.

### Tier 1 — Foundational math

Multi-hundred-line proofs in genuine probability + integration +
chain-rule calculus. The hard machinery the rest of the library leans on.

Modules: `Foundations/*` (Wiener integral, Brownian martingales, quadratic
variation, Doob L^p convergence, conditional Jensen, FTAP variants, Itô
drift, pricing kernels), `Binomial/Model`, `Binomial/CRRConvergence`,
`BlackScholes/Call`, `BlackScholes/Put`, `BlackScholes/Forward`, the
various `*Greeks`, `MathlibLp`, `WienerIntegralL2`.

Proof shape: many tactics, real lemma deployment, multi-page derivations.
`#print axioms` is clean; nothing imported from outside Mathlib / Degenne's
`brownian-motion`.

### Tier 2 — Principle modules

A small set of named structural facts whose consumer files *delegate*. A
principle is load-bearing when its instances are *provable equalities*
(Garman, PriceBounds, ConvexPricingFunctional, GreekSigns) rather than
docstring claims.

Catalogue is the [structural-principle table below](#structural-principle-modules).

Proof shape: the master file does the work (a clean derivation or
characterisation); consumers compose with one or two lines.

### Tier 3 — Closed-form verifications

Bookkeeping that textbook closed-form formulas have their claimed
algebraic properties — e.g. `risk_parity_equal_contribution`,
`blackLitterman_*`, `tangentTwo_satisfies_FOC`, `gaussianVaR_translation`
and other VaR axioms, scale-invariance of Sortino / Treynor / IR.

Proof shape: `unfold; field_simp; ring` (or close to it). The proof
*looks* the way it is. The mathematical content of each is in the
*definition*; the lemma confirms the closed form has the claimed property.

This tier is necessary — without it, a textbook formula is just a string —
but it is not "deep." Tier 3 entries should not be conflated with Tier 1
in delivery claims. See [`coverage.md`](coverage.md) for the audit that
separates them.

## The structural-principle modules

A "principle" must be load-bearing. If a master file declares an identity
but no consumer file uses it, the master is a docstring pretending to be a
module. Where a principle generates corollaries (a master is *used*),
proofs in the consumer files collapse to one or two lines.

This is enforced by audit, not just asserted. A 2026-05-23 pass checked each
principle against the actual import graph and wired up the ones whose
load-bearing claim had outrun their consumers:

- `ExponentialDiscount` — `ForwardRate`, `Mortality`, `HazardCurve` now cite
  `rate_eq_neg_log_deriv` for the rate-recovery direction `rate = −d/dt log Q`
  (`Mortality`/`HazardCurve` previously stated this only in prose) and route
  positivity through `discount_pos`.
- `GarmanNormalForm` — `Black76` (`black_futures_price_eq_bsVGarman`) and
  `Dividends` (`bs_dividends_price_eq_bsVGarman`) carry consumer-side
  corollaries chaining their pricing theorem to the Garman equality, so the
  "one formula at different `(A, DF)`" unification is cited from both ends.
- `ConvexPricingFunctional` — `PricingKernel.stateprice_call_butterfly_nonneg`
  feeds the FTAP-derived (provably non-negative) state prices into
  `callPrice_finiteState_butterfly_nonneg`, giving "no-arbitrage ⟹ butterfly
  spreads cost ≥ 0" — the principle's first downstream consumer.
- `StandardGaussianMGF` — already load-bearing transitively: `PowerOption`
  consumes it directly and `LognormalMoments` reaches it through the
  `nthMoment_terminal` hub.

| Principle module | The fact | Where it's load-bearing |
|---|---|---|
| `BlackScholes/GarmanNormalForm.lean` | Every BS-family closed form is `V = A · Φ(d_1) − K · DF · Φ(d_2)`, parameterised by `(A, K, DF, σ, T)`. | `bsV` (standard BS), Black-76 RHS, BS-Merton dividends RHS, KMV-Merton distance-to-default, and **Margrabe's exchange option** (`ExchangeOption.margrabe_eq_bsVGarman`, at `A = S¹₀, K = S²₀, DF = 1`, effective vol `√(σ₁²+σ₂²−2ρσ₁σ₂)`) are **provably the same formula** at different `(A, DF, σ)`. Even a *multivariate* option is one instance — six-plus apparent pricing variants are one. |
| `BlackScholes/StrikeConvexity.lean` | K-convexity at **three scales**: payoff (`K ↦ max(S − K, 0)` convex), finite-state price (`K ↦ Σ q_i · max(S_i − K, 0)` convex via `ConvexPricingFunctional`), continuous BS price (`K ↦ bsV K r σ S τ` convex on `(0, ∞)` via second-derivative test on `hasDerivAt_bsV_KK`). | `Spreads.lean` (bull-spread = antitone face; butterfly = convex face at payoff *and* price); `BreedenLitzenberger.lean` (PDF positivity = infinitesimal convex face). |
| `BlackScholes/PriceBounds.lean` | `0 ≤ bsV`, `0 ≤ bsP`, `Φ ≤ 1`, and put-call parity (the "no-arbitrage rectangle"). | `bsV ≤ S`, `bsP ≤ K · e^{−rT}`, forward lower bound, intrinsic-style put bound, box-spread identity, Merton 1973 strict dominance — all one-line corollaries. Subsumes the former `StaticBounds.lean` and `AmericanCallNoDividend.lean`. |
| `BlackScholes/GreekSigns.lean` | Sign constraints on each BS Greek (δ ∈ [0, 1], γ > 0, ρ ≥ 0, ∂_K V ≤ 0, ∂²_K V ≥ 0). | Names the qualitative content (call is increasing+convex in spot, increasing in vol/rate, decreasing+convex in strike) — sign facts were derivable from `PDE` / `StrikeGreeks` / `HigherGreeks` but never named. |
| `Foundations/ConvexPricingFunctional.lean` | Non-negative linear pricing functional preserves `ConvexOn`. | Call price convex in strike (finite-state), butterfly non-negativity at the *price* level (not just payoff), Breeden-Litzenberger PDF positivity — four scales of one fact. |
| `Foundations/StandardGaussianMGF.lean` | `∫ exp(α + β · z) ∂N(0, 1) = exp(α + β²/2)` (affine-shifted gaussian MGF). | `PowerOption.lean` (`nthMoment_terminal` is a direct instance); `LognormalMoments.lean` (`secondMoment_terminal = nthMoment_terminal 2`). |
| `Foundations/ExponentialDiscount.lean` | `−d/dt log(exp(−H(t))) = H'(t)` (rate as negative log-derivative). | Conceptual core of `ForwardRate.lean` (forward = −∂_T log P), `Mortality.lean` (force = −∂_t log S), `HazardCurve.lean` (hazard = −∂_t log S). |
| `Binomial/MertonAmericanCallTree.lean` | Merton 1973 in the binomial tree, **at any horizon `n`**: `americanPrice = binomialPrice` for the non-dividend call. The one-period continuation dominates the discounted intrinsic (Jensen for `max(·, 0)` + martingale identity + discount shift); the multi-step `intrinsic ≤ binomialPrice` and `americanPrice ≤ binomialPrice` then follow by induction on `n` + monotonicity of the one-period operator. | Combined with `binomialPrice ≤ americanPrice` (`Binomial.American`, trivial direction), gives the equality at every step. |
| `Binomial/ReplicatingUniqueness.lean` | Single-period replicating portfolio `(Δ, B)` is uniquely determined by target payoffs. | Discrete-time market-completeness statement. Combined with First+Second FTAP, completes the FTAP equivalence chain. |
| `Binomial/PathReflection.lean` | **André's reflection principle** (1887, full): for paths `ω : Fin n → Bool` viewed as `±1` walks, (a) algebraic identity `walkPos (reflectAfter τ ω) k = 2 · walkPos ω τ − walkPos ω k` for `τ ≤ k`; (b) reflection-at-first-hitting-time `reflectAtFirstHit a` is an involution on `{ω : HitsLevel a ω}`; (c) the **bijection** `reflectionPrincipleEquiv a b : {ω : hits a, ends at b} ≃ {ω : hits a, ends at 2a − b}` as a Mathlib `Equiv`; (d) the **discrete IVT** `walkPos ω n ≥ a > 0 ⟹ HitsLevel a ω`; (e) the **simplified barrier bijection** `reflectionPrincipleEquiv_below`. | Counting backbone of barrier-option pricing in the binomial tree. The IVT drops the `HitsLevel` condition on one side of the bijection, giving the form actually used: "paths that touch the barrier and end below" ≃ "paths that end above (reflected position)." |
| `Binomial/SnellEnvelope.lean` | **Snell envelope characterisation** of `americanPrice`: it is the *smallest* `V : ℕ → ℝ → ℝ` simultaneously dominating the payoff (`V ≥ g`) and supermartingale w.r.t. the one-step discounted Q-expectation. | Optimal-stopping characterisation of the American price without defining stopping rules on the path space. Combines `americanPrice_ge_intrinsic` + `americanPrice_supermartingale` (existence) with `americanPrice_le_of_supermartingale_dominating` (universality). |
| `Foundations/NoArbitrageDerivations.lean` | **Put-call parity and the forward price as consequences of no-arbitrage**, stated abstractly for any non-negative linear pricing functional `Λ(g) = ∑ q_i · g_i` with bond constraint `Λ(1) = DF` and stock constraint `Λ(S_T) = S_0`. Proves `C(K) − P(K) = S_0 − K · DF` and `F = S_0 / DF` (fair forward strike). | First-principles derivations of two canonical static no-arb identities — independent of any closed form (BS, Bachelier, binomial). |
| `BlackScholes/RiskNeutralProbabilities.lean` | **Probabilistic interpretation of `bsd2`**: under the risk-neutral hypothesis, `Q(S_T > K) = Φ(bsd2 S_0 K r σ T)` — the right factor of the BS formula has *content* (exercise probability), not just algebraic form. | Closes the structural narrative on the BS formula: `Φ(d_2)` is the risk-neutral probability of finishing in the money. The companion `Φ(d_1) = Q^{(S)}(S_T > K)` (stock numeraire) is in `StockNumeraire.lean`. |
| `Performance/Ratios.lean` (extended) | **Sharpe-ratio full affine invariance**: `Sh(c · μ + d, c · r_f + d, c · σ) = Sh(μ, r_f, σ)` for any `c ≠ 0`. Algebraic master `diff_div_affine_invariant` (and signed variant) factor the proofs into one-line corollaries. | The standard "ratio scale invariance" master generalised to full affine invariance — the canonical algebraic content of why Sharpe is a *ratio* and why it cares only about excess return / risk shape, not absolute units. |
| `FixedIncome/DurationSensitivity.lean` | **Modified duration as the negative log-derivative of bond price**: `P'(y) = −ModNum(y)`, hence `P'(y) / P(y) = −D_mod(y)`. Derived from per-cashflow `HasDerivAt` of `c / (1+y)^n` with the `n = 0` and `n ≥ 1` cases bundled by `field_simp + ring`. | First-principles derivation of the operational content of duration: it measures the *percentage* sensitivity of bond price to yield. |
| `FixedIncome/ConvexitySensitivity.lean` | **Bond convexity as the second derivative of price**: `P''(y) = ConvNum(y)`. Completes the discrete yield-Taylor expansion `ΔP / P ≈ −D_mod · Δy + ½ C · (Δy)²`. | Bond convexity is *literally* the second derivative of price w.r.t. yield, not a separately-defined moment — obtained by applying `hasDerivAt_coupon_term` from `DurationSensitivity` a second time. |
| `Portfolio/SharpeFOCDerivation.lean` | **Markowitz cross-product FOC derived from Sharpe-ratio maximisation**: defines `Sh²(w) = E(w)² / V(w)`, computes `HasDerivAt` with the textbook formula `Sh²' = (2EE'V − E²V') / V²`, and shows the numerator factors as `2E · (r₁(Σw)₂ − r₂(Σw)₁)`. With `E ≠ 0, V > 0`, critical points of `Sh²` are exactly the cross-product FOC. | Closes the loop with the pre-existing `tangentTwo_satisfies_FOC`: the FOC arises as the critical-point condition of a real maximisation problem, not as a stated identity. |
| `Portfolio/MarkowitzLagrangian.lean` | **N-asset Markowitz constrained-variance critical points from the Lagrangian** (forward direction): defines `IsConstrainedVarianceCriticalPoint` variationally, proves that any portfolio satisfying the Lagrangian FOC `Σw = λ_1 · 1 + λ_2 · μ` componentwise is a critical point of `(1/2) w^T Σ w` subject to budget + target-return constraints. The `λ_1 = 0` corollary recovers `IsTangentPortfolioN`. | Extends 2-asset `SharpeFOCDerivation` to the N-asset textbook Markowitz formulation. Backward direction (critical point ⟹ FOC) requires `Submodule.orthogonalComplement` machinery and is deferred. |
| `Portfolio/CAPMEquilibrium.lean` | **CAPM from market equilibrium**: under the equilibrium hypothesis that the market portfolio satisfies the tangent-portfolio cross-product FOC `μ_excess(k) · (Σw_M)_j = μ_excess(j) · (Σw_M)_k`, every asset's excess return equals its beta times the market excess return: `μ_excess(i) = β_i · μ_M`. | The discrete-Lagrangian derivation: multiply the FOC by `w_M(j)` and sum to fold `(Σw_M)` into `Var(R_M)` and `μ_excess` into `μ_M`. Derives the SML from optimal portfolio choice + market clearing. |
| `Portfolio/RiskParityFOC.lean` | **Risk parity from log-barrier Lagrangian FOC**: defines `riskContribution_i := w_i · (Σw)_i`, shows `∑ RC_i = portfolioVariance`, and proves the canonical risk-budget portfolio satisfies `RC_i = b_i` from the FOC `(Σw)_i = b_i / w_i` (the log-barrier-regularised variance minimisation). | Risk parity stated as the *output of an optimisation* (log-barrier-regularised variance minimisation), matching the Roncalli-Maillard treatment used in production. |
| `Portfolio/BlackLittermanND.lean` | **N-dim Black-Litterman posterior as normal-equation solution**: defines `blPosteriorPrecision := Σ_inv + Pᵀ · Ω_inv · P` (additive precision update), the precision-weighted RHS `Σ_inv · π + Pᵀ · Ω_inv · Q`, and proves the explicit form `posterior_precision⁻¹ · RHS` satisfies the BL normal equation. | Extends the 1-D closed form to the N-asset / m-view matrix formulation, characterising the posterior as the unique linear-system solution rather than a memorised inverse formula. |
| `BlackScholes/StockNumeraire.lean` | **Delta as stock-numeraire exercise probability**: `Φ(d_1) = Q^(S)(S_T > K)`, where `Q^(S) = Q.withDensity (e^{−rT} · S_T / S_0)` is the stock-numeraire measure. | Closes the structural narrative: both `Φ` factors in the BS formula are exercise probabilities — `Φ(d_2)` under the money-market numeraire, `Φ(d_1)` under the stock numeraire. Their difference `Φ(d_1) − Φ(d_2)` is the "value of optionality." |
| `BlackScholes/PowerCall.lean` | **Powered call closed form via structural reduction to BS-call**: `(S_T)^a` is itself a BS terminal with *effective spot* `S_0^a · exp((a − 1) r T + a(a − 1) / 2 · σ² T)` and *effective volatility* `aσ`. | Power options reuse `bs_call_formula` whole — no new gaussian integral. The only new content is the algebraic identification of `(S_T)^a` as a standard BS terminal. |
| `BlackScholes/ChooserComposition.lean` | **Chooser option as call + put portfolio via PCP at chooser date**: closed-form `chooserPrice := bsV(K, T) + bsP(K · e^{−r(T − t_1)}, t_1)`, and linearity-of-expectation `chooser_integral_decomp`. | The "chooser = call + put with adjusted strike" identity is *not* just an algebraic decomposition — it's the BS pricing identification produced by combining `chooser_via_pcp` (algebra) with `integral_add` (linearity of expectation). |
| `FixedIncome/KMVMertonStructural.lean` | **KMV-Merton `kmvPD` as actual risk-neutral default probability**: combines `riskNeutralProb_S_T_gt_K` with the algebraic survival identity `1 − kmvPD = Φ(bsd2)` to show `kmvPD = 1 − Q({V_T > F}).toReal`. Also `merton_equity_eq_bs_call`. | Connects the algebraic kmvPD definition to the actual `Q(V_T ≤ F)` probability via the same BS structure. |
| `FixedIncome/CDSTimeVarying.lean` | **CDS fair-spread cash-flow balance for time-varying hazard**: `c · annuity(T) = (1 − R) · losses(T)` via integral identities. Plus the discrete multi-period survival factorisation `∏ exp(−h_i Δt_i) = exp(−∑ h_i Δt_i)`. | Generalises constant-hazard `c = h(1 − R)` to the cash-flow-balance form that holds for any deterministic hazard curve. |
| `RiskMeasures/UtilityDerivation.lean` | **Coherent risk axioms from concave utility** (Artzner-Delbaen-Eber-Heath acceptance-set characterisation): concavity of `u` ⟹ acceptance set is closed under convex combinations (the *risk-aversion ⟹ subadditivity* chain); monotonicity of `u` ⟹ translation invariance. | The *content* of the four coherent axioms from the utility primitive: they are consequences of risk-averse expected-utility preferences. |
| `Foundations/BSCallHypFromBrownian.lean` | **`BSCallHyp` / `BachelierHyp` derivable from a pre-Brownian motion**: core scaling lemma `scaled_isPreBrownian_eval_law` shows `W T.toNNReal / √T ∼ N(0, 1)` under `IsPreBrownian W Q`. Constructors `BSCallHyp.of_isPreBrownian` and `BachelierHyp.of_isPreBrownian` then discharge the BS / Bachelier hypotheses additively. | First architectural bridge between `Foundations/` BM machinery and pricing-module consumption. Existing pricing modules continue to work unchanged; downstream consumers gain an optional BM-based constructor. |
| `Foundations/PricingFromBrownian.lean` | **Full BS / Bachelier / Digital / Power / Dividends / StockNumeraire / KMV pricing pipeline derivable from a pre-Brownian motion**: 11 one-line composite corollaries showing that every pricing entry-point that consumes `BSCallHyp` or `BachelierHyp` can be driven from a single primitive (`IsPreBrownian W Q`). | Demonstrates that the entire BS-family pricing infrastructure is *structurally* a corollary of "you have a Brownian motion." |
| `Foundations/VarianceSwapFromQV.lean` + `VarianceSwapEquipartition.lean` + `VarianceSwapLimit.lean` | **Variance-swap fair strike as a QV limit**: under refinement, `E[Σ (X-increments)²]` converges to `σ² · T`. Chain of (a) per-increment QV identity, (b) finite-`n` equipartition closed form, (c) limit as `n → ∞`. | First downstream use of `Foundations/BrownianQuadraticVariation.lean`. The companion log-payoff form and this QV form are two functionals of the same BS price process, both yielding `σ²` (after `1/T` rescaling). |
| `Foundations/PricingKernel.lean` | **Pricing kernel from two-state FTAP backward direction**: discounted EMM weights as state prices, the standard pricing kernel `V_0(X) = e^{−rT}(q_up · X_up + q_down · X_down)`. | The stochastic-discount-factor framework instantiated in the simplest finite-state market — every claim's no-arb price is a single linear functional, derived from no-arbitrage rather than assumed. |

The discipline: a "principle" must be load-bearing. If a master file
declares an identity but no consumer file uses it, the master is a
docstring pretending to be a module.

## The bridge methodology

Tier 1 Foundations machinery (Brownian motion construction, Wiener
integral, Doob L^p, quadratic variation) is only useful to the library
when downstream modules can *consume* it. Until that bridge exists, the
Foundations work sits as 4664+ LOC of dead code from the pricing modules'
perspective.

Bridges are **additive**, not replacing: a new file `Foundations/X.lean`
introduces a constructor `XHyp.of_isPreBrownian` (or similar) that
discharges an existing hypothesis (`BSCallHyp`, `BachelierHyp`,
`BrownianMartingaleHyp`, …) from a single Brownian-motion primitive.
Existing pricing modules continue to work unchanged. New downstream
consumers gain an optional BM-based path.

The first complete bridge programme is documented in
[`bridges.md`](bridges.md): `BSCallHypFromBrownian`,
`PricingFromBrownian`, the variance-swap QV chain, `DiscreteIto`,
`FTAPTwoState`, etc. Each "phase" in the bridge log
adds one constructor and one or more one-line corollaries downstream.

Anti-pattern recognised early: a `Foundations/` file with great
machinery but zero downstream consumers is a docstring pretending to be a
module. Bridges promote it to actually load-bearing.

## Naming and organisation

- Files are organised by topic under `QuantFin/<Section>/`. One
  theorem per file when the theorem is non-trivial; helper lemmas in the
  same file as `private`.
- Section names are user-facing: `BlackScholes/`, `Binomial/`, `Portfolio/`,
  `RiskMeasures/`, etc. Match the textbook chapter you'd reach for if you
  were looking up the result.
- File names are the *result* name, not the technique: `RiskParityFOC.lean`
  not `LogBarrierFOC.lean`. The technique appears in the docstring.
- Inside files, follow Mathlib convention: lemma names in `lower_snake_case`,
  definitions in `camelCase`, types in `PascalCase`. Greek letters work
  but use Roman replacements where the Greek is reserved (e.g. `Sg_inv`
  for `Σ_inv` since capital sigma is a Lean reserved token).

## What's intentionally *not* in the library

- **Path-wise Itô lemma** in full generality: requires the Mathlib Itô
  integral. Drift-coefficient form (`Foundations/ItoLemma.lean`) is in;
  the L²-limit glue is gated.
- **Full Girsanov**: same Mathlib gating.
- **Continuous-time Poisson process** (interarrival exponential,
  superposition, thinning): Mathlib has discrete `PoissonPMF` only.
- **BM pathology theorems** (reflection on continuous paths,
  nowhere-differentiability, law of iterated logarithm): Mathlib + BM
  package don't ship them yet.

These appear in [`coverage.md`](coverage.md) as `reduced_core` with
explicit notes about the gating dependency. They are NOT counted toward
the `delivery-ready` total. The roadmap revisits them as Mathlib infra
lands.
