# The leaps: deriving the risk-neutral measure and beyond

The static Black-Scholes world in this library is complete and axioms-clean,
but for a long time it rested on one *assumption*: `BSCallHyp` — "the driver
`Z` is standard normal under the risk-neutral measure `Q`" — was a hypothesis
that 14 pricing files took on faith. The 2026-05-23 "leaps" close that gap and
push past it. Each leap is foundation-certain and build-enforced
(`QuantFin/AxiomAudit.lean`); none introduces a hypothesis-form theorem whose
substantive hypothesis is left undischarged.

This document is the narrative. For the per-theorem audit see
[`coverage.md`](coverage.md); for the bridge catalogue see
[`bridges.md`](bridges.md).

## Leap 1 — static Girsanov: the risk-neutral measure is *derived*

`QuantFin/Foundations/GaussianGirsanov.lean`.

`BSCallHyp` is no longer an axiom. The risk-neutral measure `Q` is
*constructed* from the physical measure `P` by an explicit Radon-Nikodym
(Esscher) density, and the recentred driver is *proven* standard normal under
it. The deductive chain, bottom-up:

| Step | Theorem | Content |
|---|---|---|
| 1 | `gaussian_esscher_pdf` | Completing the square: `exp(c·x − c²/2)·φ₀,₁(x) = φ_c,₁(x)`. |
| 2 | `gaussianReal_withDensity_esscher` | Measure level: tilting `N(0,1)` by the Esscher density gives exactly `N(c,1)` — mean shift `c`, variance fixed. The static (single-Gaussian) Girsanov theorem. |
| 3 | `map_withDensity_comp` | Pushforward commutes with a density factoring through the map: `(P.withDensity (g∘W)).map W = (P.map W).withDensity g`. Proved from `Measure.ext` + `setLIntegral_map`; **upstreamable to Mathlib**. |
| 4 | `hasLaw_esscher_tilt` | Girsanov for a random variable: if `W ~ N(0,1)` under `P`, then `W ~ N(c,1)` under `Q := P.withDensity(exp(c·W − c²/2))`. |
| 5 | `hasLaw_sub_const` | Recentring: `W − c ~ N(0,1)` under `Q`. |
| 6 | `esscherTilt_isProbabilityMeasure` | `Q` is a probability measure (the Esscher density is normalised). |
| 7 | **`BSCallHyp.exists_of_physical`** | **The capstone.** There exists a probability measure `Q` — the explicit Esscher tilt — under which `BSCallHyp` holds for the recentred driver. The risk-neutral hypothesis is now a *theorem*. |
| 8 | `bsTerminal_physical_eq_riskNeutral` | The conceptual heart: the Girsanov shift `c = (r − μ)·√T/σ` reprices the *same* asset with drift `μ → r`. `S_T` is invariant; only its drift changes. |

Economic reading: `c = −θ·√T` with market price of risk `θ = (μ−r)/σ`; the
recentred driver `W − c = W + θ√T` is the risk-neutral driver. This is the
slice of Girsanov tractable without the path-wise stochastic integral.

## Leap 2 — the genesis cascade: physical → EMM → pricing

`QuantFin/Foundations/GaussianGirsanov.lean` (same file).

Two composites wire the Girsanov construction into the prior pricing
artifacts — making `GaussianGirsanov` load-bearing rather than a dead leaf:

- `discounted_terminal_eq_S0_of_physical` — the constructed `Q` is a *genuine
  equivalent martingale measure*: `E_Q[e^{−rT}·S_T] = S₀` (the discounted
  asset is a `Q`-martingale). This is the defining property of an EMM, so the
  Esscher construction yields a real risk-neutral measure, not merely one
  under which the driver is standard normal.
- `bs_call_formula_of_physical` — the full chain `physical → Girsanov → Q → BS
  closed form`.

These are **additive bridges**: the pricing files keep `BSCallHyp` as their
clean abstraction, and Girsanov sits above them (the same pattern as
`PricingFromBrownian` / `BSCallHypFromBrownian`). The pricing files are *not*
refactored to depend on Girsanov — that would invert the dependency graph.
The spine is `physical measure → Girsanov → Q → BSCallHyp → pricing`.

## Leap 3 — multivariate: Margrabe's exchange option

`QuantFin/BlackScholes/ExchangeOption.lean`.

The first genuinely multivariate result. The exchange option pays
`max(S¹_T − S²_T, 0)`; its structural fact (Margrabe 1978) is that it depends
only on the ratio `S¹/S²`, lognormal at **effective volatility**
`σ² = σ₁² + σ₂² − 2ρσ₁σ₂`, so the two-asset problem collapses to a one-asset
Black-Scholes problem. It reuses the 1-D machinery rather than re-deriving —
the same structural-reduction discipline as `PowerCall`.

| Theorem | Content |
|---|---|
| `margrabe_variance_sub` | `Var[L₁ − L₂] = Var L₁ + Var L₂ − 2·cov(L₁,L₂)` via covariance bilinearity. First consumer of the covariance machinery shared with `Foundations/BivariateGaussian` — makes it load-bearing. |
| `margrabe_effective_variance` | Substituting `σ₁²T, σ₂²T, ρσ₁σ₂T` gives the effective variance `(σ₁²+σ₂²−2ρσ₁σ₂)·T`. |
| `exchange_payoff_eq_ratio` | `max(a−b,0) = b·max(a/b−1,0)` — the exchange payoff is `S²_T` times a vanilla call on the ratio. |
| `margrabe_eq_bsVGarman` | Margrabe **is** a `GarmanNormalForm` instance at `A=S¹₀, K=S²₀, DF=1`, effective vol `σ`. A multivariate option is the same formula `V = A·Φ(d₁) − K·DF·Φ(d₂)` as every BS-family price. |
| `margrabe_parity` | Exchange-option parity: `Margrabe(S¹,S²) − Margrabe(S²,S¹) = S¹ − S²` (the analog of put-call parity), via `Φ(x)+Φ(−x)=1`. |
| **`margrabe_price_via_call`** | **Price-level reduction.** In the `S²`-numeraire, the exchange option is `bs_call_formula` on the ratio: `S²₀·E_Q[max(R_T − 1, 0)] = margrabePrice`. |

The price-level result takes `BSCallHyp` for the *ratio* `R = S¹/S²` — exactly
the abstraction `bs_call_formula` takes for any underlying. Grounding that
primitive from a joint two-GBM model (via the `S²`-numeraire change of
measure) is the Margrabe-analog of leap 1, and is left as the same kind of
separate deeper result that `BSCallHyp` itself was until leap 1 derived it.

## The honest abstraction boundary

Across leaps 1 and 3 there is one consistent, deliberately-drawn line: a
pricing hypothesis (`BSCallHyp`, or `BSCallHyp` for the ratio) may be taken as
a primitive at the level the whole library operates, and the *deepest*
grounding of that primitive from a Brownian motion / a joint model is a
distinct, harder result. Leap 1 is exactly that grounding for the 1-D
`BSCallHyp`. This boundary is flagged in every relevant docstring; no
hypothesis-form theorem is committed unless its hypotheses are discharged in
the same arc or are the standard library-level pricing primitive.

## What's gated (leap 4 and the deeper groundings)

The remaining frontier shares a single prerequisite: **increment-independence
/ gaussian-vector structure extracted from `IsPreBrownian`**.

- **Leap 4 — path-wise Itô.** The L² Wiener integral for deterministic
  integrands already exists (`Foundations/WienerIntegralL2.lean`:
  `wienerIntegralLp`, `wiener_assembly_isometry`). The gap is the *adapted*
  (random) integrand — the actual Itô integral — and its isometry, which need
  increment independence (`E[ΔBₖΔBⱼ] = E[ΔBₖ]E[ΔBⱼ] = 0`). `BrownianQuadratic-
  Variation` proves `E[ΔB²]=t−s` and `E[ΔB]=0` but does *not* encode
  independence; that lives in `IsPreBrownian` (Degenne's package, whose
  stochastic integral is WIP upstream).
- **Margrabe `BSCallHyp`-grounding** — the ratio's risk-neutral lognormality
  from a joint two-GBM model needs the same gaussian-vector machinery.

These are honest dedicated builds, not bolt-ons. The cornerstone they unblock
(the Itô isometry, and the full Itô integral) is what would also clear the
~12 Itô-gated `reduced_core`s in [`coverage.md`](coverage.md).
