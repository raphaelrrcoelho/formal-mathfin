# Formally Verified Quant Finance in Lean 4

168 fully-derived theorems across 9 categories of mathematical finance, plus 24 library wrappers and 16 upstream-gated reduced cores. Every full derivation is `#print axioms`-clean: depends only on `[propext, Classical.choice, Quot.sound]`.

This is a Lean 4 library of quant-finance theorems — Black-Scholes / Black-76 / Bachelier, binomial trees, fixed income, portfolio theory (Markowitz / CAPM / two-fund), performance ratios (Sharpe / Sortino / Kelly), and coherent risk measures (VaR / CVaR axioms). Built on Mathlib with no Itô / Girsanov dependence; everything follows from gaussian MGF, completing-the-square, put-call parity, and Mathlib's existing probability framework.

## Status

| | count |
|---|---|
| total theorems | 208 |
| delivery-ready | **192** |
| ↳ full derivations | 168 |
| ↳ library wrappers | 24 |
| reduced cores (upstream-gated) | 16 |
| placeholders | 0 |

See [`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md) for the per-theorem audit and [`QUANTFIN_ROADMAP.md`](QUANTFIN_ROADMAP.md) for what's next.

## What's covered

| Category | Module | Headline results |
|---|---|---|
| **Black-Scholes** | `BlackScholes/` | Call, put, digital (cash + asset) formulas + parity; full Greek matrix (δ, γ, vega, θ, ρ, vanna, volga, ψ); BS-Merton with dividends; Garman-Kohlhagen FX; implied vol uniqueness; PDE forward direction; strike Greeks (∂_K, ∂²_K); static price bounds; box-spread arbitrage; lognormal moments; variance swap fair strike. |
| **Bachelier** | `BlackScholes/Bachelier{,Greeks}.lean` | Arithmetic-BM option pricing with the truncated-mean primitive; full first-order Greeks. |
| **Asian options** | `BlackScholes/AsianInequality.lean` | AM-GM (2-elt + n-elt equal-weight); two-date geometric ≤ arithmetic Asian payoff bound. |
| **Futures (Black-76)** | `Futures/` | Black-76 formula via zero-drift specialization + full Greek matrix. |
| **Binomial trees** | `Binomial/` | Single-period replication; multi-period backward induction; American options (Snell envelope); CRR convergence (variance, drift quotient + n-form). |
| **Fixed income** | `FixedIncome/` | ZCB price + duration + convexity; coupon bond pricing + YTM monotonicity; annuity geometric-series closed form; forward / spot rate consistency; first-order + second-order Redington immunization; yield-curve bootstrap; reduced-form credit (constant-hazard survival + spread = hazard). |
| **Portfolio theory** | `Portfolio/` | Two-asset Markowitz (completing-the-square); n-asset Markowitz (Finset double sum, diagonal, iid diversification, PSD bound); CAPM (β + portfolio linearity); two-fund separation (CML equation + Sharpe invariance). |
| **Performance ratios** | `Performance/` | Sharpe (scale invariance + √T scaling); Sortino; Treynor; Information ratio; tracking-error decomposition; Kelly criterion (FOC + horizon-myopia + fraction bounds + sign analysis). |
| **Risk measures** | `RiskMeasures/` | Gaussian VaR / CVaR closed forms; coherent axioms (translation, homogeneity, monotonicity, subadditivity); joint-stdev triangle inequality; VaR/CVaR additivity at ρ=1. |

## Worked example: BS call delta via the magic identity

The clean closed form `∂_S V = Φ(d₁)` falls out by chain rule on each piece, with the magic identity `S·ϕ(d₁) = K·e^{-rτ}·ϕ(d₂)` killing the residual `∂_S d_i` contributions:

```lean
-- HybridVerify/BlackScholes/PDE.lean
lemma hasDerivAt_bsV_S {K r σ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    {S τ : ℝ} (hS : 0 < S) (hτ : 0 < τ) :
    HasDerivAt (fun s => bsV K r σ s τ) (Phi (bsd1 S K r σ τ)) S := by
  -- Chain rule on S·Φ(d₁) and K·e^{-rτ}·Φ(d₂):
  have h_d1_S := hasDerivAt_bsd1_S (r := r) hK hσ hτ hS
  have h_d2_S := hasDerivAt_bsd2_S (r := r) hK hσ hτ hS
  have h_Phi_d1 := (hasDerivAt_Phi (bsd1 S K r σ τ)).comp S h_d1_S
  have h_Phi_d2 := (hasDerivAt_Phi (bsd2 S K r σ τ)).comp S h_d2_S
  have h_V := (hasDerivAt_id S).mul h_Phi_d1
              |>.sub (h_Phi_d2.const_mul (K * Real.exp (-(r * τ))))
  -- Collapse the surviving ∂_S d_i terms via the magic identity:
  have h_bs := bs_identity (r := r) hS hK hσ hτ
  ...; field_simp; linear_combination -h_bs
```

The same `bs_identity` collapse drives delta, gamma, theta, vega, rho, and the higher-order Greeks (vanna / volga). The PDE forward direction `∂_τ V = r S · ∂_S V + ½ σ² S² · ∂²_S V - r V` is the same identity again on a different combination.

See [`Examples.lean`](lean/HybridVerify/Examples.lean) for a curated tour of five representative proofs (BS delta, Markowitz min-variance, gaussian VaR subadditivity, Kelly criterion, variance swap fair strike).

## Repository layout

```
lean/                           Lake project, Mathlib pinned to f23306121184
├── HybridVerify.lean             umbrella (imports every submodule)
├── HybridVerify/
│   ├── Foundations/              Probability primitives (gaussian, BM, martingales, Wiener integral)
│   ├── BlackScholes/             BS family + Bachelier + Asian + lognormal + variance swap
│   ├── Futures/                  Black-76
│   ├── Binomial/                 Binomial / CRR / American
│   ├── FixedIncome/              ZCB, coupon bonds, immunization, bootstrap, credit
│   ├── Portfolio/                Markowitz, CAPM, two-fund
│   ├── Performance/              Sharpe / Sortino / Treynor / IR / Kelly
│   └── RiskMeasures/             VaR/CVaR + coherent axioms + additivity
├── lakefile.lean
└── lean-toolchain                4.30.0-rc1

benchmarks/                     JSON theorem files (11 chapters of stochastic-processes textbook,
                                  with mathematical_finance.json the centerpiece — 143 entries)

python/                         Multi-backend verifier (Lean / Isabelle / SymPy)
docker/                         Pinned reproducibility image
tests/                          pytest regression on routing + faithfulness status
```

A benchmark theorem with a non-trivial proof imports the corresponding `HybridVerify.<Section>.<Module>` and re-exports the named lemma in 5–25 lines. Trivial library wrappers stay inline in the JSON.

## Quick start

Pull the prebuilt image (~3 min) instead of rebuilding (~50 min):

```bash
docker compose -f docker/docker-compose.yml pull verify
```

Verify all benchmarks in a chapter:

```bash
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/mathematical_finance.json -v --timeout 120
```

Static coverage report:

```bash
docker compose -f docker/docker-compose.yml run --rm --entrypoint python3 verify -m python.coverage_report
```

Build only the Lean library (no verifier):

```bash
docker compose -f docker/docker-compose.yml run --rm --entrypoint bash verify -lc 'cd lean && lake build'
```

Router regression tests (formal-only enforcement, faithfulness-status presence):

```bash
docker compose -f docker/docker-compose.yml run --rm --entrypoint python3 verify -m pytest tests/test_router.py -q
```

## Reproducibility

The verify Docker image pins:

- Lean toolchain `4.30.0-rc1`
- Mathlib at commit `f23306121184`
- Remy Degenne's `brownian-motion` library at commit `16d15eb42c`
- Isabelle 2025-2 with `HOL-Probability` prebuilt

Every `full` theorem is checked with `#print axioms`; the only axioms allowed are the three standard Mathlib axioms: `[propext, Classical.choice, Quot.sound]`.

## What's not done (yet)

The 16 remaining `reduced_core` theorems are upstream-gated:

- **Itô calculus** (4 Girsanov + ~8 stochastic-calculus theorems including Itô's lemma, time-dependent Itô, Lévy's martingale characterization, SDE existence): Mathlib does not yet ship the Itô integral. The project will revisit when it lands.
- **Continuous-time Poisson processes** (3 theorems: interarrival exponential, superposition, thinning): Mathlib has only the discrete `PoissonPMF`.
- **Fine BM path machinery** (3 BM pathology theorems: reflection principle, nowhere-differentiability, law of iterated logarithm).

## Related upstream contributions

Drafted as part of this project:

- `gaussianReal_zero_one_Iic_neg`, `gaussianReal_zero_one_Ioi_toReal`, `exp_mul_gaussianPDFReal_zero_one`, `integral_exp_mul_gaussianPDFReal_zero_one_Ioi` (standard normal tail + completing-the-square): drafted as a Mathlib PR.
- `IsFilteredPreBrownian.squareSubTime_isMartingale`, `IsFilteredPreBrownian.waldExponential_isMartingale` (the two textbook BM martingales): drafted as a contribution to Remy Degenne's `brownian-motion` library.

## References

Saporito, *Stochastic Processes* (textbook chapter coverage, primary source).
Hull, *Options, Futures, and Other Derivatives*. Bodie / Kane / Marcus, *Investments*. Fabozzi, *Fixed Income Mathematics*. McNeil / Frey / Embrechts, *Quantitative Risk Management*. Demeterfi / Derman / Kamal, *More Than You Ever Wanted to Know About Volatility Swaps* (1999). Artzner / Delbaen / Eber / Heath, *Coherent Measures of Risk* (1999). Kelly, *A New Interpretation of Information Rate* (1956). Tobin, *Liquidity Preference as Behavior Towards Risk* (1958). Sharpe (1965), Treynor (1965), Sortino-van der Meer (1991), Grinold-Kahn (1999). Black-Scholes (1973), Merton (1973), Black (1976), Bachelier (1900), Cox-Ross-Rubinstein (1979).

## License

Apache 2.0, per the headers on each source file.
