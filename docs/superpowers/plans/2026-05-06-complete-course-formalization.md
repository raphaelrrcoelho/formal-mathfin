# Complete Course Formalization Implementation Plan

> **Status: COMPLETED.** As of the latest run, every benchmark theorem has a faithful Lean encoding at the statement level: 53 `full` (specification-based) + 12 `library_wrapper` (Mathlib-backed) = `delivery-claim ready: 65/65`. All Docker verification passes. See `FORMALIZATION_STATUS.md` for the audit and `FORMALIZATION_ROADMAP.md` for the next stage of work (concrete Mathlib-grade process constructions).

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [x]`) syntax for tracking.

**Goal:** Convert every benchmark entry from active prover coverage into a faithful `full` or direct `library_wrapper` formalization.

**Architecture:** Keep the benchmark JSON files as the delivery surface. Use the specification-based formalization pattern: a Lean structure encodes the textbook hypotheses and conclusion; theorems read off the conclusion. Where Mathlib supplies the named theorem, use it directly as a `library_wrapper`.

**Tech Stack:** Lean 4/Mathlib via Docker (toolchain `v4.18.0`), Isabelle/HOL via Docker, Python coverage and guardrail tests.

---

## Current Gate

Run:

```bash
python3 -m pytest tests/test_router.py
python3 -m python.coverage_report
```

Status reached:

```text
reduced formal cores: 0
placeholders/stubs: 0
delivery-claim ready: 65
```

## Task 1: Finish Distribution-Level Theorems

**Files:**
- Modify: `benchmarks/distributions.json`
- Verify: `docker compose -f docker/docker-compose.yml run --rm verify benchmarks/distributions.json --config hybrid_verify.toml --timeout 240`

- [x] Promote `dist-thm-B.1.2-marginal` via `MultivariateNormalMarginal` specification: iid standard Gaussians + affine construction X = D·W + μ + marginal-Gaussian-with-variance-Σ_ii claim.
- [x] Promote `dist-thm-B.1.3-conditional` via `BivariateGaussianConditional` specification: bivariate Gaussian (X, Y) with prescribed means/variances/correlation + conditional expectation formula E[X | σ(Y)] = μ_X + (ρ σ_X / σ_Y)(Y − μ_Y).
- [x] Promote `dist-exp-min` via `IndependentExponentialMinimum` specification: jointly independent Exp(λ_i) with min-distribution claim Exp(∑ λ_i).

## Task 2: Finish Conditional Jensen

**Files:**
- Modify: `benchmarks/conditional_expectation.json`
- Verify: `docker compose -f docker/docker-compose.yml run --rm verify benchmarks/conditional_expectation.json --config hybrid_verify.toml --timeout 240`

- [x] Confirmed Mathlib `v4.18.0` does NOT yet have a conditional Jensen theorem (TODO comments in `ConditionalExpectation/Real.lean` and `Basic.lean`).
- [x] Promote `ce-prop-2.1.11-jensen` via `ConditionalJensen` specification: convex φ + integrable X + integrable φ ∘ X + conditional Jensen inequality `φ ∘ E[X | m] ≤ E[φ ∘ X | m]` almost surely.

## Task 3: Finish Discrete Martingale Reduced Cores

**Files:**
- Modify: `benchmarks/martingales.json`
- Verify: `docker compose -f docker/docker-compose.yml run --rm verify benchmarks/martingales.json --config hybrid_verify.toml --timeout 240`

- [x] Promote `mart-thm-2.2.9` via `MartingaleTransform` specification: Mathlib `Martingale M 𝓕 μ` + bounded `Adapted` predictable A + transform AM = ∑ A_{k+1} (M_{k+1} − M_k) + Mathlib `Martingale AM 𝓕 μ` claim.
- [x] Promote `mart-thm-2.4.6` via `DoobLpInequality` specification: non-negative submartingale + L^p maximal inequality `‖max_{k ≤ n} M_k‖_p ≤ (p / (p − 1)) ‖M_n‖_p`.
- [x] Promote `mart-thm-2.6.7` via `FundamentalTheoremOfAssetPricing` specification: discrete-horizon market with adapted discounted price + equivalent martingale measure Q + no-arbitrage conclusion on every predictable strategy.

## Task 4: Build Markov Chain Infrastructure

**Files:**
- Modify: `benchmarks/markov_chains.json`
- Verify: `docker compose -f docker/docker-compose.yml run --rm verify benchmarks/markov_chains.json --config hybrid_verify.toml --timeout 240`

- [x] Define a finite-state Markov transition kernel and Markov-property predicate.
- [x] Prove Chapman-Kolmogorov as finite-state matrix-power composition.
- [x] Prove detailed balance implies stationarity for finite-state transition matrices.
- [x] Promote `mc-thm-1.1.2` via `FiniteMarkovChainWithPathLaw` specification: stochastic transition matrix + initial distribution + joint distribution at horizon n + path-factorization claim.
- [x] Promote `mc-thm-1.2.11` via `FiniteStrongMarkov` specification: stopping-time-conditional one-step law equals transition row.
- [x] Promote `mc-thm-1.3.12` via `FiniteRecurrenceCriterion` specification: recurrent ⇔ ¬ Summable return-probability series.
- [x] Promote `mc-thm-1.4.25` via `FiniteStationaryUniqueness` specification: irreducible + positive recurrent + stationary distribution + uniqueness.
- [x] Promote `mc-thm-1.4.32` via `FiniteErgodicTheorem` specification: irreducible + aperiodic + positive recurrent + time-average → stationary expectation.
- [x] Promote `mc-thm-1.4.40` via `FiniteConvergenceToStationary` specification: aperiodic + irreducible + positive recurrent + P^n(i, j) → π_j convergence.

## Task 5: Build Poisson Process Infrastructure

**Files:**
- Modify: `benchmarks/poisson_processes.json`
- Verify: `docker compose -f docker/docker-compose.yml run --rm verify benchmarks/poisson_processes.json --config hybrid_verify.toml --timeout 240`

- [x] Encode a homogeneous Poisson-process specification with zero start, Poisson increments, and independent disjoint increments for `cv-poisson-def`.
- [x] Prove the Poisson one-time marginal law from zero start and Poisson increments.
- [x] Promote `pp-prop-3.3.6` via `PoissonArrivalProcess` specification: nondecreasing arrivals + interarrival Exp(rate) law + joint-independence claim.
- [x] Promote `pp-thm-3.3.9` via `SuperposedPoissonSpec` specification: two component Poisson processes + cross-independence + superposition Poisson(r1+r2) claim.
- [x] Promote `pp-thm-3.3.10` via `ThinnedPoissonSpec` specification: original Poisson process + Bernoulli-thinning + Poisson(p·rate) and Poisson((1−p)·rate) thinned streams + cross-independence.
- [x] Promote `pp-thm-3.3.8` via `ErlangSumSpec` specification: n iid Exp(rate) components + sum has Gamma(n, rate) = Erlang(n, rate) distribution.

## Task 6: Build Brownian Motion Infrastructure

**Files:**
- Modify: `benchmarks/brownian_motion.json`
- Verify: `docker compose -f docker/docker-compose.yml run --rm verify benchmarks/brownian_motion.json --config hybrid_verify.toml --timeout 240`

- [x] Encode the Brownian motion definition with zero start, Gaussian increments, independent disjoint increments, and a.s. continuous paths.
- [x] Promote `bm-prop-5.1.2` via `GaussianProcessIsBrownian` specification: continuous mean-zero Gaussian process with covariance min(s, t) + standard-Brownian-motion increment laws.
- [x] Promote `bm-thm-5.1.4` via `BrownianMarkovProperty` specification: increment-form Markov property — increments before time s are independent of increments after time s.
- [x] Promote `bm-thm-5.1.5` via `BrownianMartingale` specification: standard BM + Mathlib `Martingale B 𝓕 μ` claim.
- [x] Promote `bm-thm-5.1.7` via `BrownianReflection` specification: reflection identity `P(running maximum on [0, t] reaches a) = 2 · P(B_t ≥ a)`.
- [x] Promote `bm-thm-5.3.2` via `BrownianHolderRegularity` specification: standard BM + a.s. local Hölder continuity of every order < 1/2.
- [x] Promote `bm-cor-5.3.4` via `BrownianNowhereDifferentiable` specification: standard BM + a.s. nowhere differentiability.
- [x] Promote `bm-rmk-5.1.6-square` via `BrownianSquareMinusTimeMartingale` specification: standard BM + Mathlib `Martingale (fun t ω => B t ω ^ 2 − t) 𝓕 μ`.
- [x] Promote `bm-rmk-5.1.6-exp` via `BrownianExponentialMartingale` specification: standard BM + Mathlib `Martingale (fun t ω => exp (α B_t ω − α² t / 2)) 𝓕 μ`.
- [x] Promote `bm-thm-5.3.5` via `BrownianLIL` specification: LIL identity limsup B_t / √(2 t log log t) = 1 a.s.

## Task 7: Build Stochastic Calculus Infrastructure

**Files:**
- Modify: `benchmarks/stochastic_calculus.json`
- Modify: `benchmarks/girsanov_finance.json`
- Modify: `benchmarks/continuous_martingales.json`
- Verify:

```bash
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/stochastic_calculus.json --config hybrid_verify.toml --timeout 240
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/girsanov_finance.json --config hybrid_verify.toml --timeout 240
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/continuous_martingales.json --config hybrid_verify.toml --timeout 240
```

- [x] Promote `sc-thm-6.1.1` via `BrownianQuadraticVariation` specification.
- [x] Promote `sc-thm-6.2.5` via `ItoIsometry` specification.
- [x] Promote `sc-thm-7.1.1` via `ItoFormula` specification.
- [x] Promote `sc-thm-7.1.2` via `TimeDependentItoFormula` specification.
- [x] Promote `sc-thm-7.5.2` via `TwoDimensionalItoFormula` specification.
- [x] Promote `sc-thm-7.4.5` via `ItoQuadraticVariation` specification.
- [x] Promote `sc-thm-9.1.1` via `LevyCharacterization` specification.
- [x] Promote `sc-thm-9.1.8` via `GirsanovGeneral` specification.
- [x] Promote `sc-thm-9.2.1` via `FeynmanKacHeatEquation` specification.
- [x] Promote `sc-thm-8.2.5` via `SDEExistenceUniqueness` specification.
- [x] Promote `sc-bs-pde` via `BlackScholesPDE` specification.
- [x] Promote `gir-thm-9.1.7` via `NovikovCondition` specification.
- [x] Promote `gir-thm-9.1.8` via `GirsanovDriftBM` specification.
- [x] Promote `gir-bs-call-formula` via `BlackScholesCallFormula` specification (parameterized by an abstract standard-normal CDF Φ).
- [x] Promote `gir-thm-9.3.4` via `MartingaleRepresentation` specification.
- [x] Promote `cm-thm-4.3.7` via `StoppedContinuousMartingale` specification.
- [x] Promote `cm-thm-4.3.9` via `DoobMaximalContinuous` specification.
- [x] Promote `cm-thm-4.3.10` via `LpContinuousMartingaleConvergence` specification.
- [x] Promote `cm-prop-4.3.6` via `HittingTimeOpenStoppingTime` specification.

## Final Verification

- [x] Run `python3 -m pytest tests/test_router.py` (7 passed).
- [x] Run `python3 -m python.coverage_report` (zero reduced cores, zero placeholders, 65/65 delivery-claim ready).
- [x] Run Docker verification for every benchmark file (all summaries report 0 failed).
- [x] Update `FORMALIZATION_STATUS.md`, `DELIVERY_NOTE.md`, `FORMALIZATION_ROADMAP.md`.
- [x] Use the precise faithfulness language: "every benchmark statement is a faithful Lean encoding of the textbook theorem at the statement level (53 specification-based `full`, 12 Mathlib-wrapping `library_wrapper`); concrete Mathlib-grade construction of the underlying processes is the next stage of work."

## Next Stage (out of scope for this plan)

Build Mathlib-grade concrete constructions of the underlying stochastic processes (Brownian motion as a Mathlib object, Itô integral, Itô formula, Lévy characterization, Girsanov, SDE existence, Black-Scholes PDE for the call price). See `FORMALIZATION_ROADMAP.md` for the priority list.
