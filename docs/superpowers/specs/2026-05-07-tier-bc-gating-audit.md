# Tier B/C Gating Audit

This document enumerates, for each Tier B and Tier C theorem, the specific Mathlib
infrastructure that is missing at toolchain `v4.18.0`. The intent is to document
*precisely* what would need to be built upstream (or what could be axiomatized in a
faithful way) before each entry could be promoted from `reduced_core` to `full`.

This is the honest deliverable for Tier B/C in this artifact: not pretend proofs,
but a concrete map of where the work lies.

## Tier B — Brownian Motion Construction Required

All Tier B entries require a Mathlib-grade Brownian motion. The Mathlib community
has been working on this for years. The current state in `v4.18.0`: no
canonical `MeasureTheory.BrownianMotion` definition exists.

What is missing:

- A canonical `BrownianMotion : ℝ≥0 → Ω → ℝ` whose finite-dimensional distributions
  are Gaussian with covariance `min(s, t)`, on a constructed (e.g. canonical Wiener)
  measure space.
- Continuity of paths (Kolmogorov continuity theorem, with explicit Hölder
  exponent < 1/2).
- Strong Markov property w.r.t. its natural filtration.

### B.1 BM is a martingale (`bm-prop-5.1.2`)

- File: `benchmarks/brownian_motion.json`, entry `bm-prop-5.1.2`.
- Need: BM as a random process with `Martingale B 𝓕 P`. Currently a structure
  axiomatizing the martingale property as a field.
- Mathlib gap: no constructed BM. Once BM is constructed, the martingale property
  for the natural filtration follows directly from independent Gaussian increments
  via `Martingale.condExp_ae_eq` + `IndepFun.condExp_eq_const`.

### B.2 B²ₜ − t is a martingale (`bm-thm-5.1.4`)

- File: `benchmarks/brownian_motion.json`, entry `bm-thm-5.1.4`.
- Need: BM + Itô calculus level-1 (just second-moment computation).
- Mathlib gap: no constructed BM. With BM, the proof uses
  `Var(B_{t+s} − B_t) = s` and `E[B_t² | 𝓕_s] = E[(B_t − B_s + B_s)² | 𝓕_s]`
  expansion; compose with `condExp_mul_of_stronglyMeasurable_left`.

### B.3 Wald exponential `exp(αB_t − α²t/2)` is a martingale (`bm-thm-5.1.5`)

- File: `benchmarks/brownian_motion.json`, entry `bm-thm-5.1.5`.
- Need: BM, MGF of Gaussian (Mathlib has this for `gaussianReal`).
- Mathlib gap: no constructed BM. With BM, proof uses
  `mgf_gaussianReal` and tower-property style aggregation across increments.

### B.4 Reflection principle (`bm-thm-5.1.7`)

- File: `benchmarks/brownian_motion.json`, entry `bm-thm-5.1.7`.
- Need: BM + strong Markov property.
- Mathlib gap: strong Markov for BM. Construction-pending.

### B.5 Hölder regularity (`bm-thm-5.3.2`)

- File: `benchmarks/brownian_motion.json`, entry `bm-thm-5.3.2`.
- Need: Kolmogorov's continuity theorem.
- Mathlib gap: there are partial PRs for Kolmogorov continuity but no canonical
  Mathlib `kolmogorov_continuity_theorem` at `v4.18.0`.

### B.6 Nowhere differentiability (`bm-thm-5.3.5`)

- File: `benchmarks/brownian_motion.json`, entry `bm-thm-5.3.5`.
- Need: BM + measure-theoretic argument over an uncountable union (delicate).
- Mathlib gap: BM, plus a measurable-set version of the differentiability complement.
  Research-grade in formalization.

### B.7 Strong Markov for BM (`bm-cor-5.3.4`)

- File: `benchmarks/brownian_motion.json`, entry `bm-cor-5.3.4`.
- Need: BM + general strong Markov for continuous-path Markov processes.
- Mathlib gap: strong Markov framework for continuous-time. Partial work in
  `MeasureTheory.Strongly_measurable_stoppedProcess` for discrete time.

### B.8 / B.9 Quadratic variation of BM (`bm-rmk-5.1.6-square`, `bm-rmk-5.1.6-exp`)

- File: `benchmarks/brownian_motion.json`, entries `bm-rmk-5.1.6-square` and
  `bm-rmk-5.1.6-exp`.
- Need: BM, quadratic-variation framework, dyadic-partition convergence.
- Mathlib gap: no quadratic-variation framework for continuous processes.

### B.10 Continuous-time martingale convergence on `[0, T]` (`sc-thm-6.1.1`)

- File: `benchmarks/stochastic_calculus.json`, entry `sc-thm-6.1.1`.
- Need: continuous-time L² martingale theory.
- Mathlib gap: discrete-time L² martingales are present; continuous-time is
  partial. The benchmark statement is a continuous-path L² convergence.

### B.11 Brownian motion as Gaussian process characterization

- File: `benchmarks/brownian_motion.json` — implicit in several entries (e.g.
  `bm-prop-5.1.2`).
- Need: Gaussian process framework with covariance kernel.
- Mathlib gap: `gaussianReal` is the 1D Gaussian, multivariate Gaussian is partial,
  Gaussian processes (over uncountable index sets) are not yet present.

## Tier C — Stochastic Integral Layer Required

All Tier C entries require Tier B plus the stochastic-integral layer (Itô
integral against BM). At `v4.18.0`, Mathlib has neither.

What is missing:

- The Itô integral `∫₀^t H_s dB_s` for `H` predictable, locally L²(BM).
- Itô isometry: `E[(∫₀^t H_s dB_s)²] = E[∫₀^t H_s² ds]`.
- Itô's formula in 1D, time-dependent, and 2D.
- Stochastic differential equation (SDE) existence/uniqueness under Lipschitz
  coefficients.
- Girsanov's theorem (change of measure).
- Martingale representation theorem.

### C.1 Itô isometry (`sc-thm-6.2.5`)

- File: `benchmarks/stochastic_calculus.json`, entry `sc-thm-6.2.5`.
- Need: stochastic integral; isometry follows from L² construction.

### C.2 Itô process quadratic variation (`sc-thm-7.4.5`)

- File: `benchmarks/stochastic_calculus.json`, entry `sc-thm-7.4.5`.
- Need: stochastic integral, quadratic variation for general semimartingales.

### C.3 Itô's formula 1D (`sc-thm-7.1.1`)

- File: `benchmarks/stochastic_calculus.json`, entry `sc-thm-7.1.1`.
- Need: stochastic integral, second-order Taylor expansion with remainder
  controlled in L²(quadratic variation).

### C.4 Itô's formula time-dependent (`sc-thm-7.1.2`)

- File: `benchmarks/stochastic_calculus.json`, entry `sc-thm-7.1.2`.
- Need: 1D Itô + chain rule for `f(t, X_t)`.

### C.5 Itô's formula 2D (`sc-thm-7.5.2`)

- File: `benchmarks/stochastic_calculus.json`, entry `sc-thm-7.5.2`.
- Need: multi-dimensional stochastic integral, joint quadratic variation.

### C.6 Lévy's martingale characterization (`sc-thm-9.1.1`)

- File: `benchmarks/stochastic_calculus.json`, entry `sc-thm-9.1.1`.
- Need: continuous local martingales, quadratic variation = t identifies BM.

### C.7 Novikov's condition (`sc-thm-9.1.8`)

- File: `benchmarks/stochastic_calculus.json`, entry `sc-thm-9.1.8`.
- Need: stochastic exponential, exponential-martingale criteria.

### C.8 Girsanov's theorem (`gir-thm-9.1.7`, `gir-thm-9.1.8`)

- File: `benchmarks/girsanov_finance.json`, entries `gir-thm-9.1.7`, `gir-thm-9.1.8`.
- Need: change-of-measure framework for SDEs, Radon–Nikodym derivatives in
  continuous time.

### C.9 Black–Scholes PDE / call price formula

- Files: `benchmarks/girsanov_finance.json`, entry `gir-bs-call-formula`,
  `benchmarks/stochastic_calculus.json`, entry `sc-bs-pde`.
- Need: Itô's formula (time-dependent), Feynman–Kac, lognormal SDE solution.

### C.10 SDE existence / uniqueness (`sc-thm-9.2.1`)

- File: `benchmarks/stochastic_calculus.json`, entry `sc-thm-9.2.1`.
- Need: stochastic integral, Picard iteration in L².

### C.11 Martingale representation theorem (`gir-thm-9.3.4`)

- File: `benchmarks/girsanov_finance.json`, entry `gir-thm-9.3.4`.
- Need: stochastic integral, Brownian-filtration representation. Research-grade.

### C.12 Strong Markov for general processes (`mc-thm-1.2.11`)

- File: `benchmarks/markov_chains.json`, entry `mc-thm-1.2.11`.
- Need: stopping-time machinery for general state-space (continuous-time Markov
  framework). At v4.18.0 Mathlib has partial pieces in
  `Probability.Process.Stopping`; the textbook statement quantifies over
  general stopping times for a general Markov process.

### C.13 Continuous-time Markov + Poisson process theorems

- Files: `benchmarks/poisson_processes.json` entries `pp-prop-3.3.6`,
  `pp-thm-3.3.9`, `pp-thm-3.3.10` (interarrivals iid Exp, superposition,
  thinning).
- Need: continuous-time counting-process framework with explicit
  inter-arrival representation.
- Mathlib gap: `poissonMeasure` exists for `ℕ`-valued Poisson r.v.; the
  process-level definition (with inter-arrival times) and the related
  superposition/thinning theorems are not in Mathlib.

### C.14 Feynman–Kac for the heat equation (`sc-thm-8.2.5`)

- File: `benchmarks/stochastic_calculus.json`, entry `sc-thm-8.2.5`.
- Need: stochastic integral, time-dependent Itô, expectation-of-functional
  formula for SDE solutions.

### C.15 Continuous martingale theorems (`cm-thm-4.3.7`, `cm-thm-4.3.9`, `cm-thm-4.3.10`)

- File: `benchmarks/continuous_martingales.json`.
- Need: continuous-time martingale theory (Doob–Meyer decomposition,
  uniformly-integrable martingales, optional stopping).

## What Could Be Done Without Building Tier B/C

1. **Tier A backlog.** Real proofs of Tier A theorems still pending: conditional
   Jensen (`ce-prop-2.1.11-jensen`), Doob L^p (`mart-thm-2.4.6`), sum of
   exponentials (`pp-thm-3.3.8`), min of exponentials (`dist-exp-min`),
   multivariate Gaussian theorems (`dist-thm-B.1.2-marginal`,
   `dist-thm-B.1.3-conditional`), Markov-chain convergence cluster
   (`mc-thm-1.3.12`, `mc-thm-1.4.25`, `mc-thm-1.4.40`), Birkhoff ergodic
   theorem (`mc-thm-1.4.32`), FTAP for finite markets (`mart-thm-2.6.7`),
   path-factorization (`mc-thm-1.1.2`).

2. **Mathlib upstream contributions.** The most upstream-eligible Tier A
   targets are conditional Jensen (Mathlib has it as a TODO in two files) and
   Doob L^p (also a Mathlib TODO). Landing those upstream gives the artifact a
   tangible Mathlib citation.

3. **Brownian-motion construction.** A canonical `BrownianMotion` in Mathlib
   would unlock all 11 Tier B entries simultaneously. This is the pivotal
   upstream contribution for stochastic-process formalization.

4. **Itô integral.** Once BM is in Mathlib, the Itô integral construction
   (Daniell-Kolmogorov + simple-process L² closure) unlocks Tier C.

## How to Refresh This Audit

```bash
python3 -m python.coverage_report
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/<file>.json --config hybrid_verify.toml --timeout 240
```

When Mathlib master adds Brownian motion or the Itô integral, revisit Tier B
or Tier C respectively and promote the entries that have become wrappable.
