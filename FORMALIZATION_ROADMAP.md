# Formalization Roadmap

Goal: move from "active prover obligations type-check on faithful textbook statements" toward "real Lean derivations of textbook theorems."

The current audit is (post v4.30 migration + BM port + Strong Markov AFP wrap, 2026-05-09):

```text
65 benchmark statements
33 delivery-claim ready entries: 13 full + 20 library_wrapper
32 reduced formal cores
0 placeholders
0 active SymPy entries
```

Recent promotions (Tier A): `mart-thm-2.2.9` (martingale transform — A.3),
`ce-prop-2.1.11-jensen` (conditional Jensen with explicit subgradient — A.1),
`mart-thm-2.6.7` (FTAP ⇒ direction, leveraging the embedded martingale-transform
helper — A.12), `mc-thm-1.1.2` (Markov-chain path factorization, constructive
def — A.13), `dist-exp-min` (minimum of independent exponentials, survival-
function level — A.5), and `mc-thm-1.4.32` (Birkhoff/ergodic for Markov chains
via AFP `Ergodic_Theory.Ergodicity.birkhoff_theorem_AE` — A.9, library_wrapper).

**BM port (2026-05-09)**: the 3 Degenne placeholders were recovered without
the Degenne Lake dependency by leveraging upstream Mathlib at pin
`f23306121184`. `bm-thm-5.1.4` is now `library_wrapper` via Mathlib's
`HasIndepIncrements.indepFun_eval_sub`; `bm-thm-5.3.2` and `bm-prop-5.1.2`
are honest `reduced_core` structural encodings (Mathlib has the precondition
`IsKolmogorovProcess` and `IsGaussianProcess` but not yet the
Kolmogorov-Chentsov continuity theorem or the converse-direction wrapper
proof). See `FORMALIZATION_STATUS.md` § "BM port (2026-05-09)".

**Strong Markov AFP wrap (2026-05-09)**: `mc-thm-1.2.11` promoted from
`reduced_core` to `library_wrapper` via AFP
`Markov_Models.Discrete_Time_Markov_Process.lim_stream_strong_Markov` inside
the `discrete_Markov_process` locale. Wrapper builds in 1s against the
pre-built `Markov_Models` heap.

**Infrastructure: AFP install** (2026-05-07/08). `docker/Dockerfile.verify` now
pre-builds AFP `Ergodic_Theory`, `Markov_Models`, and `Stochastic_Matrices`
sessions on top of `HOL-Probability` (image delta ~2.0–2.5 GB,
~30–60 min build). `python/isabelle_backend.py` selects the session per
theorem (auto-detects AFP namespace imports, or set
`metadata.isabelle_session` explicitly). Recognized AFP namespaces:
`Ergodic_Theory`, `Markov_Models`, `Stochastic_Matrices`, `Perron_Frobenius`,
`Jordan_Normal_Form`, `Coinductive`, `Gauss_Jordan_Elim_Fun`. `Stochastic_Matrices`
is wired but **not yet exercised** — the next Docker rebuild lands it. See
`docker/AFP_NOTES.md` for authoring patterns and the full list of probed AFP
lemmas (including `stationary_distribution_unique`).

Tier A targets remaining: A.2 (Doob L^p, **library-blocked 2026-05-08** —
exhaustive web/AFP/Mathlib audit found NO formal version of this theorem in
any source (Mathlib master, in-flight Mathlib PRs, AFP `Doob_Convergence`,
AFP `Martingales`, AFP `DiscretePricing`, HOL-Probability core, or
`RemyDegenne/brownian-motion`). The Mathlib martingale specialist's
`brownian-motion` blueprint outlines `lem:doob_Lp_countable` with the same
proof strategy we used (layer cake → L^1 maximal → Fubini → Hölder) but
has not formalized it. There is no Lean↔Isabelle proof-transport mechanism
that would let us wrap an Isabelle proof. We have 10 helper lemmas verified
against Mathlib v4.18.0 in `docs/superpowers/sketches/doob_lp_v1.lean`
(`runMax`, `runMax_nonneg`, `runMax_measurable`,
`runMax_stronglyMeasurable`, `layer_meas_bound`,
`lintegral_runMax_rpow_eq_layer`, `layer_integrand_bound`,
`A_le_layer_integral`, `lintegral_rpow_Ioc`,
`ofReal_setIntegral_eq_setLIntegral_ofReal`); the Fubini swap remains
the dominant cost on the path to a faithful main proof. Status: stays
`reduced_core` until Mathlib lands `MeasureTheory.maximal_ineq_Lp` (or
Degenne's `lem:doob_Lp_countable` is formalized upstream); see
`docker/AFP_NOTES.md` for the full negative-finding audit), A.4 (sum of
exponentials,
**blocked**: no measure convolution / MGF uniqueness), A.6/A.7 (multivariate
Gaussian, **blocked**: no MV Gaussian construction), A.8 (`mc-thm-1.4.40`
convergence, **still blocked** — neither Mathlib nor AFP `Stochastic_Matrices`
packages a `lim P^n` / spectral-gap theorem; would need building on top of
AFP `Perron_Frobenius`), A.10 (`mc-thm-1.4.25` stationary uniqueness,
**ready-to-wrap pending Docker rebuild** — direct wrap of AFP
`stationary_distribution_unique`), A.11 (recurrence criterion, **deferred** —
needs limit z→1 bridging from `gf_G` to ∑P^n).

**Full Docker verification 2026-05-08** (post router/backend edits): all
65 benchmark theorems verify, 0 failed, 0 partial. `pytest tests/test_router.py`
green (7/7).

`reduced_core` here means one of two things:

1. **Algebraic / analytic core check.** A narrow real-analytic identity that backs the textbook theorem in spirit (e.g., the Wald exponential constant identity `exp(α²t/2) · exp(-α²t/2) = 1`).
2. **Lean specification structure.** A Lean structure that encodes the textbook hypotheses AND the textbook conclusion as fields. Any inhabitant satisfies the textbook claim by construction, but the structure does NOT derive the conclusion from foundational primitives. The "theorem" reads off the conclusion via `:= h.conclusion_field`.

Both are honest as `reduced_core` and useful as documentation. Neither is `full` — that requires a real derivation.

The next stage of work is to attack the achievable real proofs (Tier A below) and contribute the results upstream where possible.

## Three Tiers

The detailed roadmap is in `docs/superpowers/specs/2026-05-06-real-proof-tiers.md`.
The Tier B/C honest gating audit (what Mathlib infrastructure is missing for
each of those entries) is in `docs/superpowers/specs/2026-05-07-tier-bc-gating-audit.md`.

Summary:

### Tier A — real proofs achievable now, weeks per theorem

These don't need new infrastructure beyond Mathlib `v4.18.0`.

- Conditional Jensen's inequality (Mathlib has it as a TODO).
- Doob's L^p maximal inequality (also a Mathlib TODO).
- Discrete martingale transform.
- Sum of n iid Exp(λ) → Gamma(n, λ).
- Min of independent exponentials → Exp(∑ λ).
- Multivariate Gaussian definition with marginal/affine/conditional theorems.
- Finite-state Markov chain convergence to stationary (Perron–Frobenius), recurrence criterion, ergodic theorem.
- FTAP for finite-state finite-period markets.
- Path-factorization theorem for general (countable-state) Markov chains.

Real Mathlib contributions in scope: conditional Jensen, Doob L^p, multivariate Gaussian.

### Tier B — needs Brownian motion construction first, months of foundational work

These all reduce to "first build a Mathlib-grade Brownian motion."

- BM martingale property, B²−t martingale, Wald exponential.
- Reflection principle, Markov / strong Markov property.
- Hölder regularity (needs Kolmogorov continuity theorem).
- Nowhere differentiability.
- Gaussian-process characterization of BM.
- Quadratic variation of BM.
- Law of the iterated logarithm.

The Mathlib community has been working toward Brownian-motion construction for years. Following / contributing to that work is the realistic path.

### Tier C — needs the stochastic-integral layer (research-grade)

Requires Tier B plus Itô-integral construction (a thesis-level effort each).

- Itô isometry, Itô's formula (1D / time-dependent / 2D).
- Itô process quadratic variation.
- Lévy's martingale characterization of BM.
- Novikov's condition.
- Girsanov's theorem (any version).
- Feynman–Kac for the heat equation.
- SDE existence and uniqueness.
- Martingale representation theorem.
- Black-Scholes PDE / call price formula.

These are not achievable in the near term as Lean derivations. Keep the specifications as documentation of what a future Mathlib-grade construction needs to satisfy.

## Working Rules

- Do not mark `library_wrapper` unless active code invokes or directly wraps a named library theorem close to the benchmark statement.
- Do not mark `full` unless the formal proof is a real derivation. Spec-with-axiomatized-conclusion is `reduced_core`.
- Keep old CAS snippets only under `metadata.cas_reference.sympy`.
- After each promotion attempt, run `python3 -m pytest tests/test_router.py` and `python3 -m python.coverage_report` and Docker-verify the affected file.

## Guardrails

```bash
python3 -m pytest tests/test_router.py
python3 -m python.coverage_report
```

```bash
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/<file>.json --config hybrid_verify.toml --timeout 240
```

Before any public claim, check `python3 -m python.coverage_report` and use `delivery-claim ready` (i.e., `full + library_wrapper`), not the total theorem count.
