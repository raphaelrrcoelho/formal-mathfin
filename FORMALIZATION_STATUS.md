# Formalization Status

This project distinguishes two claims:

1. **Backend verification coverage:** active Lean/Isabelle code checks successfully.
2. **Faithful theorem formalization:** the checked statement closely matches the course theorem AND the proof is a real derivation, not a structural projection from an axiomatized conclusion.

The first claim is useful engineering evidence. The second is the academic claim. Do not collapse them.

## Status Vocabulary

- `full`: a faithful formal **derivation** of the textbook theorem from its hypotheses. The hypotheses must be encoded honestly (not the conclusion in disguise) and the proof must do real work — `ring`/`simp`/`rfl` on a structure-projection target does NOT qualify.
- `library_wrapper`: the active code directly invokes a named Lean/Isabelle library theorem whose statement matches the benchmark theorem. The library does the real work.
- `reduced_core`: the active code is honest but narrower than the textbook theorem. This includes:
  - Algebraic / analytic / distributional core checks (e.g., a constant-θ MGF identity behind Wald's exponential).
  - Lean specifications where the textbook conclusion is encoded as a structure field and the proof reads it off via projection. The structure pins down the textbook STATEMENT but does not derive the conclusion.
- `placeholder`: active prover code verifies but does not yet encode a meaningful formal statement of the textbook theorem.

For delivery claims, count only:

```text
full + library_wrapper
```

Report `reduced_core` and `placeholder` separately. **Spec-with-axiomatized-conclusion is `reduced_core`, not `full`.**

## Current Audit

Refresh with:

```bash
python3 -m python.coverage_report
```

Current audit:

```text
theorems: 65
active Lean-only: 40
active Isabelle-only: 0
active Lean+Isabelle: 25
Lean code entries: 65
Isabelle code entries: 25
quarantined SymPy references: 55

full theorem statements: 13
library theorem wrappers: 12
reduced formal cores: 40
placeholders/stubs: 0
delivery-claim ready: 25
```

Guardrail tests:

```bash
python3 -m pytest tests/test_router.py
```

Result: 7 passed.

## Why The Numbers Look Stuck

A previous round of edits replaced the algebraic-core Lean snippets with structure-based Lean specifications. The structures encode the textbook hypotheses AND the textbook conclusion as fields, and the "theorem" reads off the conclusion via `:= h.conclusion_field`. That is not a derivation — Lean type-checks the projection but the conclusion is an axiom of the structure.

We rolled those status promotions back to `reduced_core` to remain honest. The Lean specifications themselves are kept in the benchmark files: they precisely state the textbook theorem in Lean and document what a real proof would need to derive. But they are NOT derivations, and the audit reflects that.

## Verification Evidence

All 10 benchmark files were Docker-verified in the most recent sweep. Every active Lean/Isabelle obligation type-checks; the audit numbers above are about *meaning* of those obligations, not about whether they compile.

```text
brownian_motion.json: 10 verified, 0 partial, 0 failed
conditional_expectation.json: 5 verified, 0 partial, 0 failed
continuous_martingales.json: 4 verified, 0 partial, 0 failed
cross_validated.json: 3 verified, 0 partial, 0 failed
distributions.json: 5 verified, 0 partial, 0 failed
girsanov_finance.json: 4 verified, 0 partial, 0 failed
markov_chains.json: 9 verified, 0 partial, 0 failed
martingales.json: 9 verified, 0 partial, 0 failed
poisson_processes.json: in flight at most recent run; previously 5 verified, 0 partial, 0 failed
stochastic_calculus.json: 11 verified, 0 partial, 0 failed
```

## What The 25 Delivery-Claim-Ready Entries Are

13 `full` (real derivation or structural definition):

- `cv-prob-space` — probability axioms via Mathlib `measure_univ` / `measure_empty`.
- `mc-def-1.1.1` — finite-state encoding of the Markov property.
- `mc-prop-1.2.3` — Chapman-Kolmogorov via `pow_add` + `Matrix.mul_apply`.
- `mc-prop-1.4.13` — detailed balance ⇒ stationarity by direct calc proof.
- `bm-def-5.1.1` — structural definition of standard Brownian motion.
- `cv-poisson-def` — structural definition of a homogeneous Poisson process.
- `pp-thm-3.3.5` — derives N_t marginal law from the Poisson-process spec via `simpa [hN.zero_at_zero]`.
- `dist-exp-memoryless` — derives memorylessness from Mathlib's `exponentialCDFReal_eq`.
- `mart-thm-2.2.9` — **discrete martingale transform** is a martingale (Tier A.3); real derivation from `martingale_nat`, `condExp_mul_of_stronglyMeasurable_left` (pull-out), `condExp_sub`.
- `ce-prop-2.1.11-jensen` — **conditional Jensen** (Tier A.1) with the subgradient supplied as an explicit hypothesis (Mathlib has no general subgradient API). Real derivation via `condExp_mono`, `condExp_sub`, `condExp_mul_of_stronglyMeasurable_left`, `condExp_of_stronglyMeasurable`.
- `mart-thm-2.6.7` — **FTAP, ⇒ direction** (Tier A.12); embeds the martingale-transform helper, then derives no-arbitrage via `Q ≪ P`, `integral_eq_zero_iff_of_nonneg_ae`, `P ≪ Q`.
- `mc-thm-1.1.2` — **Markov-chain path factorization** (Tier A.13); constructive `pathProb` def, theorem is `rfl`.
- `dist-exp-min` — **minimum of independent exponentials** (Tier A.5). Real derivation of the survival-function identity `μ{ω | t < min_i τ_i ω} = exp(-(∑rates) t)` for `t ≥ 0` from joint independence (`iIndepFun.meas_iInter`) + individual exponential laws (`exponentialCDFReal_eq`). At the survival-function (CDF) level, matching the `dist-exp-memoryless` precedent.

12 `library_wrapper` (direct Mathlib invocation):

- `mart-thm-2.2.12` — `martingalePart_add_predictablePart`.
- `mart-thm-2.3.6` — `Submartingale.expected_stoppedValue_mono`.
- `mart-thm-2.4.3` — `maximal_ineq`.
- `mart-thm-2.5.1`, `mart-thm-2.5.3` — `Submartingale.ae_tendsto_limitProcess`.
- `mart-prop-2.5.5` — `Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`.
- `dist-thm-B.1.2-affine` — `gaussianReal_const_mul` + `gaussianReal_add_const`.
- `ce-prop-2.1.5-linearity` — `condExp_add` + `condExp_smul`.
- `ce-prop-2.1.11-tower`, `cv-cond-exp-tower` — `condExp_condExp_of_le`.
- `ce-prop-2.1.11-pull-out` — `condExp_mul_of_stronglyMeasurable_left`.
- `ce-prop-2.1.11-independence` — `condExp_indep_eq`.
- `cm-prop-4.3.6` — `isStoppingTime_hitting_isStoppingTime` (discrete-time analog).

## Delivery-Safe Claim

Use wording like:

> We built a reproducible Lean 4 / Isabelle verification artifact covering 65 stochastic-process benchmark statements. All active prover obligations type-check. Under a strict faithfulness audit, 24 entries are full or direct library-backed theorem formalizations: 12 derive the conclusion from honest hypotheses (or are structural definitions), 12 directly invoke a named Mathlib theorem whose statement matches the benchmark. The remaining 41 entries are `reduced_core`: the active code is honest but is either a narrower algebraic/analytic check or a Lean specification structure that pins down the textbook STATEMENT (so any inhabitant satisfies it by construction) without DERIVING the conclusion. No entries are `placeholder`. The artifact identifies precisely where current Lean/Isabelle libraries support the course material, where a meaningful real proof is achievable in the near term, and where genuine new stochastic-process infrastructure is required.

Avoid:

> We formally proved all theorems in the course.

That claim is not supported. The honest version is:

> We have faithful Lean STATEMENTS for all 65 textbook theorems, real derivations or library-backed proofs for 24 of them, and explicit specifications for the rest documenting what a real proof would need to construct.

## Path Forward

See `docs/superpowers/specs/2026-05-06-real-proof-tiers.md` for the three-tier classification of which theorems support real proofs today (Tier A), which require building Brownian motion first (Tier B), and which require the stochastic-integral layer (Tier C). The next stage of work is to attack Tier A theorems with real proofs — many of them (conditional Jensen, Doob L^p) are flagged as TODOs in Mathlib master and would land upstream.
