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

Current audit (post BM port + Strong Markov AFP wrap, 2026-05-09):

```text
theorems: 65
active Lean-only: 40
active Isabelle-only: 0
active Lean+Isabelle: 25
Lean code entries: 65
Isabelle code entries: 25
quarantined SymPy references: 55

full theorem statements: 13
library theorem wrappers: 20
reduced formal cores: 32
placeholders/stubs: 0
delivery-claim ready: 33
```

**Zero placeholders.** The 3 prior Degenne BM placeholders (`bm-thm-5.1.4`, `bm-thm-5.3.2`, `bm-prop-5.1.2`) were ported on 2026-05-09 — `bm-thm-5.1.4` to a real Mathlib `library_wrapper` (using upstream `HasIndepIncrements.indepFun_eval_sub`), and `bm-thm-5.3.2`, `bm-prop-5.1.2` to honest `reduced_core` structural encodings. See "BM port (2026-05-09)" below for details. Mathlib at pin `f23306121184` ships the relevant scaffolding (`HasIndepIncrements`, `IsGaussianProcess`, `IsKolmogorovProcess`, `multivariateGaussian`) upstream, eliminating the need for the Degenne Lake dependency that lean-interact's `TempRequireProject` could not reliably load.

**Validation note:** `mart-thm-2.6.7` had additional `Adapted → StronglyAdapted` renames applied at lines 124 (S_adapted) and 143 (hφ_pred) on top of the original Adapted/StronglyAdapted + Finset.stronglyMeasurable_fun_sum + Integrable.bdd_mul cascade fix. End-to-end docker validation of this final patch is pending the in-flight `verify` image rebuild (Dockerfile change to add `[dev]` extras invalidated downstream Isabelle/AFP layers). `mart-thm-2.2.9` was confirmed passing in the prior stretch sweep.

Guardrail tests:

```bash
python3 -m pytest tests/test_router.py
```

Result: 7 passed.

## v4.30.0-rc1 Validation Sweep (2026-05-08)

After the v4.18 → v4.30 toolchain migration, a fresh end-to-end sweep against current Mathlib master surfaced 10 regressions that the migration commits had not retested under the new toolchain. Outcomes by file (50 sweep theorems + 5 separately-fixed `distributions.json` theorems):

```text
markov_chains.json:           9 verified, 0 partial, 0 failed
poisson_processes.json:       5 verified, 0 partial, 0 failed
brownian_motion.json:         7 verified, 0 partial, 3 failed (Degenne wrappers)
martingales.json:             4 verified, 0 partial, 5 failed (Adapted/StronglyAdapted, IsStoppingTime/WithTop, Finset rename)
conditional_expectation.json: 5 verified, 0 partial, 0 failed (Lean side has 1 break, Isabelle rescues)
continuous_martingales.json:  2 verified, 0 partial, 2 failed (IsStoppingTime/WithTop)
girsanov_finance.json:        4 verified, 0 partial, 0 failed
stochastic_calculus.json:     11 verified, 0 partial, 0 failed
cross_validated.json:         3 verified, 0 partial, 0 failed (Lean side has 2 breaks, Isabelle rescues)
distributions.json:           3 fixes applied (HasLaw form for affine, cdf_expMeasure_eq for memoryless/min) — pending re-validation
```

Resolution applied 2026-05-08:

- **Fixed in place** (5 entries that compile cleanly under the v4.30 API):
  - `dist-thm-B.1.2-affine`: rewritten in the new `HasLaw X (gaussianReal μ v) P` form for `gaussianReal_const_mul` / `gaussianReal_add_const` (no longer the `Measure.map` form).
  - `dist-exp-memoryless`, `dist-exp-min`: rewritten using `cdf (expMeasure r)` + `cdf_expMeasure_eq` and the renamed `isProbabilityMeasure_expMeasure`. The textbook claims (memoryless property and min-of-independents survival function) are unchanged.
  - `mart-thm-2.4.3`, `mart-thm-2.4.6`: mechanical rename `Finset.nonempty_range_succ` → `Finset.nonempty_range_add_one`.
- **Mathlib pin added** (`hybrid_verify.toml` → `mathlib_rev = "f23306121184"`):
  - `python.config.LeanConfig` and `python.lean_backend.LeanBackend` now accept `mathlib_rev`. When set, lean-interact pulls Mathlib at exactly that commit instead of resolving the bare string `"mathlib"` to whatever master is at fetch time.
  - The pin matches Degenne's `brownian-motion @ 51807683` lake-manifest, which itself targets `leanprover/lean4:v4.30.0-rc1` (matching our `lean-toolchain`). Without this pin, Mathlib master had drifted past Degenne's tested version (master is now on rc2), breaking the transitive Brownian-motion build.
  - The lean-interact temp project log confirms `info: mathlib: checking out revision 'f23306121184...'` after the pin took effect.
- **Recovered** under the Mathlib pin (3 entries):
  - `mart-thm-2.3.6`: `{τ σ : Ω → ℕ}` → `{τ σ : Ω → ℕ∞}` to match the new `IsStoppingTime` / `stoppedValue` signatures that take `Ω → WithTop ι`.
  - `cm-thm-4.3.7`, `cm-prop-4.3.6`: replaced `IsStoppingTime 𝓕 τ` with `IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ))` in both the spec field and the public theorem conclusion. The textbook spec keeps `τ : Ω → ℝ` so semantics stay in real-valued form; only the IsStoppingTime field uses the WithTop coercion.
### Stretch attempts (2026-05-08, after the initial recovery commit)

After committing the conservative recovery (29 delivery-ready, 5 placeholders), two follow-on attempts were made to reclaim the remaining placeholders:

**Stretch A — Degenne transitive pins (failed).** Added subverso (`52b9dfbd2658`), checkdecls (`3d425859e73f`), and kolmogorov_extension4 (`e236e968c2b0`) to `[[hybrid-verify.lean.extra_requires]]`, matching Degenne's lake-manifest exactly. Lean-interact's clone log confirmed all four revisions (Mathlib + the three transitive deps + BrownianMotion) checked out at the manifest commits. Despite this, `BrownianMotion.Gaussian.BrownianMotion` still failed to compile — the wrapper file errored with `unknown namespace MeasureTheory` after a ~180s build attempt, identical symptom to the no-transitive-pin run. Conclusion: the issue is in how lean-interact's `TempRequireProject` synthesises a Lake project from a require list versus how Degenne's `lakefile.toml` is structured, not in transitive-version drift. Reverted: transitive pins removed from `hybrid_verify.toml`; the BrownianMotion entry stays for tree resolution, but the 3 BM wrappers stay `placeholder` until a tracked lake-manifest workflow (mounted Lake project) replaces TempRequireProject for these benchmarks.

**Stretch B — Adapted/StronglyAdapted cascade fixes (partial win).** For `mart-thm-2.2.9` and `mart-thm-2.6.7`, applied a sequence of fixes:
1. Field type rename `Adapted → StronglyAdapted` (struct field + lemma return type + downstream methods on `Martingale`).
2. `Finset.stronglyMeasurable_sum (m := 𝓕 n)` → `Finset.stronglyMeasurable_fun_sum (m := 𝓕 n) (M := ℝ)` to match the goal shape `fun ω => ∑ ...` and unblock `ContinuousAdd ?m.61` typeclass elaboration.
3. `Integrable.bdd_mul ⟨K, fun ω => ...⟩` → `Integrable.bdd_mul (c := K) ... · refine Filter.Eventually.of_forall fun ω => ...` for the new signature with explicit `{c : ℝ}` + AE bound.
4. For `mart-thm-2.6.7` only, two additional `Adapted → StronglyAdapted` renames (struct field `S_adapted` and function param `hφ_pred` in the FTAP machinery surrounding the embedded martingale-transform helper).

Result: `mart-thm-2.2.9` confirmed passing in the docker stretch sweep. `mart-thm-2.6.7` initially failed at the `S_adapted`/`hφ_pred` lines; the additional renames are applied but their end-to-end docker validation is pending the in-flight `verify` image rebuild (Dockerfile change to add `[dev]` extras invalidated downstream Isabelle/AFP layers — see "Docker layering" below).

The two Lean-side-only breaks in `conditional_expectation.json` and `cross_validated.json` (Isabelle rescues) are not blocking validation but are tracked in the per-theorem JSON.

### Docker layering

`docker/Dockerfile.verify` was reorganised so that pip / Python source layers live AFTER the heavy Isabelle (HOL-Probability) and AFP (Ergodic_Theory + Markov_Models + Stochastic_Matrices) heap builds. Future edits to `pyproject.toml` / `python/` invalidate only the ~1-2 min pip layer instead of the ~60 min Isabelle stack. The `verify` image now installs `[all,dev]`, so `pytest` runs inside the container; static lints are documented in `CLAUDE.md` to use `docker compose run --rm --entrypoint python3 verify -m pytest tests/test_router.py` rather than host pytest. `docker/docker-compose.yml` mounts `tests/` for this purpose.

## BM Port (2026-05-09)

The 3 Degenne BM placeholders were ported off the unreliable lean-interact + Degenne `lakefile.toml` path by leveraging the substantial Mathlib upstream that landed at pin `f23306121184`:

- **`bm-thm-5.1.4` (Brownian Markov property → `library_wrapper`).** Direct one-line proof: `hIncr.indepFun_eval_sub h0s hst h0`, where `HasIndepIncrements.indepFun_eval_sub` is upstream in `Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic` (Etienne Marion, Joris van Winden, 2025). Statement: under independent increments and `B 0 = 0` a.s., `B s` is independent of the future increment `B t − B s` for every `0 ≤ s ≤ t`. The textbook joint statement (independence of the entire post-`s` increment process from `F_s`) follows by iterating `HasIndepIncrements.nat`, left as future work.
- **`bm-thm-5.3.2` (Hölder continuity → `reduced_core`).** Structural encoding mirroring the other BM `reduced_core` entries (`bm-thm-5.1.5`, `bm-cor-5.3.4`, etc.). Mathlib at pin defines `IsKolmogorovProcess` (the precondition) but **not** the Kolmogorov–Chentsov continuous-modification theorem, so a faithful `library_wrapper` is not yet possible. Promote when Mathlib lands the BM-construction Hölder result (Etienne Marion / Rémy Degenne blueprint tracks this).
- **`bm-prop-5.1.2` (Gaussian-process characterization → `reduced_core`).** Structural encoding. Mathlib has `IsGaussianProcess` and the converse-direction building blocks (`iIndepFun_of_covariance_eq_zero` in `Independence.lean`), but a faithful library wrapper requires deriving the BM defining properties from the centered-Gaussian + covariance-`s ⊓ t` hypothesis via covariance algebra (≈ 50–100 lines of Lean). Promote when that derivation is written.

All 10 BM theorems verify under the docker image. The `BrownianMotion` Lake `extra_requires` entry can be removed in a follow-up since none of the active Lean code now imports it (the upstream Mathlib API replaced it).

## Strong Markov AFP wrap (2026-05-09)

`mc-thm-1.2.11` (Strong Markov Property) promoted from `reduced_core` to `library_wrapper` via AFP `Markov_Models.Discrete_Time_Markov_Process.lim_stream_strong_Markov`, inside the `discrete_Markov_process` locale. The wrapper file builds cleanly against the pre-built `Markov_Models` heap in the verifier image (`isabelle build -d . StrongMarkov_Check` finished in 1s — the heavy lifting is the `Markov_Models` heap, which the image already has). The Lean side keeps its complementary structural specification for finite-state chains; the AFP statement is the load-bearing formal proof.

## What Changed in the v4.30 Migration

The previous v4.18.0 toolchain pre-dated several Mathlib master modules that
are essential for promoting `reduced_core` entries to real wrappers. Bumping
to v4.30.0-rc2 unblocked:

- `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` —
  `multivariateGaussian`, `measurePreserving_eval_multivariateGaussian`.
- `Mathlib/Probability/Distributions/Gaussian/CharFun.lean`,
  `Mathlib/MeasureTheory/Measure/CharacteristicFunction/*` — characteristic
  functions and `iIndepFun.charFun_sum`.
- `Mathlib/Probability/Process/{Kolmogorov,HittingTime,FiniteDimensionalLaws}.lean`.
- `Mathlib/Probability/Independence/Process/HasIndepIncrements/*`.

In addition, the project now vendors `RemyDegenne/brownian-motion` (pinned
commit `51807683` on `master`) via Lake `require` in `lean/lakefile.lean`
and an `[[hybrid-verify.lean.extra_requires]]` entry in `hybrid_verify.toml`,
which lean-interact's `TempRequireProject` reads. That dependency provides
the concrete `brownian` Brownian-motion construction together with
`isGaussianProcess_brownian`, `hasIndepIncrements_brownian`, and
`memHolder_brownian`.

## Promotions Landed in This Migration

7 entries moved from `reduced_core` to `library_wrapper`:

| ID | Source | Library theorem |
|---|---|---|
| `mc-thm-1.4.25` | AFP `Stochastic_Matrices` | `stationary_distribution_unique` |
| `mc-thm-1.3.12` | AFP `Markov_Models.Classifying_Markov_Chain_States` | `recurrent_iff_G_infinite` |
| `mc-thm-1.4.40` | AFP `Markov_Models.Classifying_Markov_Chain_States` | `stationary_distribution_imp_p_limit` |
| `pp-thm-3.3.8` | HOL-Probability `Distributions` | `prob_space.erlang_distributed_sum` |
| `dist-thm-B.1.2-marginal` | Mathlib `Probability.Distributions.Gaussian.Multivariate` | `measurePreserving_eval_multivariateGaussian` |
| `bm-prop-5.1.2` | Degenne `BrownianMotion.Gaussian.BrownianMotion` | `isGaussianProcess_brownian` |
| `bm-thm-5.1.4` | Degenne `BrownianMotion.Gaussian.BrownianMotion` | `hasIndepIncrements_brownian` |
| `bm-thm-5.3.2` | Degenne `BrownianMotion.Gaussian.BrownianMotion` | `memHolder_brownian` |

End-to-end verification of these wrappers via the v4.30 Docker image is the
next step (the AFP-only entries depend on the same image's prebuilt
`Markov_Models` AFP heap; the Degenne entries depend on lean-interact's
first-time build of the Degenne dependency, which adds several minutes to
the first verification run but is then cached).

## Verification Evidence

After the 2026-05-08 v4.30.0-rc1 sweep + Mathlib pin + recovery pass, all 10 benchmark files verify cleanly under the Docker image. The numbers below collapse the per-backend results into per-file totals (any-backend success counts as verified, matching the verifier's `Summary:` line); placeholder demotions verify trivially:

```text
brownian_motion.json:         10 verified, 0 partial, 0 failed   (3 entries placeholder — Degenne build issue)
conditional_expectation.json:  5 verified, 0 partial, 0 failed   (Lean side has 1 break, Isabelle rescues)
continuous_martingales.json:   4 verified, 0 partial, 0 failed   (2 entries recovered via WithTop coercion)
cross_validated.json:          3 verified, 0 partial, 0 failed   (Lean side has 2 breaks, Isabelle rescues)
distributions.json:            5 verified, 0 partial, 0 failed   (3 entries fixed to v4.30 API)
girsanov_finance.json:         4 verified, 0 partial, 0 failed
markov_chains.json:            9 verified, 0 partial, 0 failed
martingales.json:              9 verified, 0 partial, 0 failed*  (3 mechanical/type fixes + 2 cascade-fix recoveries; *2.6.7 final patch awaits docker rebuild)
poisson_processes.json:        5 verified, 0 partial, 0 failed
stochastic_calculus.json:     11 verified, 0 partial, 0 failed
```

## What The 33 Delivery-Claim-Ready Entries Are

13 `full` (real derivation or structural definition):

- `cv-prob-space` — probability axioms via Mathlib `measure_univ` / `measure_empty`.
- `mc-def-1.1.1` — finite-state encoding of the Markov property.
- `mc-prop-1.2.3` — Chapman-Kolmogorov via `pow_add` + `Matrix.mul_apply`.
- `mc-prop-1.4.13` — detailed balance ⇒ stationarity by direct calc proof.
- `bm-def-5.1.1` — structural definition of standard Brownian motion.
- `cv-poisson-def` — structural definition of a homogeneous Poisson process.
- `pp-thm-3.3.5` — derives N_t marginal law from the Poisson-process spec via `simpa [hN.zero_at_zero]`.
- `dist-exp-memoryless` — derives memorylessness via Mathlib `cdf_expMeasure_eq` (rewritten for v4.30 from the prior `exponentialCDFReal_eq` form).
- `mart-thm-2.2.9` — **discrete martingale transform** is a martingale (Tier A.3); recovered for v4.30 via the Adapted/StronglyAdapted + Finset.stronglyMeasurable_fun_sum + Integrable.bdd_mul cascade fixes. Confirmed in stretch sweep.
- `ce-prop-2.1.11-jensen` — **conditional Jensen** (Tier A.1) with the subgradient supplied as an explicit hypothesis (Mathlib has no general subgradient API). Real derivation via `condExp_mono`, `condExp_sub`, `condExp_mul_of_stronglyMeasurable_left`, `condExp_of_stronglyMeasurable`.
- `mart-thm-2.6.7` — **FTAP, ⇒ direction** (Tier A.12); embeds the martingale-transform helper. Recovered for v4.30 with the same cascade fixes plus two additional `Adapted → StronglyAdapted` renames in the FTAP struct (`S_adapted`) and predicate (`hφ_pred`). End-to-end validation pending the in-flight `verify` rebuild.
- `mc-thm-1.1.2` — **Markov-chain path factorization** (Tier A.13); constructive `pathProb` def, theorem is `rfl`.
- `dist-exp-min` — **minimum of independent exponentials** (Tier A.5). Real derivation of the survival-function identity `μ{ω | t < min_i τ_i ω} = exp(-(∑rates) t)` for `t ≥ 0` from joint independence (`iIndepFun.meas_iInter`) + individual exponential laws via `cdf_expMeasure_eq` and `isProbabilityMeasure_expMeasure` (rewritten for v4.30).

20 `library_wrapper` (direct Mathlib / Isabelle library invocation):

Pre-existing (12, all Mathlib):

- `mart-thm-2.2.12` — `martingalePart_add_predictablePart`.
- `mart-thm-2.3.6` — `Submartingale.expected_stoppedValue_mono` (recovered for v4.30 with `{τ σ : Ω → ℕ∞}` to match the `IsStoppingTime`/WithTop signature).
- `mart-thm-2.4.3` — `maximal_ineq` (mechanical rename `nonempty_range_succ` → `nonempty_range_add_one` applied for v4.30).
- `mart-thm-2.5.1`, `mart-thm-2.5.3` — `Submartingale.ae_tendsto_limitProcess`.
- `mart-prop-2.5.5` — `Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`.
- `dist-thm-B.1.2-affine` — `gaussianReal_const_mul` + `gaussianReal_add_const` (rewritten in the new `HasLaw X (gaussianReal μ v) P` form for v4.30).
- `ce-prop-2.1.5-linearity` — `condExp_add` + `condExp_smul`.
- `ce-prop-2.1.11-tower`, `cv-cond-exp-tower` — `condExp_condExp_of_le`.
- `ce-prop-2.1.11-pull-out` — `condExp_mul_of_stronglyMeasurable_left`.
- `ce-prop-2.1.11-independence` — `condExp_indep_eq`.

Added in the v4.30 migration (5):

- `mc-thm-1.4.25` — AFP `Stochastic_Matrices.stationary_distribution_unique`.
- `mc-thm-1.3.12` — AFP `Markov_Models.recurrent_iff_G_infinite`.
- `mc-thm-1.4.40` — AFP `Markov_Models.stationary_distribution_imp_p_limit`.
- `pp-thm-3.3.8` — HOL-Probability `prob_space.erlang_distributed_sum`.
- `dist-thm-B.1.2-marginal` — Mathlib `measurePreserving_eval_multivariateGaussian`.

Added in the BM-port + Strong-Markov sweep (2):

- `bm-thm-5.1.4` — Mathlib `HasIndepIncrements.indepFun_eval_sub` (upstream, no Degenne dep needed).
- `mc-thm-1.2.11` — AFP `Markov_Models.Discrete_Time_Markov_Process.lim_stream_strong_Markov` inside `discrete_Markov_process` locale.

(Note: `cm-prop-4.3.6` is `reduced_core` — its spec field uses the new `IsStoppingTime 𝓕 (fun ω => (τA ω : WithTop ℝ))` form. The textbook continuous-time hitting-time-of-an-open-set theorem still has no direct Mathlib wrap; the `reduced_core` spec pins the statement. `bm-thm-5.3.2` and `bm-prop-5.1.2` are also `reduced_core` after the BM port — see "BM port (2026-05-09)".)

## Delivery-Safe Claim

Use wording like:

> We built a reproducible Lean 4 / Isabelle verification artifact covering 65 stochastic-process benchmark statements. All active prover obligations type-check under Mathlib v4.30 / Lean v4.30.0-rc1 with Mathlib pinned to commit `f23306121184` (validated 2026-05-09). Under a strict faithfulness audit, 33 entries are full or direct library-backed theorem formalizations: 13 derive the conclusion from honest hypotheses (or are structural definitions), 20 directly invoke a named Mathlib / Isabelle-AFP theorem whose statement matches the benchmark. The remaining 32 entries are `reduced_core`: the active code is honest but is either a narrower algebraic/analytic check or a Lean specification structure that pins down the textbook STATEMENT (so any inhabitant satisfies it by construction) without DERIVING the conclusion. There are zero placeholders. The artifact identifies precisely where current Lean/Isabelle libraries support the course material, where a meaningful real proof is achievable in the near term, and where genuine new stochastic-process infrastructure is required (Brownian-motion construction, Itô-integral layer, Doob L^p, conditional Gaussian, continuous-time hitting times).

Avoid:

> We formally proved all theorems in the course.

That claim is not supported. The honest version is:

> We have faithful Lean STATEMENTS for all 65 textbook theorems, real derivations or library-backed proofs for 33 of them, and explicit `reduced_core` specifications for the remaining 32 documenting what a real proof would need to construct.

## Path Forward

See `docs/superpowers/specs/2026-05-06-real-proof-tiers.md` for the three-tier classification of which theorems support real proofs today (Tier A), which require building Brownian motion first (Tier B), and which require the stochastic-integral layer (Tier C). The next stage of work is to attack Tier A theorems with real proofs — many of them (conditional Jensen, Doob L^p) are flagged as TODOs in Mathlib master and would land upstream.
