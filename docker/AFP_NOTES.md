# AFP integration notes

This image extends the Isabelle 2025-2 + HOL-Probability stack with a
narrowly-scoped slice of the [Archive of Formal Proofs](https://www.isa-afp.org/)
so that benchmark theorems can import results that are not in the Isabelle
distribution itself, in particular Birkhoff's ergodic theorem
(`Ergodic_Theory.Invariants`) and discrete-time Markov chain theory
(`Markov_Models.Discrete_Time_Markov_Chain`).

## What was added

- `docker/Dockerfile.verify`
  - New `INSTALL_AFP` build arg (default `1`) controls a layer that runs
    after `isabelle build HOL-Probability`. The layer downloads
    `https://www.isa-afp.org/release/afp-current.tar.gz`, extracts it under
    `/opt/afp`, registers the component with
    `isabelle components -u /opt/afp/thys`, and pre-builds heaps for
    **only** `Ergodic_Theory`, `Markov_Models`, and `Stochastic_Matrices`
    (transitive AFP dependencies — `Coinductive`, `Gauss_Jordan_Elim_Fun`,
    `Perron_Frobenius`, `Jordan_Normal_Form`, etc. — are pulled in by
    `isabelle build -b`).
  - Build is single-threaded (`-j 1 -o threads=1`) under the existing
    `-Xmx2g` build cap. Runtime cap remains `-Xmx3g`.
- `isabelle/ROOT`
  - New `HybridVerifyAFP` session inheriting from `HOL-Probability` and
    declaring `Ergodic_Theory` and `Markov_Models` as `sessions`. The
    original `HybridVerify` session is unchanged.
- `hybrid_verify.toml`
  - New `[hybrid-verify.isabelle].afp_session = "HybridVerifyAFP"` key. The
    default `session` stays `HOL-Probability` so existing benchmarks are
    unaffected.
- `python/config.py`, `python/cli.py`, `python/isabelle_backend.py`
  - Backend now keeps a per-session map of running Isabelle servers/clients.
  - Per-theorem session selection: a benchmark may set
    `metadata.isabelle_session = "HybridVerifyAFP"` explicitly, or simply
    import an AFP-namespaced theory (e.g.
    `imports "Ergodic_Theory.Invariants"`). The backend recognizes the
    namespace prefixes `Ergodic_Theory`, `Markov_Models`,
    `Stochastic_Matrices`, `Perron_Frobenius`, `Jordan_Normal_Form`,
    `Coinductive`, and `Gauss_Jordan_Elim_Fun` and routes those theorems
    to the AFP heap.
  - All other theorems continue to verify against `HOL-Probability` exactly
    as before.

## Authoring AFP-backed benchmark theorems

The image pre-builds the AFP sessions `Ergodic_Theory` and `Markov_Models`
directly. Set `metadata.isabelle_session` to whichever AFP session contains
your imports:

```json
"metadata": { "isabelle_session": "Markov_Models", ... }
```

```isabelle
theory Verify_X
  imports "Markov_Models.Classifying_Markov_Chain_States"
begin
  ...
end
```

Note: `HybridVerifyAFP` is declared in `isabelle/ROOT` as a wrapping session
but is NOT pre-built in the Docker layer (only the underlying AFP sessions
are). To use `HybridVerifyAFP` directly you would need to either rebuild
adding `HybridVerifyAFP` to the `isabelle build` line, or use the underlying
AFP session name directly (recommended).

The default session (`HOL-Probability`) is still used for theorems that
only need core probability theory.

## Verified theorems available for wrapping (probed 2026-05-07)

Within `MC_syntax` locale (from `Markov_Models.Classifying_Markov_Chain_States`):

- `recurrent_iff_U_eq_1`: `recurrent ?s = (U ?s ?s = 1)` — definition of recurrent state via return probability
- `recurrent_def`: `recurrent ?s = almost_everywhere (T ?s) (ev (HLD {?s}))` — alternative characterization (a.s. visits s infinitely often)
- `G_eq_real_suminf`: `G x y = ennreal (∑i. p x y i)` (when convergent) — connection between G and series of n-step probabilities
- `U_cases`: `U s s = 1 ∨ U s s < 1` — dichotomy
- `p_Suc`, `p_add`, `p_le_1`, `p_x_x_0`, `p_0` — n-step transition probability properties
- `f_Suc`, `f_le_p`, `F_le_1` — first passage time probabilities
- `gf_G_eq_gf_F`, `gf_G_eq_gf_U` — generating function relations

From `Ergodic_Theory.Ergodicity` (already wrapped for `mc-thm-1.4.32` / A.9):

- `birkhoff_theorem_AE` — Birkhoff's pointwise ergodic theorem in the
  `ergodic_pmpt` locale: `AE x in M. (λn. birkhoff_sum f n x / n) ⟶ ∫x. f x ∂M`.

From `Stochastic_Matrices.Stochastic_Matrix_Perron_Frobenius` (probed
2026-05-08 via WebFetch; **not yet exercised in Docker** — image must be
rebuilt with the updated AFP prebuild list):

- `stationary_distribution_exists` (matrix version): `∃ v. A *st v = v` —
  every stochastic matrix has a stationary distribution.
- `stationary_distribution_unique` (matrix version):
  `fixed_mat.irreducible (st_mat A) ⟹ ∃! v. A *st v = v` —
  uniqueness under irreducibility (target wrapper for A.10 = `mc-thm-1.4.25`).
- Markov-chain-flavoured variants exist inside `transition_matrix` locale.

NOT directly available even with the expanded AFP install:

- `recurrent ↔ G x x = ⊤` — textbook recurrence criterion ∑P^n(i,i) = ∞.
  Bridging is needed (limit z→1 of `gf_G` from `Markov_Models`); deferred.
- Spectral-gap / `P^n → π` convergence theorem for primitive stochastic
  matrices (target for A.8 = `mc-thm-1.4.40`). Probed
  `Stochastic_Matrix_Perron_Frobenius`: existence/uniqueness only, no
  convergence-of-powers statement found. Still blocked at the AFP level.
- **Doob's L^p maximal inequality** (target for A.2 = `mart-thm-2.4.6`).
  Probed 2026-05-08 across every plausible source:
  - AFP `Doob_Convergence` (Keskin): only upcrossing + a.s. convergence; no maximal.
  - AFP `Martingales` (Keskin, Banach-space): `Martingale.thy` has no `doob`/`maximal`
    lemmas at all (definitions only).
  - AFP `DiscretePricing/Martingale.thy`: 4 basic algebraic lemmas only.
  - Isabelle HOL-Probability core: has no `Martingale.thy`.
  - Mathlib v4.18.0: has only the L^1 form (`MeasureTheory.maximal_ineq`); the
    `OptionalStopping.lean` docstring explicitly notes the L^p form is "in an
    upcoming PR" and no such PR is currently open (searched all Mathlib PRs/issues
    mentioning Doob).
  - `RemyDegenne/brownian-motion` (the Mathlib martingale specialist's WIP repo):
    blueprint has `lem:doob_Lp_countable` outlined with the same proof strategy as
    our sketch (layer cake → L^1 → Fubini → Hölder), but **not yet formalized**
    in Lean. The repo's `DoobLp.lean` despite the filename only contains the L^1
    inequality generalized to countable + right-continuous index types.
  - No Lean↔Isabelle proof transport: OpenTheory connects HOL Light/Isabelle/HOL4
    only; no Lean target. There is no mechanism to wrap an Isabelle proof inside
    a Lean theorem (or vice versa) without re-proving from scratch.
  Conclusion: Doob's L^p maximal inequality is a genuine open frontier in formal
  probability. Treating `mart-thm-2.4.6` as `reduced_core` with a 10-helper-lemma
  Lean scaffold is the honest position. Future unblock: track Degenne's
  `brownian-motion` repo (he is closest to formalizing it) and the Mathlib
  `Probability/Martingale/` directory for an `Lp.lean` file or a PR adding
  `MeasureTheory.maximal_ineq_Lp` / `Submartingale.lp_maximal`.

## Image cost estimate

- AFP tarball download: ~100 MB (single HTTP GET).
- Extracted AFP tree under `/opt/afp`: roughly 1.5 GB on disk.
- Pre-built heaps for `Ergodic_Theory` + `Markov_Models` +
  `Stochastic_Matrices` and their transitive dependencies (`Coinductive`,
  `Gauss_Jordan_Elim_Fun`, `Perron_Frobenius`, `Jordan_Normal_Form`,
  `Polynomial_Factorization`, …): roughly 0.7 - 1.2 GB additional under
  `~/.isabelle`.
- Total image-size delta: order of **2.0 - 2.5 GB**.
- Build time delta on a modest CI box (single-threaded, `-Xmx2g`):
  expect roughly **30 - 60 minutes** for the AFP layer
  (`Ergodic_Theory` and the `Perron_Frobenius` cluster are the dominant
  costs). The HOL-Probability layer above is unchanged.

## Skipping the AFP layer

If you do not need ergodic / Markov entries and want a faster build:

```bash
docker compose -f docker/docker-compose.yml build \
  --build-arg INSTALL_AFP=0 verify
```

The image still has HOL-Probability and works for every benchmark whose
`code.isabelle` only imports `HOL-Probability.*`. Theorems that import an
AFP namespace will fail at verify time with an Isabelle "missing theory"
error; that is the intended signal.

## Why this layout

- Putting the AFP layer **after** the `HOL-Probability` build means edits
  to AFP wiring (or toggling `INSTALL_AFP`) don't invalidate the expensive
  HOL-Probability heap-build cache.
- Pre-building only the two sessions we use keeps the image well under what
  a full `isabelle build -b -a` (~60 GB, multi-hour) would cost.
- Per-theorem session dispatch keeps the existing single-session code path
  intact for benchmarks that don't need AFP.
