# Contributing

This is a Lean 4 library of formally verified quant-finance theorems. The
canonical verification is `lake build` from the repo root.

## Getting set up

The fastest path is Docker (pinned Lean toolchain + Mathlib + BrownianMotion):

```bash
# Pull the prebuilt image (~3 min vs ~15 min local build)
docker compose -f docker/docker-compose.yml pull verify

# Sanity check: build the whole library
docker compose -f docker/docker-compose.yml run --rm --entrypoint bash verify -lc 'lake build'
```

For host authoring, install elan + the pinned Lean toolchain, then VS Code with
the Lean extension. The Lake project at repo root is what VS Code's LSP sees;
no extra config needed.

## Adding a theorem

1. **Pick a home.** The library is organised by topic under `HybridVerify/`:
   - `Foundations/` — probability primitives, Itô, FTAP, pricing kernels.
   - `BlackScholes/` — BS family, Greeks, exotics.
   - `Binomial/` — CRR, American, Snell, reflection.
   - `Futures/`, `FixedIncome/`, `Portfolio/`, `Performance/`, `RiskMeasures/`,
     `Actuarial/`, `DeFi/` — domain-specific modules.
2. **Author the proof in a real `.lean` file**, not in a JSON snippet.
   Non-trivial proofs need the full `lake build` memory budget + incremental
   compilation + LSP authoring. The benchmark JSONs are for re-export shims
   (5-25 lines) that `import HybridVerify.<Section>.<Module>` and reference
   the named lemma. Trivial library wrappers (single-line `:= someLemma`)
   can stay inline in the JSON.
3. **Iterate fast via the REPL daemon.** Per-file checks in 5-30 sec
   instead of 5-15 min:
   ```bash
   docker compose -f docker/docker-compose.yml up -d lean-repl
   docker compose -f docker/docker-compose.yml logs -f lean-repl | grep -m1 READY
   ./scripts/lean-check.sh HybridVerify/<Section>/<Module>.lean
   ```
4. **Confirm axioms-cleanliness.** Every `full` theorem must depend only on
   the three standard Mathlib axioms:
   ```lean
   #print axioms myTheorem
   -- expected: [propext, Classical.choice, Quot.sound]
   ```
   Anything more (e.g. `sorryAx`) means the proof has a gap.
5. **Update the audit.** Add a row to `docs/coverage.md` describing the
   theorem, the file path, and its faithfulness status:
   - `full` — derived from honest hypotheses.
   - `library_wrapper` — direct application of a named Mathlib /
     BrownianMotion lemma whose statement matches the benchmark.
   - `reduced_core` — narrower algebraic/analytic check, or specification
     structure that pins down the textbook statement without deriving it.
   - `placeholder` — must be 0; if you need a placeholder, the proof isn't
     ready to merge.
6. **Run the full build.** `lake build` (or the docker equivalent) — clean
   build is required.
7. **Run the regression tests:**
   ```bash
   docker compose -f docker/docker-compose.yml run --rm \
       --entrypoint python3 verify -m pytest tests/test_router.py -q
   ```

## Style

- One theorem per file when the theorem is non-trivial. Helper lemmas can
  live in the same file as `private`.
- Default to no comments. Add one only when the *why* is non-obvious (a
  hidden invariant, a workaround for a specific Mathlib bug, behaviour that
  would surprise a reader). Identifiers should carry the *what*.
- File headers follow Mathlib convention: copyright + license + authors +
  short docstring + `## Result` section listing the public lemmas.
- Match the surrounding code's tactic style. `field_simp; ring` for
  algebraic close-outs. `bs_identity` for BS-family derivations. See
  `docs/patterns.md` for the distilled pattern catalogue.

## Upstream contributions

Drafts for Mathlib, Degenne's BrownianMotion, and Zulip messages live under
`upstream/`:

- `upstream/mathlib/` — PR drafts (Lean files + PR_BODY.md).
- `upstream/brownian-motion/` — PR drafts (Lean files + ISSUE_BODY.md).
- `upstream/zulip/` — discussion drafts.

When a HybridVerify result is general enough to belong upstream, draft it
here first, get a sign-off on the Lean side, then open the PR against the
target repo. Keep the in-tree copy until the upstream PR lands.

## Reorganization rationale

The repo was previously framed as a "hybrid Lean + Isabelle + SymPy
verification framework." That framing has been retired — see
`docs/superpowers/specs/2026-05-23-repo-reorganization-design.md`. The
artifact is the Lean library; the Python runner is a CLI harness.
