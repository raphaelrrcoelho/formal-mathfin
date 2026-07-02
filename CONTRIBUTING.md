# Contributing

This is a Lean 4 library of formally verified mathematical-finance theorems. The
canonical verification is `lake build` from the repo root.

Please read and follow our [Code of Conduct](CODE_OF_CONDUCT.md).

**New here?** [`docs/onboarding.md`](docs/onboarding.md) is the step-by-step
first-contribution walkthrough. [`docs/troubleshooting.md`](docs/troubleshooting.md)
covers common setup failures. Issues tagged
[`good first issue`](https://github.com/raphaelrrcoelho/formal-mathfin/issues?q=is%3Aopen+label%3A%22good+first+issue%22)
are the recommended entry points. Maintainers can use the
[`docs/issue-labels.md`](docs/issue-labels.md) taxonomy to classify new issues
consistently.

## Getting set up

The fastest path is Docker (pinned Lean toolchain + Mathlib + BrownianMotion):

```bash
# Log in to GHCR (one-time per machine — needs gh with read:packages scope):
TOKEN=$(grep -E '^[[:space:]]+oauth_token:' ~/.config/gh/hosts.yml | head -1 | awk '{print $2}')
echo "$TOKEN" | docker login ghcr.io -u raphaelrrcoelho --password-stdin

# Pull the prebuilt image (~3 min vs ~15 min local build)
docker compose -f docker/docker-compose.yml pull verify

# Sanity check: build the whole library
docker compose -f docker/docker-compose.yml run --rm --entrypoint bash verify -lc 'lake build'
```

For host authoring, install elan + the pinned Lean toolchain, then VS Code with
the Lean extension. The Lake project at repo root is what VS Code's LSP sees;
no extra config needed.

## PR checklist

Before opening a PR use the PR template (`.github/PULL_REQUEST_TEMPLATE.md`).
The CI pipeline runs `pytest tests/ -q` → `python3 -m tools.verify.ledger status` →
`lake build` in that order. A red gate at any step blocks merge.

## Adding a theorem

1. **Pick a home.** The library is organised by topic under `MathFin/`:
   - `Foundations/` — probability primitives, Itô, FTAP, pricing kernels.
   - `BlackScholes/` — BS family, Greeks, exotics.
   - `Binomial/` — CRR, American, Snell, reflection.
   - `Futures/`, `FixedIncome/`, `Portfolio/`, `Performance/`, `RiskMeasures/`,
     `Actuarial/`, `DeFi/` — domain-specific modules.
2. **Author the proof in a real `.lean` file**, not in a JSON snippet.
   Non-trivial proofs need the full `lake build` memory budget + incremental
   compilation + LSP authoring. The benchmark JSONs are for re-export shims
   (5-25 lines) that `import MathFin.<Section>.<Module>` and reference
   the named lemma. Trivial library wrappers (single-line `:= someLemma`)
   can stay inline in the JSON.
3. **Iterate fast via the REPL daemon.** Per-file checks in 5-30 sec
   instead of 5-15 min:
   ```bash
   docker compose -f docker/docker-compose.yml up -d lean-repl
   docker compose -f docker/docker-compose.yml logs -f lean-repl | grep -m1 READY
   ./scripts/lean-check.sh MathFin/<Section>/<Module>.lean
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
       --entrypoint python3 verify -m pytest tests/ -q
   ```

   All three suites must pass:
   - `tests/test_router.py` — Lean-only routing, no `sorry`, `@[expose]` rule,
     `formalization_status` declared on every entry.
   - `tests/test_ledger.py` — ledger freshness and globally unique ids.
   - `tests/test_values.py` — no forbidden tactics, no `rfl`-backed `full`
     entries, blueprint-spine ⊆ curated `AxiomAudit`, byte-fresh
     `AxiomAuditGen.lean`.

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

When a MathFin result is general enough to belong upstream, draft it
here first, get a sign-off on the Lean side, then open the PR against the
target repo. Keep the in-tree copy until the upstream PR lands.
