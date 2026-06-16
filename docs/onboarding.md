# First contribution walkthrough

This guide walks you through making your first contribution to `formal-mathfin`
from zero to a merged PR. It assumes familiarity with Lean 4 syntax but not
with this codebase.

## 1. Pick a task

Browse issues labelled
[`good first issue`](https://github.com/raphaelrrcoelho/formal-mathfin/issues?q=is%3Aopen+label%3A%22good+first+issue%22).

Good entry points by type:
- **Documentation only** (no build required): glossary, troubleshooting FAQ,
  cross-linking `docs/coverage.md`, `## Result` docstring audit.
- **Small Lean proof** (~50–100 LOC): a new Black–Scholes Greek (charm, speed)
  or the Black-76 caplet — the pattern is fully established, the infrastructure
  is all there.
- **Python tooling** (~150–250 LOC): `formalization.yaml` manifest generator.

## 2. Set up the environment

### Docker path (recommended — pins Lean/Mathlib/BrownianMotion)

```bash
# Log in to GHCR (one-time per machine):
TOKEN=$(grep -E '^[[:space:]]+oauth_token:' ~/.config/gh/hosts.yml | head -1 | awk '{print $2}')
echo "$TOKEN" | docker login ghcr.io -u raphaelrrcoelho --password-stdin
# If the command above fails, refresh gh auth first:
# gh auth refresh -h github.com -s read:packages

# Pull the pinned image (~3 min):
docker compose -f docker/docker-compose.yml pull verify

# Sanity check — clean exit means every theorem typechecks:
docker compose -f docker/docker-compose.yml run --rm --entrypoint bash verify -lc 'lake build'
```

### VS Code authoring (for Lean edits)

Install [elan](https://github.com/leanprover/elan) and the VS Code Lean 4
extension. Open the repo root — the `lakefile.lean` is the project root. The
LSP picks up `MathFin/` automatically; `loogle`/`apply?`/`exact?` work
transitively through Mathlib.

## 3. Fast iteration loop (5–30 s per check)

Instead of a cold `lake build` (5–15 min), use the persistent REPL daemon:

```bash
# Start the daemon (once per session, wait for "READY"):
docker compose -f docker/docker-compose.yml up -d lean-repl
docker compose -f docker/docker-compose.yml logs -f lean-repl | grep -m1 READY

# Check a file after each edit:
./scripts/lean-check.sh MathFin/BlackScholes/PDE.lean
# Returns JSON: {"success": bool, "errors": [...], "warnings": [...], "sorry_count": N}

# Check a single benchmark snippet:
./scripts/bench-check.sh benchmarks/mathematical_finance.json mf-bs-delta

# Tear down at end of session:
docker compose -f docker/docker-compose.yml down lean-repl
```

> **Memory rule:** never run two Lean-loaded processes simultaneously.
> Daemon up → no `lake build`, no `verify` runs. See
> [troubleshooting.md](troubleshooting.md) if you hit OOM.

## 4. Understand the library layout

```
MathFin/
  Foundations/       # probability primitives, Itô, FTAP, pricing kernels
  BlackScholes/      # BS formula, Greeks, exotics, PDE, Merton jump-diffusion
  Binomial/          # CRR, American/Bermudan, Snell, reflection principle
  Futures/           # Black-76, swaption
  FixedIncome/       # ZCB, duration, credit, Vasicek
  Portfolio/         # Markowitz, CAPM, Black-Litterman, risk parity
  Performance/       # Sharpe, Sortino, Treynor, Kelly
  RiskMeasures/      # VaR, CVaR, coherent axioms
  Actuarial/         # annuity, net premium, Gompertz
  DeFi/              # constant-product AMM
  Examples.lean      # curated five-proof tour — start here
```

Every module **must** have `@[expose] public section` after its docstring
(otherwise its declarations are module-private and benchmark snippets break).

Non-trivial proofs live in `.lean` files here. Benchmark JSONs contain only
5–25 line re-export shims (`import MathFin.<Section>.<Module>` + a reference to
the named lemma).

## 5. Anatomy of a module file

```lean
/-
Copyright (c) 2026 Your Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name

## Result

`myTheorem` : <one-line description>.
-/

import MathFin.Foundations.GaussianCDFDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian

@[expose] public section

open MeasureTheory

/-- The main result. -/
theorem myTheorem ... := by
  ...
```

## 6. Check axioms-cleanliness

Every `full` theorem must depend only on the three Mathlib standard axioms:

```lean
#print axioms myTheorem
-- expected: [propext, Classical.choice, Quot.sound]
```

Anything else (especially `sorryAx`) means the proof has a gap and cannot merge.

## 7. Update the audit trail

After the proof builds:

```bash
# 1. Add/update docs/coverage.md row (file, theorem name, status, evidence).
# 2. Regenerate the exhaustive axiom audit:
python3 -m tools.verify.axiom_audit_gen --write

# 3. Refresh the verification ledger:
python3 -m tools.verify.ledger status   # shows fresh/stale/missing
# If stale entries: start the daemon and run:
python3 -m tools.verify.ledger verify
```

## 8. Run the gates

```bash
docker compose -f docker/docker-compose.yml run --rm \
    --entrypoint python3 verify -m pytest tests/ -q
```

All three test files must pass:
- `tests/test_router.py` — routing, Lean-only code keys, no sorry, `@[expose]` rule, formalization_status.
- `tests/test_ledger.py` — ledger freshness and unique ids.
- `tests/test_values.py` — no forbidden tactics, no `rfl`-backed `full` entries, blueprint ⊆ audit.

## 9. Open the PR

Use the PR template (`.github/PULL_REQUEST_TEMPLATE.md`). Tick every box that
applies. The CI pipeline runs `pytest` + `ledger status` + `lake build` — a
red CI means the PR is not ready to merge.

## Where to ask for help

- Open a GitHub issue with a question label, or comment on the issue you're
  working on.
- The `docs/patterns.md` file is the distilled pattern catalogue — check it
  before asking "how do I prove X in this style."
- `docs/troubleshooting.md` covers common setup failures.
