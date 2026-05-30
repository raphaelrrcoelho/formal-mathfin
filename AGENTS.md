# AGENTS.md

This file provides guidance to Codex when working with code in this
repository. The content mirrors `CLAUDE.md`; see that file for the
authoritative version. Codex-specific notes are at the bottom.

## What this repo is

A Lean 4 library of formally verified quant-finance theorems, built on
Mathlib and Degenne's BrownianMotion package. The Lean library is the
artifact; the Python runner under `tools/verify/` is a CLI harness that
drives `lean-interact` against benchmark JSONs. The library is
self-sufficient: a plain `lake build` from the repo root is the canonical
verification.

## Commands

Preferred runner is Docker:

```bash
docker compose -f docker/docker-compose.yml build verify
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/<file>.json -v --config quantfin.toml --timeout 120
```

The default compose command runs `benchmarks/cross_validated.json`:

```bash
docker compose -f docker/docker-compose.yml run --rm verify
```

Use the local Python CLI only for quick checks or when the local Lean
toolchain is known to be configured:

```bash
python -m tools.verify benchmarks/<file>.json [-v] [--config quantfin.toml] [--timeout 120] [--parallel]
```

`-v` enables debug logging. `--parallel` verifies all theorems concurrently
(otherwise sequential per-theorem; intra-theorem dispatch is governed by the
router).

Install (only needed for non-Docker workflows):

```bash
pip install -e ".[all]"                        # adds lean-interact
pip install -e ".[dev]"                        # pytest + pytest-asyncio
```

Fast regression checks:

```bash
python3 -m pytest tests/test_router.py
python3 -m tools.verify.coverage_report
```

`tests/test_router.py` enforces Lean-only routing, Lean-only `code` keys (no
dropped-backend residue), no `sorry`/`admit`, and a declared
formalization-faithfulness status for every benchmark theorem.

Delivery/status docs:
- `docs/coverage.md`: per-theorem audit, safe claim wording, verification evidence, and remaining placeholders.
- `docs/roadmap.md`: next-steps roadmap.
- `docs/bridges.md`: Foundations/ → pricing-module bridges catalogue.
- `docs/patterns.md`: distilled Lean proof patterns.

Docker notes:
- `docker/Dockerfile.verify` is the canonical reproducible environment: Lean (elan) + the `QuantFin` library prebuilt with `lake exe cache get && lake build`, plus Python + the `tools.verify` package.
- Compose bind-mounts `tools/`, `benchmarks/`, `tests/`, `quantfin.toml`, and the Lake project pieces at repo root (`QuantFin/`, `QuantFin.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`).
- `lean-interact`'s Mathlib cache lives in the `lean_interact_cache` Docker volume.
- If Docker build fails under Codex because it cannot write under `~/.docker`, rerun with elevated permissions.

## Architecture

Single Lean 4 backend, driven by a thin Python orchestrator. (The SymPy and
Isabelle backends from the early hybrid era have been removed entirely.)

**Dispatch** (`tools/verify/orchestrator.py`):
1. `Router.route(domain)` returns a `RoutingDecision`.
2. Sequential mode tries backends in order and stops on first SUCCESS.
3. Parallel mode dispatches via `asyncio.gather` (legacy; degenerates with one backend).
4. `compute_overall_confidence` picks the best backend confidence.

**Confidence tiers** (`tools/verify/models.py`):
- L5 = Lean SUCCESS (no sorries)
- L4 = Lean PARTIAL with ≤1 sorry; L3 = >1 sorry
- L0 = nothing succeeded

**Routing table** (`router.DEFAULT_ROUTING`) — all routes Lean-only.
Every theorem declares
`metadata.formalization_status ∈ {full, library_wrapper, reduced_core,
placeholder}`. Delivery claims count `full + library_wrapper` only — see
`docs/coverage.md`.

**Lean proofs live in `QuantFin/<Section>/<Module>.lean`**, organised
into thematic subdirectories: `Foundations/`, `BlackScholes/`, `Futures/`,
`Binomial/`, `FixedIncome/`, `Portfolio/`, `Performance/`, `RiskMeasures/`,
`Actuarial/`, `DeFi/`. The Lean backend uses `lean-interact.LocalProject`
pointing at the repo root. Non-trivial proofs **must** live as real Lean
files (full `lake build` memory budget + LSP); benchmark snippets
`import QuantFin.<Section>.<Module>` and re-export.

**Config** (`tools/verify/config.py`): TOML loader using stdlib `tomllib`
(Python 3.11+). Searches `quantfin.toml` then
`pyproject.toml[tool.quantfin-verify]`.

**Models** (`tools/verify/models.py`): `TheoremStatement` is a frozen
dataclass with mutable `metadata`. `code` keyed by `Backend` enum.

## Benchmark JSON shape

Either a top-level list of theorem dicts, or
`{"theorems": [...], "description": "..."}`. Each theorem requires `id`,
`name`, `domain` (must match a `Domain` enum value), and a `code` map with
active formal backend-name keys (`"lean"`). Optional: `description`,
`metadata`. Files are organized by Saporito stochastic-processes textbook
chapters.

## Codex-specific notes

- Codex's user is the same as Claude's user — see `MEMORY.md`-class
  feedback persisted across sessions for both agents.
- The `.codex/` directory holds Codex-local state and is gitignored.
