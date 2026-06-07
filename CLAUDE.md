# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repo is

A Lean 4 library of formally verified mathematical-finance theorems, built on Mathlib
and Degenne's BrownianMotion package. The Lean library is the artifact; the
Python runner under `tools/verify/` is a CLI harness that drives
`lean-interact` against benchmark JSONs. The library is self-sufficient: a
plain `lake build` from the repo root is the canonical verification.

## Commands

Preferred runner is Docker. The image is hosted on GHCR
(`ghcr.io/raphaelrrcoelho/mathfin-verify`, private). Pull-first,
build-fallback:

```bash
# First time on a machine — log in to GHCR with your gh OAuth token:
TOKEN=$(grep -E '^[[:space:]]+oauth_token:' ~/.config/gh/hosts.yml | head -1 | awk '{print $2}')
echo "$TOKEN" | docker login ghcr.io -u raphaelrrcoelho --password-stdin
# (gh auth must include `read:packages` scope; refresh with
#  `gh auth refresh -h github.com -s read:packages` if needed.)

# Refresh the image to the latest published version:
docker compose -f docker/docker-compose.yml pull verify

# Run a benchmark:
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/<file>.json -v --config mathfin.toml --timeout 120

# Rebuild the image: NEVER locally (see "Memory doctrine" below) — push to
# main (publish-image.yml paths cover MathFin/lakefile/manifest/toolchain/
# Dockerfile/pyproject) or trigger the workflow manually:
gh workflow run publish-image.yml && sleep 5 && gh run watch
# then refresh: docker compose -f docker/docker-compose.yml pull verify
```

The default compose command runs `benchmarks/cross_validated.json`:

```bash
docker compose -f docker/docker-compose.yml run --rm verify
```

Do NOT run `python -m tools.verify ...` against the host toolchain. Always go
through the docker `verify` service so Mathlib/Lean versions are pinned and
reproducible.

`-v` enables debug logging. `--parallel` verifies all theorems concurrently
(otherwise sequential per-theorem; intra-theorem dispatch is governed by the
router).

Install (only needed if running outside Docker):

```bash
pip install -e ".[all]"                        # adds lean-interact
pip install -e ".[dev]"                        # pytest + pytest-asyncio
```

(Core needs only the Python standard library; the extras add lean-interact /
pytest.)

Fast regression checks (run inside the verify container so versions match):

```bash
docker compose -f docker/docker-compose.yml run --rm \
    --entrypoint python3 verify -m pytest tests/test_router.py -q
docker compose -f docker/docker-compose.yml run --rm \
    --entrypoint python3 verify -m tools.verify.coverage_report
```

`tests/test_router.py` enforces Lean-only routing, Lean-only `code` keys (no
dropped-backend residue), no `sorry`/`admit`, a declared
formalization-faithfulness status for every benchmark theorem, and that every
`module`-header Lean file carries `@[expose] public section` (without it the
file's declarations are module-private — invisible to importers while the
build stays green). `tests/test_ledger.py` enforces that every entry has a
verification-ledger row and that ids are globally unique.
`tests/test_values.py` enforces the values gates: no forbidden text in
`MathFin/` sources (sorry/admit/native_decide/polyrith/`?`-suggestion
tactics/hammer/loogle/leansearch — comments exempt, allowlist with
justification), no `full` entry backed by a definitional-`rfl` proof (the
reduced_core pattern in disguise; caught mf-kelly-n-periods-linearity on its
first run), blueprint-spine ⊆ curated AxiomAudit, and byte-freshness of the
GENERATED exhaustive audit `MathFin/AxiomAuditGen.lean` — after ANY
benchmark edit regenerate it with
`python3 -m tools.verify.axiom_audit_gen --write` (it pins every
proof-position MathFin constant cited by the corpus; the curated
`MathFin/AxiomAudit.lean` remains the storied headliner file). CI
(`build.yml`) runs pytest + `ledger status` BEFORE the Lean build — pushes
with failing gates or stale ledger claims go red.

**Verification ledger** (`verification_ledger.json` + `tools/verify/ledger.py`):
every benchmark entry's validity depends on exactly its snippet code, the
transitive MathFin modules it imports, and the toolchain pins — the ledger
records the input-hash each entry last verified under. After ANY `MathFin/`
or benchmark edit:

```bash
python3 -m tools.verify.ledger status      # fresh/stale/missing (exit 1 if not all fresh)
python3 -m tools.verify.ledger verify      # re-verify just the stale entries (daemon must be up)
```

Host-side, stdlib-only; the Lean work happens in the lean-repl daemon. This
replaces blanket re-verification sweeps — only entries whose inputs changed
ever re-run. Benchmark snippets that import a MathFin module do NOT
`import Mathlib` (the module's `public import Mathlib` re-exports it);
only pure-Mathlib wrapper snippets carry the blanket import.

Delivery/status docs:
- `docs/coverage.md`: per-theorem audit, safe claim wording, verification evidence, and remaining placeholders.
- `docs/roadmap.md`: next-steps roadmap (strategic depth-vs-breadth framing + tactical phase log).
- `docs/bridges.md`: catalogue of Foundations/ → pricing-module bridges.
- `docs/patterns.md`: distilled Lean proof patterns from prior phases.

Docker notes:
- `docker/Dockerfile.verify` installs Lean (via elan), prebuilds the
  `MathFin` library against pinned Mathlib + BrownianMotion via
  `lake exe cache get && lake build`, then layers Python + the
  `tools.verify` package.
- Compose bind-mounts `tools/`, `benchmarks/`, `tests/`,
  `mathfin.toml`, and the Lake project pieces at repo root
  (`MathFin/`, `MathFin.lean`, `lakefile.lean`,
  `lake-manifest.json`, `lean-toolchain`). The Lake bind mount is RW so
  authoring `MathFin/*.lean` on host (VS Code + Lean LSP) propagates
  without a rebuild. The olean store lives in the `lake_build_cache`
  named volume, shared by `verify` and `lean-repl` (one Lake writer at a
  time — never run a build in one while the other is up); any host-side
  `.lake/` directory is unused and should not exist.
- **Single-FILE bind mounts pin the inode** (`MathFin.lean`,
  `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`,
  `mathfin.toml`): rename-based writes (Claude's Edit/Write tools, `sed
  -i`, `mv`) replace the host inode, after which a RUNNING container
  silently keeps the OLD content — while directory-mounted trees
  (`MathFin/`, `benchmarks/`, …) stay fresh. Symptom (2026-06-06): new
  modules built fine but the umbrella's import list was stale →
  "unknown constant" in AxiomAudit for every new name. After editing
  any single-file-mounted file, re-sync it into running containers
  (`docker exec -i docker-lean-repl-1 sh -c 'cat > /app/MathFin.lean'
  < MathFin.lean`) or restart the service. And never `| tail` a build
  log you are diagnosing — the first error is the diagnostic one.
- Both Lean services default to `cpuset 0-3` (4 Lake workers) and
  `mem_limit 6g`: this host gives WSL ~8 GB and uncapped Lean runs froze
  the machine. A runaway elaboration OOM-kills the container (exit 137,
  the backend respawns) instead of the host. Widen on bigger machines
  via `VERIFY_CPUSET=0-7`.
- `lean-interact`'s own cache is in the `lean_interact_cache` Docker volume.
- If Docker build fails under Claude/Codex because it cannot write under
  `~/.docker`, rerun the same `docker compose ...` command with elevated
  permissions.

## Memory doctrine — this box is a 10 GB client, not a build server

Measured 2026-06-06: 15.7 GB host RAM, WSL capped at 10 GB (`.wslconfig`
`memory=10GB`, `swap=4GB`, `autoMemoryReclaim=gradual` — already tuned; no
local headroom lever remains). A Mathlib-loaded Lean environment is ~4–5 GB,
so **two simultaneous Lean processes overcommit the host** — every OOM /
container kill / historical PC freeze has been exactly that event.

1. **One Lean-loaded process locally, ever.** The lean-repl daemon is the
   default slot occupant. `verify` runs, `leanchecker`, and lake builds take
   the slot only with the daemon DOWN (`docker compose down lean-repl`).
   Never exec a second env-loading command into a container already serving
   one (2026-06-06: a `leanchecker` exec OOM-killed the daemon's container).
2. **Never `docker compose build` locally.** Image builds escape compose's
   mem caps AND silently redo the full Mathlib layer (the local layer cache
   does not contain the pulled GHCR image's intermediates). CI
   `publish-image.yml` rebuilds on push to main (paths include `pyproject.toml`
   — pip layer inputs are baked, unlike bind-mounted `tools/`); locally only
   ever `docker compose pull verify`.
3. **Full-environment batch work runs on GitHub runners** (4-core/16 GB —
   more memory than this box): the `kernel-replay` (leanchecker) CI job,
   image publishing, and corpus-scale `ledger verify --exec` sweeps.
4. **Remote daemon is one flag away** when parallel heavy work is wanted:
   the whole authoring loop speaks TCP to `127.0.0.1:7878`, so
   `ssh -L 7878:localhost:7878 <bigger-box>` makes a remote daemon
   transparent to `lean-check.sh` / `bench-check.sh` / the ledger.

## Automation toolkit — and its values gate

In-loop automation (all CPU-local, pin-respecting):
- **`grind`** (in core): first call on algebraic equalities — incl. field
  identities with `≠ 0` side conditions and commuted denominators — ℕ/cast
  arithmetic, and goals linear in nonlinear atoms. NOT nonlinear real
  inequalities (0/7 on the corpus sample; FRO Year-3 work-in-progress —
  re-test each toolchain bump). Boundary + trials: docs/patterns.md.
- **`nlinarith [certificates]`** stays the tool for nonlinear inequalities;
  grind accepts the same certificates but does not search hypothesis
  products.
- **loogle** (`scripts/loogle.sh 'Real.sqrt (_ * _)'`): scriptable Mathlib
  search (public instance tracks a NEWER Mathlib than the pin — confirm hits
  via the daemon before building on them).
- **`hammer`** (LeanHammer, when present): premise selection + external ATP
  with NATIVE Aesop/Duper/Grind reconstruction — kernel-checked, axiom-clean.
  PRIVACY: never use the default cloud selector; every file sets
  `set_library_suggestions` to a local selector (sineQuaNon / MePo) or a
  self-hosted `premiseSelection.apiBaseUrl`.

The gate (the repo contract applies unchanged to machine-found proofs):
- Automation output is a **scout, not an author**. A goal closed by
  `hammer`/`grind` is refactored to the *conceptually right* proof — the
  certificate that shows why — before it merges. An opaque 20-premise
  discharge is slop even when the kernel accepts it.
- Search and premise tools exist to **find the idiomatic Mathlib/Degenne
  lemma so we consume it** instead of reproving it (coherence-first,
  anti-wrapper).
- The blueprint (`MathFin/Blueprint.lean`, post-hoc `@[blueprint]` tags) is
  the concept-clarity instrument: generated proof-term dependency graph +
  honest prose. Regenerate via `lake exe blueprint_export` +
  `tools/blueprint_render.py`; never hand-edit the generated block in
  docs/blueprint.md.
- `leanchecker` (CI kernel replay) + `AxiomAudit.lean` are the honesty
  floor. No `sorry`, axiom-clean, kernel-replayed.

## Architecture

Single Lean 4 verification backend, driven by a thin Python orchestrator.
Each theorem in a benchmark JSON file carries a `code` map with a single
`"lean"` key; the router maps the theorem's `domain` to the Lean backend.
(The SymPy and Isabelle backends from the early hybrid era have been removed
entirely.)

**Dispatch flow** (`tools/verify/orchestrator.py`):
1. `Router.route(domain)` returns a `RoutingDecision` (backend list + parallel flag) — always `[Backend.LEAN]`.
2. The theorem's `"lean"` code is dispatched to the Lean backend.
3. The routing/parallel scaffolding is retained from the hybrid era but degenerates to single-backend dispatch.
4. `compute_overall_confidence` reports the Lean result's confidence.

**Confidence tiers** (`tools/verify/models.py` + scoring in `confidence.py`):
- L5 = Lean SUCCESS (no sorries)
- L4 = Lean PARTIAL with ≤1 sorry; L3 = >1 sorry
- L0 = nothing succeeded

**Routing table** (`router.DEFAULT_ROUTING`) — Lean-only across all domains:
- `martingales`, `stopping_times`, `brownian_motion`, `measure_theory`, `poisson_processes`, `stochastic_calculus`, `stochastic_differential_equations`, `mathematical_finance`, `markov_chains`, `ergodic_theory`, `central_limit_theorem`.
- Every benchmark theorem's `code` map has a single `"lean"` key. Run `python3 -m pytest tests/test_router.py` after routing or benchmark-code edits.
- Every benchmark theorem must declare `metadata.formalization_status`: `full`, `library_wrapper`, `reduced_core`, or `placeholder`. Delivery claims count only `full + library_wrapper`; see `docs/coverage.md`.
- Do not tell a collaborator that all course theorems are formally proved. Run `python3 -m tools.verify.coverage_report` for the current `full / library_wrapper / reduced_core / placeholder` split.

**Lean proofs live in `MathFin/<Section>/<Module>.lean`, not in JSON
strings**. The library is organized into thematic subdirectories under the
repo-root `MathFin/`: `Foundations/`, `BlackScholes/`, `Futures/`,
`Binomial/`, `FixedIncome/`, `Portfolio/`, `Performance/`, `RiskMeasures/`,
`Actuarial/`, `DeFi/`. The Lean backend uses `lean-interact.LocalProject`
pointing at the repo root (configured via `mathfin.toml`
`local_project = "."`). `lakefile.lean` + `lake-manifest.json` +
`lean-toolchain` are authoritative for Mathlib/Lean versions and transitive
deps. Non-trivial proofs (multi-step derivations, helper lemmas, structures)
**must** live as real Lean files under `MathFin/<Section>/` so they
get the full `lake build` memory budget + incremental compilation + LSP
authoring; benchmark snippets `import MathFin.<Section>.<Module>` and
re-export the named lemma in 5–25 lines. Trivial library wrappers
(single-line `:= someLemma`) can stay inline in the JSON. To author a new
proof: edit `MathFin/<Section>/<Module>.lean` on host with VS Code +
Lean LSP (`loogle`/`leansearch%`/`apply?` are transitively available
via Mathlib's `LeanSearchClient`), `lake build` to validate, then update the
benchmark JSON to import + reference.

**Module-system rule**: `MathFin/` files use the Lean module system (`module`
header + `public import`s) and **must** put `@[expose] public section` right
after the module docstring. Without it every declaration is module-private:
importers see nothing, `lake build` stays green, and only consumers (benchmark
snippets) break. Enforced by
`test_router.test_mathfin_module_files_expose_public_section`.

**Fast authoring iteration via persistent REPL daemon (`docker compose
service lean-repl`)**. The daemon (`tools/verify/lean_repl.py`) boots a
`lean-interact` server pointing at the repo root once per session, paying
the ~5-min Mathlib + BrownianMotion + MathFin olean-load cost a single
time. It then listens on TCP `127.0.0.1:7878` and processes each "check this
file" request in 5-30 sec — vs. 5-15 min for the `docker compose run --rm
verify` cold path. This is the LSP-equivalent for non-editor authoring
(Claude Code edits via the Edit tool, not VS Code).

Workflow:
```bash
# one-time per session: bring up the daemon, wait for "READY" in its logs
docker compose -f docker/docker-compose.yml up -d lean-repl
docker compose -f docker/docker-compose.yml logs -f lean-repl | grep -m1 READY

# per iteration: edit a .lean file, then check it via the wrapper
./scripts/lean-check.sh MathFin/Foundations/BrownianMartingale.lean
# Returns JSON: {"success": bool, "errors": [...], "warnings": [...], "sorry_count": N}

# check a single benchmark snippet the same way (seconds, not a 5-min cold boot)
./scripts/bench-check.sh benchmarks/martingales.json mart-thm-2.2.9

# tear down at end of session
docker compose -f docker/docker-compose.yml down lean-repl
```

`scripts/lean-check.sh` auto-detects whether the daemon is up (probes
`127.0.0.1:7878`); falls back to `lake env lean <file>` inside a fresh
`verify` container if not (slow but reliable, with live stdout — no
`| tail` buffering). Daemon's TCP port is bound to localhost only (no
external exposure).

Caveats:
- Daemon serializes requests through `LeanBackend._lock` (Lean isn't reentrant). Concurrent connections queue.
- Daemon does not write `.olean`s for downstream imports; once a proof works in the daemon, run a final `lake build` (or restart the daemon) before relying on the oleans for cross-file imports.
- If you bump Mathlib pin or the lakefile, restart the daemon to pick up new project state.
- A red working tree does NOT block the daemon: if the startup `lake build`
  fails, it logs the error loudly and serves anyway against the oleans that
  did build (`lean-check` of the broken file works — it elaborates file
  content, needing only its imports' oleans). Checking a file that *imports*
  a broken module still fails (unknown-namespace cascades) until that module
  builds; the canonical green gate stays the final `lake build`.

For multi-iteration sessions, prefer keeping
`Foundations/BrownianMartingale.lean`-class files small (one theorem + its
private helpers per file) so Lean only re-elaborates the changed file.

**Lean backend is lazily initialized**. `LeanBackend._ensure_server` defers
the expensive Mathlib bootstrap to the first `verify()` call. It holds a
`threading.Lock` since `lean-interact`'s server is not thread-safe — async
`verify()` calls serialize through the lock.

**Config** (`tools/verify/config.py`): TOML loader using stdlib `tomllib`
(Python 3.11+). Searches `mathfin.toml` then `pyproject.toml`
(`[tool.mathfin-verify]`). Defaults are baked into the dataclasses, so a
missing file is fine.

**Models** (`tools/verify/models.py`): `TheoremStatement` is a frozen
dataclass; `metadata` is a mutable dict by reference. `code` is keyed by the
`Backend` enum (just `Backend.LEAN`); `from_dict` does the conversion at load
time.

## Benchmark JSON shape

Either a top-level list of theorem dicts, or
`{"theorems": [...], "description": "..."}`. Each theorem requires `id`,
`name`, `domain` (must match a `Domain` enum value), and a `code` map with a
single `"lean"` key. Optional: `description`, `metadata`. Files are organized
by Saporito stochastic-processes textbook chapters.
