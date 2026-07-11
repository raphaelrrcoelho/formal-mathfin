"""Incremental verification ledger for benchmark snippets.

Each benchmark entry's validity depends on exactly three inputs: its own
``code.lean`` snippet, the source of the MathFin modules it (transitively)
imports, and the toolchain pins (``lean-toolchain`` + ``lake-manifest.json``,
which pin Mathlib and BrownianMotion). This tool hashes those inputs per entry
and records, in ``verification_ledger.json`` at the repo root, the hash under
which each entry last verified.

"Is anything rotten?" then becomes a hash comparison (milliseconds), and a
sweep re-verifies only entries whose inputs actually changed — instead of all
261 entries (~hours of container boots).

Usage (host side; the Lean work happens in the lean-repl daemon):

    python3 -m tools.verify.ledger status            # fresh/stale/missing report
    python3 -m tools.verify.ledger verify --stale    # re-verify what changed
    python3 -m tools.verify.ledger verify --all      # full seeding sweep

``verify`` talks to the lean-repl daemon on 127.0.0.1:7878 (same protocol as
``scripts/lean-check.sh``: send raw Lean code, half-close, read JSON). Bring
the daemon up first; on success each entry is recorded immediately, so an
interrupted sweep resumes with ``--stale``. Pure stdlib.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import os
import re
import socket
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
LEDGER_PATH = REPO / "verification_ledger.json"
BENCH_DIR = REPO / "benchmarks"
PIN_FILES = ("lean-toolchain", "lake-manifest.json")

# Tooling-only Lake packages, OUTSIDE every benchmark import closure: no
# MathFin module reachable from a benchmark snippet imports them (enforced by
# ``test_router.test_tooling_packages_not_imported_by_library``), and a
# package on LEAN_PATH that an env never imports cannot affect elaboration
# (Lean environments are import-closed). Their manifest entries are therefore
# stripped before pin-hashing so adding/bumping them does not false-restale
# the corpus. Substantive pins (mathlib, BrownianMotion, batteries, …) still
# restale everything, as they must.
# `Hammer`/`Duper`/`auto`/`premise-selection` are the LeanHammer cluster:
# authoring-time scouts (CLAUDE.md values gate), imported only by pilot files
# under tests/, never by MathFin modules or benchmark snippets.
PIN_EXCLUDED_PACKAGES = frozenset({
    "LeanArchitect", "Hammer", "Duper", "auto", "«premise-selection»",
})


def _pin_bytes(path: Path) -> bytes:
    """Pin-relevant bytes of a pin file (manifest: tooling packages stripped)."""
    data = path.read_bytes()
    if path.name != "lake-manifest.json":
        return data
    manifest = json.loads(data)
    manifest["packages"] = [
        p for p in manifest.get("packages", [])
        if p.get("name") not in PIN_EXCLUDED_PACKAGES
    ]
    return json.dumps(manifest, sort_keys=True).encode()

MATHFIN_IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?import(?:\s+all)?\s+(MathFin(?:\.[A-Za-z0-9_]+)*)\s*$",
    re.MULTILINE,
)

DAEMON_HOST = "127.0.0.1"
DAEMON_PORT = 7878


# ---------------------------------------------------------------- inputs

def _module_path(module: str) -> Path:
    return REPO / (module.replace(".", "/") + ".lean")


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class InputHasher:
    """Computes per-entry input hashes with memoized file hashes/imports."""

    def __init__(self, pins: str | None = None) -> None:
        self._file_sha: dict[Path, str] = {}
        self._file_imports: dict[Path, list[str]] = {}
        # Pin segment: tooling-only packages stripped from the manifest before
        # hashing (see PIN_EXCLUDED_PACKAGES). `pins` overrides for rebase.
        self._pins = pins if pins is not None else "".join(
            _sha(_pin_bytes(REPO / p)) for p in PIN_FILES
        )

    def _hash_file(self, path: Path) -> str:
        if path not in self._file_sha:
            self._file_sha[path] = _sha(path.read_bytes())
        return self._file_sha[path]

    def _imports_of(self, path: Path) -> list[str]:
        if path not in self._file_imports:
            text = path.read_text(encoding="utf-8")
            self._file_imports[path] = MATHFIN_IMPORT_RE.findall(text)
        return self._file_imports[path]

    def closure(self, code: str) -> list[tuple[str, str]]:
        """Transitive MathFin modules imported by a snippet: (module, sha)."""
        seen: dict[str, str] = {}
        frontier = MATHFIN_IMPORT_RE.findall(code)
        missing: list[str] = []
        while frontier:
            module = frontier.pop()
            if module in seen:
                continue
            path = _module_path(module)
            if not path.is_file():
                missing.append(module)
                seen[module] = "MISSING"
                continue
            seen[module] = self._hash_file(path)
            frontier.extend(self._imports_of(path))
        if missing:
            raise FileNotFoundError(
                f"snippet imports unknown MathFin modules: {missing}"
            )
        return sorted(seen.items())

    def entry_hash(self, code: str) -> str:
        closure = self.closure(code)
        blob = json.dumps(
            {"code": code, "modules": closure, "pins": self._pins},
            sort_keys=True,
        )
        return _sha(blob.encode("utf-8"))


def iter_entries():
    for path in sorted(BENCH_DIR.glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        theorems = data.get("theorems", data) if isinstance(data, dict) else data
        for theorem in theorems:
            yield path.name, theorem


# ---------------------------------------------------------------- ledger

def load_ledger() -> dict:
    if LEDGER_PATH.is_file():
        return json.loads(LEDGER_PATH.read_text(encoding="utf-8"))
    return {"_meta": {"description": "benchmark verification ledger; see tools/verify/ledger.py"}, "entries": {}}


def save_ledger(ledger: dict) -> None:
    with LEDGER_PATH.open("w", encoding="utf-8") as f:
        json.dump(ledger, f, indent=2, ensure_ascii=False, sort_keys=True)
        f.write("\n")


def classify(hasher: InputHasher, ledger: dict):
    """Returns (fresh, stale, missing) lists of (file, id, code, hash)."""
    fresh, stale, missing = [], [], []
    for fname, theorem in iter_entries():
        code = theorem["code"]["lean"]
        digest = hasher.entry_hash(code)
        row = ledger["entries"].get(theorem["id"])
        item = (fname, theorem["id"], code, digest)
        if row is None:
            missing.append(item)
        elif row.get("input_hash") != digest:
            stale.append(item)
        else:
            fresh.append(item)
    return fresh, stale, missing


# ---------------------------------------------------------------- daemon

def daemon_check(code: str, timeout: float) -> dict:
    """Send one snippet to the lean-repl daemon, return its JSON verdict."""
    with socket.create_connection((DAEMON_HOST, DAEMON_PORT), timeout=30) as conn:
        conn.settimeout(timeout)
        conn.sendall(code.encode("utf-8"))
        conn.shutdown(socket.SHUT_WR)
        chunks = []
        while True:
            data = conn.recv(65536)
            if not data:
                break
            chunks.append(data)
    return json.loads(b"".join(chunks).decode("utf-8"))


EXEC_CONTAINER = os.environ.get("LEDGER_EXEC_CONTAINER", "docker-lean-repl-1")
# Compose bind-mounts specific subtrees (MathFin/, tools/, ...), NOT the repo
# root — so the temp file must live inside one of them. MathFin/ is mounted RW
# (same pattern as scripts/bench-check.sh); the dotfile name keeps it out of
# the lake glob and git.
EXEC_TMP = "MathFin/.ledger-exec-check.lean"


def exec_check(code: str, timeout: float) -> dict:
    """Stateless check: write the snippet to a repo-root temp file and run
    ``lake env lean`` on it inside the (bind-mounted) Lean container.

    No REPL, no env cache — a flat ~30–90 s per entry that is immune to the
    daemon's cold-start pathology (a respawned REPL re-pays the full Mathlib
    import on its first request). Best for small batches; the daemon path
    still wins for long warm sweeps where repeat import-sets cost ~0.1 s.
    Read-only on the olean store (``lake env`` does not build), so it is safe
    to run next to an idle daemon."""
    tmp_host = REPO / EXEC_TMP
    tmp_host.write_text(code, encoding="utf-8")
    # LEDGER_EXEC_LOCAL: run `lake env lean` directly in THIS environment (already
    # inside a Lean-equipped container, e.g. the autoform PR-assembly build) rather
    # than `docker exec` into a named daemon container.
    if os.environ.get("LEDGER_EXEC_LOCAL"):
        cmd = ["lake", "env", "lean", EXEC_TMP]
    else:
        cmd = ["docker", "exec", EXEC_CONTAINER, "lake", "env", "lean", f"/app/{EXEC_TMP}"]
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout, cwd=REPO,
        )
    finally:
        tmp_host.unlink(missing_ok=True)
    out = (proc.stdout or "") + (proc.stderr or "")
    errors = [ln for ln in out.splitlines() if "error" in ln.lower()]
    sorry_count = out.count("declaration uses 'sorry'")
    return {
        "success": proc.returncode == 0 and not errors and sorry_count == 0,
        "errors": errors[:20],
        "warnings": [],
        "sorry_count": sorry_count,
    }


def _git_head() -> str:
    try:
        return subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            cwd=REPO, capture_output=True, text=True, check=True,
        ).stdout.strip()
    except Exception:
        return "unknown"


# ---------------------------------------------------------------- commands

def cmd_status(_args) -> int:
    hasher = InputHasher()
    ledger = load_ledger()
    fresh, stale, missing = classify(hasher, ledger)
    print(f"fresh: {len(fresh)}  stale: {len(stale)}  missing: {len(missing)}")
    for label, items in (("STALE", stale), ("MISSING", missing)):
        for fname, tid, _, _ in items:
            print(f"  {label:8} {fname:32} {tid}")
    return 0 if not stale and not missing else 1


def cmd_verify(args) -> int:
    hasher = InputHasher()
    ledger = load_ledger()
    fresh, stale, missing = classify(hasher, ledger)
    targets = stale + missing if not args.all else fresh + stale + missing
    # Cluster identical import sets: the daemon's lean-interact env cache makes
    # a repeat import-set ~0.1s vs ~60-80s for a fresh one, so ordering by
    # import set amortizes env construction maximally.
    targets.sort(key=lambda item: (
        tuple(sorted(MATHFIN_IMPORT_RE.findall(item[2]))) or ("~mathlib-only",),
        item[0], item[1],
    ))
    if args.limit:
        targets = targets[: args.limit]
    if not targets:
        print("nothing to verify — ledger is fresh")
        return 0

    head = _git_head()
    checker = exec_check if args.use_exec else daemon_check
    via = ("`lake env lean` in container " + EXEC_CONTAINER) if args.use_exec \
        else "the lean-repl daemon"
    print(f"verifying {len(targets)} entries via {via} (HEAD {head})",
          flush=True)
    failures = []
    for i, (fname, tid, code, digest) in enumerate(targets, 1):
        t0 = time.monotonic()
        try:
            verdict = checker(code, timeout=args.timeout)
        except (ConnectionRefusedError, OSError,
                subprocess.TimeoutExpired) as exc:
            print(f"\nABORT at {tid}: checker unavailable ({exc}). "
                  "Fix and resume with `verify --stale`.", flush=True)
            break
        elapsed = round(time.monotonic() - t0, 1)
        if verdict.get("success"):
            ledger["entries"][tid] = {
                "input_hash": digest,
                "verified_at_commit": head,
                "date": _dt.date.today().isoformat(),
                "elapsed_s": elapsed,
                "benchmark_file": fname,
            }
            save_ledger(ledger)
            print(f"[{i}/{len(targets)}] OK   {tid} ({elapsed}s)", flush=True)
        else:
            failures.append((fname, tid, verdict.get("errors", [])))
            print(f"[{i}/{len(targets)}] FAIL {tid} ({elapsed}s) "
                  f"{verdict.get('errors', [])[:2]}", flush=True)

    print(f"\ndone: {len(targets) - len(failures)} verified, "
          f"{len(failures)} failed", flush=True)
    for fname, tid, errors in failures:
        print(f"  FAIL {fname:32} {tid}")
        for err in errors[:3]:
            print(f"       {err}")
    return 1 if failures else 0


def cmd_rebase_pins(args) -> int:
    """Rewrite stored entry hashes from the OLD pin scheme to the current one
    — WITHOUT re-verification, and only where that is provable.

    Sound by construction: an entry is rewritten only if its stored hash
    EQUALS the hash recomputed under the baseline rev's pin files (old
    raw-bytes scheme) with the CURRENT snippet + module closure — i.e. its
    code and every transitive MathFin module are byte-identical to the
    verified state, and only the pin segment moved. Anything else is left
    untouched (genuinely stale ⇒ still needs `verify`). Use when the pin
    *scheme* changes or a PIN_EXCLUDED_PACKAGES dep is added — never as a
    shortcut after substantive pin bumps (those won't match the proof gate
    anyway, by design)."""
    def git_show(rev: str, path: str) -> bytes:
        return subprocess.run(
            ["git", "show", f"{rev}:{path}"],
            cwd=REPO, capture_output=True, check=True,
        ).stdout

    old_pins = "".join(_sha(git_show(args.baseline_rev, p)) for p in PIN_FILES)
    old_hasher = InputHasher(pins=old_pins)
    new_hasher = InputHasher()
    ledger = load_ledger()
    entries = ledger.get("entries", {})
    rebased = skipped = 0
    for _fname, theorem in iter_entries():
        tid = theorem["id"]
        code = theorem.get("code", {}).get("lean", "")
        row = entries.get(tid)
        if row is None:
            continue
        if row.get("input_hash") == old_hasher.entry_hash(code):
            row["input_hash"] = new_hasher.entry_hash(code)
            row["pin_rebased_from"] = args.baseline_rev
            rebased += 1
        else:
            skipped += 1
    save_ledger(ledger)
    print(f"rebased: {rebased}  left-untouched: {skipped} "
          f"(baseline {args.baseline_rev})")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("status", help="fresh/stale/missing report (exit 1 if not all fresh)")
    p_rebase = sub.add_parser(
        "rebase-pins",
        help="migrate stored hashes across a pin-SCHEME change (proof-gated, "
             "no re-verification; see cmd_rebase_pins docstring)")
    p_rebase.add_argument("--baseline-rev", default="HEAD",
                          help="git rev whose pin files the ledger was "
                               "last verified under (default HEAD)")
    p_verify = sub.add_parser("verify", help="verify entries via the lean-repl daemon")
    p_verify.add_argument("--all", action="store_true",
                          help="re-verify everything, not just stale/missing")
    p_verify.add_argument("--stale", action="store_true",
                          help="(default) verify stale + missing entries only")
    p_verify.add_argument("--limit", type=int, default=0,
                          help="cap the number of entries this run")
    p_verify.add_argument("--exec", dest="use_exec", action="store_true",
                          help="check via `lake env lean` inside the container "
                               "(stateless, no REPL env cache; flat ~30-90s "
                               "per entry — best for small batches and cold "
                               "daemons)")
    p_verify.add_argument("--timeout", type=float, default=1800.0,
                          help="per-entry daemon timeout in seconds")
    args = parser.parse_args()
    if args.command == "status":
        return cmd_status(args)
    if args.command == "rebase-pins":
        return cmd_rebase_pins(args)
    return cmd_verify(args)


if __name__ == "__main__":
    sys.exit(main())
