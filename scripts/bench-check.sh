#!/usr/bin/env bash
# Check a single benchmark snippet against the lean-repl daemon (fast path).
#
#   ./scripts/bench-check.sh benchmarks/martingales.json mart-thm-2.2.9
#
# Extracts the entry's `code.lean` into a temp .lean file under the repo and
# pipes it through scripts/lean-check.sh (daemon at 127.0.0.1:7878 when up;
# falls back to a one-shot `lake env lean` container otherwise). This is the
# snippet-level sibling of lean-check.sh — use it to iterate on benchmark
# entries without paying the ~5-min verify-container cold boot per attempt.
#
# Note: this checks elaboration only. The canonical delivery gate remains the
# docker `verify` service (router + backend + confidence tiers).
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
JSON="${1:?usage: bench-check.sh <benchmark.json> <theorem-id>}"
ID="${2:?usage: bench-check.sh <benchmark.json> <theorem-id>}"

TMP="$REPO/MathFin/BenchCheckScratch.lean"
trap 'rm -f "$TMP"' EXIT

python3 - "$JSON" "$ID" > "$TMP" <<'PYEOF'
import json, sys
path, tid = sys.argv[1], sys.argv[2]
data = json.load(open(path))
thms = data["theorems"] if isinstance(data, dict) else data
hits = [t for t in thms if t["id"] == tid]
if not hits:
    sys.exit(f"no entry with id {tid!r} in {path}")
sys.stdout.write(hits[0]["code"]["lean"])
PYEOF

"$REPO/scripts/lean-check.sh" MathFin/BenchCheckScratch.lean
