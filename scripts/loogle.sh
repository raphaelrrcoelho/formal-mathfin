#!/usr/bin/env bash
# scripts/loogle.sh — scriptable Mathlib search for the authoring loop.
#
# Wraps the public loogle JSON API (https://loogle.lean-lang.org/json?q=…)
# so theorem search composes with lean-check.sh / bench-check.sh instead of
# needing an editor. Loogle's query language (type patterns with `_`,
# turnstile `⊢`, name fragments, `"string"`) is documented at
# https://loogle.lean-lang.org — the same engine as the in-editor `#loogle`.
#
# CAVEATS
#  * The public instance indexes a RECENT Mathlib, not this repo's pin
#    (lake-manifest.json). A hit may be renamed/absent in our snapshot —
#    always confirm via the daemon (`scripts/lean-check.sh` on a probe file)
#    before building on it. Misses in the other direction are rarer.
#  * It searches Mathlib only — never MathFin's own lemmas (grep for those).
#  * Self-host option (same toolchain as the project, exact-pin index):
#    https://github.com/nomeata/loogle ships a CLI binary and `server.py`.
#
# Usage:
#   scripts/loogle.sh 'Real.sqrt (_ * _)'
#   scripts/loogle.sh -n 5 'Tendsto, Finset.sum'
#   scripts/loogle.sh --json '⊢ Continuous Real.exp'   # raw JSON for tooling
set -euo pipefail

LIMIT=10
RAW=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    -n) LIMIT="$2"; shift 2 ;;
    --json) RAW=1; shift ;;
    -h|--help) grep '^#' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) break ;;
  esac
done

if [[ $# -lt 1 ]]; then
  echo "usage: $0 [-n LIMIT] [--json] '<loogle query>'" >&2
  exit 2
fi

QUERY="$*"
RESP="$(curl -sG --max-time 30 'https://loogle.lean-lang.org/json' --data-urlencode "q=$QUERY")"

if [[ "$RAW" == 1 ]]; then
  printf '%s\n' "$RESP"
  exit 0
fi

printf '%s' "$RESP" | python3 -c "
import json, sys
limit = int(sys.argv[1])
r = json.load(sys.stdin)
if 'error' in r:
    print('loogle error:', r['error'], file=sys.stderr)
    for s in (r.get('suggestions') or [])[:5]:
        print('  suggestion:', s, file=sys.stderr)
    sys.exit(1)
hits = r.get('hits') or []
print(f\"{r.get('header', '').splitlines()[0] if r.get('header') else ''} (showing {min(limit, len(hits))} of {len(hits)})\")
for h in hits[:limit]:
    print(f\"{h['name']}{h.get('type') or ''}\")
    print(f\"    [{h.get('module')}]\")
" "$LIMIT"
