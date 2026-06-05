"""Structural guards for the benchmark verification ledger.

Presence-only: every benchmark entry must have a ledger row, and entry ids
must be globally unique (the ledger is keyed by id). Freshness — whether each
row's input hash still matches the entry's code + transitive MathFin imports +
toolchain pins — is deliberately NOT asserted here: a library edit legitimately
stales entries until re-verification, and the test suite must stay green in
that window. Freshness is checked by

    python3 -m tools.verify.ledger status   # exit 1 when stale/missing

run after any MathFin/ or benchmark edit (re-verify with `verify --stale`).
"""

import json
from collections import Counter
from pathlib import Path


def _benchmark_ids():
    for path in Path("benchmarks").glob("*.json"):
        data = json.loads(path.read_text())
        theorems = data.get("theorems", data) if isinstance(data, dict) else data
        for theorem in theorems:
            yield path.name, theorem["id"]


def test_benchmark_ids_are_globally_unique() -> None:
    counts = Counter(tid for _, tid in _benchmark_ids())
    dupes = {tid: n for tid, n in counts.items() if n > 1}
    assert not dupes, dupes


def test_every_benchmark_entry_has_a_ledger_row() -> None:
    ledger = json.loads(Path("verification_ledger.json").read_text())
    rows = set(ledger["entries"])
    missing = [(fname, tid) for fname, tid in _benchmark_ids() if tid not in rows]
    assert not missing, missing
