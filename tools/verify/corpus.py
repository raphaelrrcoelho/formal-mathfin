"""Single source of truth for iterating the benchmark corpus.

Every tool that walks ``benchmarks/*.json`` (the axiom-audit generator, the
HF dataset builder, the values tests) imports this instead of re-implementing
the glob + ``{"theorems": [...]}``-vs-list handling — so the corpus schema is
a contract with one implementation. (``tools/verify/ledger.py`` still carries
its own variant, deliberately left untouched until its next structural pass:
it is verified load-bearing hashing code.)
"""

from __future__ import annotations

import json
from pathlib import Path


def iter_entries():
    """Yield ``(path, theorem_dict)`` over every benchmark entry, in
    deterministic (sorted-by-file) order."""
    for path in sorted(Path("benchmarks").glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        theorems = data.get("theorems", data) if isinstance(data, dict) else data
        for theorem in theorems:
            yield path, theorem
