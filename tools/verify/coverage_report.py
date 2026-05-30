"""Formal backend coverage report for benchmark JSON files."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

from .models import Domain


ALLOWED_FORMALIZATION_STATUSES = {
    "full",
    "library_wrapper",
    "reduced_core",
    "placeholder",
}


def _load_theorems(path: Path) -> list[dict]:
    data = json.loads(path.read_text())
    return data.get("theorems", data)


def main() -> int:
    totals: Counter[str] = Counter()
    by_file: dict[str, Counter[str]] = {}
    formal_gaps: list[str] = []

    for path in sorted(Path("benchmarks").glob("*.json")):
        file_counts: Counter[str] = Counter()
        by_file[path.name] = file_counts

        for theorem in _load_theorems(path):
            totals["theorems"] += 1
            file_counts["theorems"] += 1

            code = theorem.get("code", {})
            metadata = theorem.get("metadata", {})
            formalization_status = metadata.get("formalization_status")
            Domain(theorem["domain"])  # validate the domain enum value

            # Lean is the sole backend. A non-lean code key or a leftover
            # cas_reference is dropped-backend residue (sympy/isabelle were
            # stripped from the repo) and must not reappear.
            for name in code:
                if name != "lean":
                    formal_gaps.append(
                        f"{path.name}:{theorem['id']} non-lean code key '{name}'"
                    )
            if "cas_reference" in metadata:
                formal_gaps.append(
                    f"{path.name}:{theorem['id']} leftover cas_reference metadata"
                )

            if formalization_status not in ALLOWED_FORMALIZATION_STATUSES:
                formal_gaps.append(
                    f"{path.name}:{theorem['id']} missing/invalid formalization_status"
                )
            else:
                totals[f"status_{formalization_status}"] += 1
                file_counts[f"status_{formalization_status}"] += 1

            if "lean" in code:
                totals["lean_code"] += 1
                file_counts["lean_code"] += 1
            else:
                formal_gaps.append(f"{path.name}:{theorem['id']} no lean code")

    print("Formal coverage report")
    print("======================")
    print(f"theorems: {totals['theorems']}")
    print(f"Lean code entries: {totals['lean_code']}")
    print("\nFormalization faithfulness")
    print(f"full theorem statements: {totals['status_full']}")
    print(f"library theorem wrappers: {totals['status_library_wrapper']}")
    print(f"reduced formal cores: {totals['status_reduced_core']}")
    print(f"placeholders/stubs: {totals['status_placeholder']}")
    print(
        "delivery-claim ready: "
        f"{totals['status_full'] + totals['status_library_wrapper']}"
    )

    print("\nBy file")
    for name, counts in by_file.items():
        print(
            f"- {name}: {counts['theorems']} theorems, "
            f"Lean {counts['lean_code']}, "
            f"full {counts['status_full']}, "
            f"library {counts['status_library_wrapper']}, "
            f"reduced {counts['status_reduced_core']}, "
            f"placeholder {counts['status_placeholder']}"
        )

    if formal_gaps:
        print("\nFormal gaps")
        for gap in formal_gaps:
            print(f"- {gap}")
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
