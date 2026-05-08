"""Formal backend coverage report for benchmark JSON files."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

from .models import Backend, Domain
from .router import Router


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
    router = Router()
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
            domain = Domain(theorem["domain"])
            route = router.route(domain).backends
            formal_route = [backend for backend in route if backend != Backend.SYMPY]
            present = {Backend(name) for name in code}
            active = [backend for backend in formal_route if backend in present]

            if Backend.SYMPY in present:
                formal_gaps.append(f"{path.name}:{theorem['id']} active sympy code")
            if formalization_status not in ALLOWED_FORMALIZATION_STATUSES:
                formal_gaps.append(
                    f"{path.name}:{theorem['id']} missing/invalid formalization_status"
                )
            else:
                totals[f"status_{formalization_status}"] += 1
                file_counts[f"status_{formalization_status}"] += 1
            if "sympy" in metadata.get("cas_reference", {}):
                totals["cas_reference"] += 1
                file_counts["cas_reference"] += 1
            if Backend.LEAN in present:
                totals["lean_code"] += 1
                file_counts["lean_code"] += 1
            if Backend.ISABELLE in present:
                totals["isabelle_code"] += 1
                file_counts["isabelle_code"] += 1
            if Backend.LEAN in active and Backend.ISABELLE in active:
                totals["lean_isabelle_active"] += 1
                file_counts["lean_isabelle_active"] += 1
            elif Backend.LEAN in active:
                totals["lean_active"] += 1
                file_counts["lean_active"] += 1
            elif Backend.ISABELLE in active:
                totals["isabelle_active"] += 1
                file_counts["isabelle_active"] += 1
            else:
                formal_gaps.append(f"{path.name}:{theorem['id']} no formal route code")

    print("Formal coverage report")
    print("======================")
    print(f"theorems: {totals['theorems']}")
    print(f"active Lean-only: {totals['lean_active']}")
    print(f"active Isabelle-only: {totals['isabelle_active']}")
    print(f"active Lean+Isabelle: {totals['lean_isabelle_active']}")
    print(f"Lean code entries: {totals['lean_code']}")
    print(f"Isabelle code entries: {totals['isabelle_code']}")
    print(f"quarantined SymPy references: {totals['cas_reference']}")
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
            f"Lean-only active {counts['lean_active']}, "
            f"Isabelle-only active {counts['isabelle_active']}, "
            f"Lean+Isabelle active {counts['lean_isabelle_active']}, "
            f"CAS refs {counts['cas_reference']}, "
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
