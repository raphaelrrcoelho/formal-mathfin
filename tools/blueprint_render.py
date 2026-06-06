#!/usr/bin/env python3
"""Regenerate the mermaid spine in docs/blueprint.md from extracted blueprint JSON.

Pipeline (the graph is generated ground truth, never hand-drawn):

  1. inside the verify container:
       lake build MathFin.Blueprint blueprint_export
       lake exe blueprint_export MathFin.Blueprint > docs/blueprint_nodes.json
  2. host-side:
       python3 tools/blueprint_render.py        # rewrites the marked block

Edges come from `Architect.collectUsed` over the *proof terms* (transitive,
passing through untagged helpers) — see MathFin/Blueprint/Export.lean. A node
with no inferred edge is a genuine root: if the prose claims a dependency the
graph does not show, the prose is wrong, not the graph (this caught
`bs_pde_holds` being self-contained algebra on day one).

The not-yet-formalized frontier (no Lean declarations to tag) is declared in
EXTRA_NODES / EXTRA_EDGES below — the only hand-maintained remnant, kept
deliberately tiny and visibly ⏳-classed.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
NODES_JSON = REPO / "docs" / "blueprint_nodes.json"
BLUEPRINT_MD = REPO / "docs" / "blueprint.md"

BEGIN = "<!-- BEGIN GENERATED SPINE (tools/blueprint_render.py — do not hand-edit) -->"
END = "<!-- END GENERATED SPINE -->"

# The honest frontier: stated, not formalized, gated on upstream infrastructure.
# Keep in lock-step with the "The frontier" prose section of blueprint.md.
EXTRA_NODES = [
    ("pathwiseIto", "Pathwise Itô · Lévy · SDEs", "gated"),
]
EXTRA_EDGES = [
    ("itoIntegralClm", "pathwiseIto"),
    ("itoFormulaL2", "pathwiseIto"),
]


def mermaid_id(label: str) -> str:
    """`thm:ito-formula-l2` → `itoFormulaL2` (mermaid-safe camelCase)."""
    stem = label.split(":", 1)[-1]
    parts = re.split(r"[^A-Za-z0-9]+", stem)
    return parts[0] + "".join(p.capitalize() for p in parts[1:] if p)


def topo_order(nodes: list[dict]) -> list[dict]:
    """Kahn topological sort (deps first), label-sorted within a layer —
    stable output for clean git diffs."""
    by_label = {n["label"]: n for n in nodes}
    indeg = {n["label"]: 0 for n in nodes}
    for n in nodes:
        for u in n["uses"]:
            if u in indeg:
                indeg[n["label"]] += 1
    order, layer = [], sorted(l for l, d in indeg.items() if d == 0)
    while layer:
        nxt = []
        for l in layer:
            order.append(by_label[l])
            for m in nodes:
                if l in m["uses"]:
                    indeg[m["label"]] -= 1
                    if indeg[m["label"]] == 0:
                        nxt.append(m["label"])
        layer = sorted(set(nxt))
    if len(order) != len(nodes):  # cycle should be impossible for proof terms
        raise SystemExit("cycle detected in blueprint graph — refusing to render")
    return order


def node_class(n: dict) -> str:
    if not n.get("leanOk", True):
        return "partial"
    if not n.get("module", "").startswith("MathFin"):
        return "upstream"
    return "proved"


def render(nodes: list[dict]) -> str:
    lines = ["```mermaid", "graph TD"]
    ordered = topo_order(nodes)
    ids = {n["label"]: mermaid_id(n["label"]) for n in nodes}
    for n in ordered:
        title = n.get("title") or n["label"]
        lines.append(f'  {ids[n["label"]]}["{title}"]:::{node_class(n)}')
    for nid, title, cls in EXTRA_NODES:
        lines.append(f'  {nid}["{title}"]:::{cls}')
    lines.append("")
    for n in ordered:
        for u in sorted(n["uses"]):
            if u in ids:
                lines.append(f"  {ids[u]} --> {ids[n['label']]}")
    for src, dst in EXTRA_EDGES:
        lines.append(f"  {src} --> {dst}")
    lines += [
        "",
        "  classDef proved fill:#d4edda,stroke:#28a745,color:#111;",
        "  classDef upstream fill:#d9e8f6,stroke:#1f6fb2,color:#111;",
        "  classDef partial fill:#ffe5d0,stroke:#d9534f,color:#111;",
        "  classDef gated fill:#fff3cd,stroke:#d39e00,color:#111;",
        "```",
    ]
    return "\n".join(lines)


def main() -> None:
    raw = json.loads(NODES_JSON.read_text())
    # the exe emits titles only in the Node; carry them through if present
    for n in raw:
        n.setdefault("title", None)
    md = BLUEPRINT_MD.read_text()
    if BEGIN not in md or END not in md:
        raise SystemExit(f"markers not found in {BLUEPRINT_MD}; refusing to guess")
    block = f"{BEGIN}\n{render(raw)}\n{END}"
    new = re.sub(re.escape(BEGIN) + r".*?" + re.escape(END), block, md, flags=re.S)
    BLUEPRINT_MD.write_text(new)
    print(f"rendered {len(raw)} nodes + {len(EXTRA_NODES)} frontier into {BLUEPRINT_MD}")


if __name__ == "__main__":
    main()
