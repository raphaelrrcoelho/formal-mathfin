"""Generate ``MathFin/AxiomAuditGen.lean`` — the exhaustive axiom audit.

The curated ``MathFin/AxiomAudit.lean`` pins the *headliner* theorems with
dated, storied sections. This generator closes the complement: every MathFin
constant consumed in PROOF POSITION by any benchmark snippet gets a
``#guard_msgs``-pinned ``#print axioms`` check, so no benchmark-cited theorem
can pick up ``sorryAx`` (a ``sorry``) or a non-standard axiom without
breaking ``lake build``. With this file, "the audited set is representative,
not exhaustive" stops being true for the benchmark-facing surface.

Scope (documented, deliberate):

* *proof position* means a ``MathFin.*`` constant at the head of a proof term
  (immediately after ``:=``). Statement-position defs are exercised by
  elaboration + the verification ledger; ``library_wrapper`` entries cite
  upstream (Mathlib / BrownianMotion) names, whose axiom hygiene is
  upstream's contract.
* expected messages default to the three standard axioms; pure-algebra
  results that need fewer are recorded in ``EXPECTED_OVERRIDES`` (built
  empirically from build output — the build is the oracle).

Usage::

    python3 -m tools.verify.axiom_audit_gen --check   # exit 1 if stale
    python3 -m tools.verify.axiom_audit_gen --write   # regenerate in place

Freshness is enforced by ``tests/test_values.py::test_axiom_audit_gen_is_fresh``
(the blueprint anti-restale pattern: generated artifacts are never hand-edited
and regeneration must be a no-op).
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from tools.verify.corpus import iter_entries

GEN_PATH = Path("MathFin/AxiomAuditGen.lean")

# A MathFin constant at the head of a proof term: `:=` (possibly across a
# newline, possibly behind opening parens) immediately followed by the name.
# Named arguments inside proofs (`(h := MathFin.foo)`) are still proof
# position, so capturing them is correct.
PROOF_HEAD_RE = re.compile(r":=\s*\(*\s*(MathFin\.[A-Za-z_][A-Za-z0-9_.']*)")

STANDARD_AXIOMS = "[propext, Classical.choice, Quot.sound]"

# name -> full #guard_msgs doc-comment body, for results whose axiom set is a
# strict subset of the standard three (pure-algebra theorems). Populated from
# build output; the build is the oracle for these strings.
EXPECTED_OVERRIDES: dict[str, str] = {}


def collect_proof_position_names() -> list[str]:
    names: set[str] = set()
    for _path, theorem in iter_entries():
        code = theorem.get("code", {}).get("lean", "")
        names.update(PROOF_HEAD_RE.findall(code))
    return sorted(names)


def _guard_block(name: str) -> str:
    info = EXPECTED_OVERRIDES.get(
        name, f"info: '{name}' depends on axioms: {STANDARD_AXIOMS}"
    )
    return (
        f"/-- {info} -/\n"
        f"#guard_msgs (whitespace := lax) in #print axioms {name}\n"
    )


def generate() -> str:
    names = collect_proof_position_names()
    header = f"""/-
  GENERATED FILE — do not edit by hand.

  Exhaustive axiom audit: every MathFin constant consumed in PROOF POSITION
  by a benchmark snippet is #guard_msgs-pinned to its exact axiom set, so no
  benchmark-cited theorem can pick up `sorryAx` (a `sorry`) or a non-standard
  axiom without breaking `lake build`.

  The curated, storied audit is MathFin/AxiomAudit.lean (headliners + dated
  narrative); THIS file is its machine-written closure over the benchmark
  corpus ({len(names)} constants). Scope: proof-position MathFin names only —
  statement-position defs are exercised by elaboration + the verification
  ledger, and library_wrapper entries cite upstream names.

  Regenerate:  python3 -m tools.verify.axiom_audit_gen --write
  Freshness:   tests/test_values.py::test_axiom_audit_gen_is_fresh
  (Excluded from CI kernel replay like AxiomAudit: whole-library closure.)
-/
import MathFin

namespace MathFin.AxiomAuditGen

"""
    body = "\n".join(_guard_block(name) for name in names)
    return header + body + "\nend MathFin.AxiomAuditGen\n"


def main(argv: list[str]) -> int:
    mode = argv[0] if argv else "--check"
    content = generate()
    if mode == "--write":
        GEN_PATH.write_text(content)
        print(f"wrote {GEN_PATH} ({len(collect_proof_position_names())} guards)")
        return 0
    if mode == "--check":
        on_disk = GEN_PATH.read_text() if GEN_PATH.exists() else ""
        if on_disk != content:
            print(f"STALE: {GEN_PATH} does not match the generator output; "
                  "run `python3 -m tools.verify.axiom_audit_gen --write`")
            return 1
        print(f"fresh: {GEN_PATH}")
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
