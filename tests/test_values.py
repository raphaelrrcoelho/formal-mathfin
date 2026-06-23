"""Values gates — mechanical enforcement of the honesty contract over the
LIBRARY sources and the generated audit artifacts (complementing
``test_router.py``'s benchmark-level checks).

1. ``test_mathfin_sources_free_of_forbidden_text`` — scout/search/interactive
   tactics and trust-extending commands never land in committed ``MathFin/``
   sources: scout-not-author, offline-loop, and kernel-only trust, enforced
   textually (comments are stripped first, so prose may mention the words).
2. ``test_full_entries_are_not_definitional_rfl`` — a ``full`` entry's cited
   theorems (and the snippet's own declarations) must not be definitional
   ``rfl`` / ``unfold; rfl``: that is the ``reduced_core`` pattern in
   disguise. This is the entry-time version of the 2026-05-29 / 2026-06-03
   audit demotions (newton-raphson, pp-thm-3.3.5, mc-thm-1.1.2).
3. ``test_blueprint_spine_is_audited`` — every MathFin theorem on the curated
   blueprint spine is axiom-guarded in ``MathFin/AxiomAudit.lean``: the spine
   is curated prose + a generated dependency graph, the audit must be its
   superset (headliners are, at minimum, axiom-pinned).
4. ``test_axiom_audit_gen_is_fresh`` — ``MathFin/AxiomAuditGen.lean`` is
   byte-identical to the generator's output (generated artifacts are never
   hand-edited; regeneration is a no-op).
"""

import re
from pathlib import Path

from tools.verify.axiom_audit_gen import GEN_PATH, PROOF_HEAD_RE, generate
from tools.verify.corpus import iter_entries

AUDIT_PATH = Path("MathFin/AxiomAudit.lean")
BLUEPRINT_PATH = Path("MathFin/Blueprint.lean")


# --------------------------------------------------------------------------
# 1. forbidden text in library sources
# --------------------------------------------------------------------------

FORBIDDEN_PATTERNS = (
    (re.compile(r"\bsorry\b"), "sorry"),
    (re.compile(r"\badmit\b"), "admit"),
    (re.compile(r"\bnative_decide\b"),
     "native_decide extends the trusted base beyond the kernel"),
    (re.compile(r"\bpolyrith\b"), "polyrith calls an external service"),
    (re.compile(r"\bexact\?"), "exact? is an interactive-search leftover"),
    (re.compile(r"\bapply\?"), "apply? is an interactive-search leftover"),
    (re.compile(r"\brw\?"), "rw? is an interactive-search leftover"),
    (re.compile(r"\bsimp\?"), "simp? is an interactive-search leftover"),
    (re.compile(r"\bhammer\b"), "hammer output is a scout, not an author"),
    (re.compile(r"#loogle"), "#loogle queries an external service"),
    (re.compile(r"\bleansearch\b", re.IGNORECASE),
     "leansearch queries an external service"),
)

# (path-as-str, token) pairs, each with a justification comment.
FORBIDDEN_ALLOWLIST: set = set()


def _strip_comments(src: str) -> str:
    """Remove Lean comments (nested ``/- -/`` blocks incl. docstrings, and
    ``--`` line comments), preserving newlines so line numbers stay stable.
    String literals are respected so ``--`` inside a string survives."""
    out = []
    i, n = 0, len(src)
    depth = 0
    in_string = False
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth == 0 and not in_string and c == '"':
            in_string = True
            out.append(c)
            i += 1
            continue
        if in_string:
            if c == "\\":
                out.append(c)
                out.append(nxt)
                i += 2
                continue
            if c == '"':
                in_string = False
            out.append(c)
            i += 1
            continue
        if c == "/" and nxt == "-":
            depth += 1
            i += 2
            continue
        if depth > 0:
            if c == "-" and nxt == "/":
                depth -= 1
                i += 2
                continue
            if c == "\n":
                out.append(c)
            i += 1
            continue
        if c == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def test_mathfin_sources_free_of_forbidden_text() -> None:
    failures = []
    for path in sorted(Path("MathFin").rglob("*.lean")):
        stripped = _strip_comments(path.read_text())
        for pattern, why in FORBIDDEN_PATTERNS:
            for m in pattern.finditer(stripped):
                token = m.group()
                if (str(path), token) in FORBIDDEN_ALLOWLIST:
                    continue
                line = stripped.count("\n", 0, m.start()) + 1
                failures.append(f"{path}:{line}: `{token}` — {why}")
    assert not failures, (
        "forbidden text in library sources (allowlist with a justification "
        "comment if genuinely deliberate):\n  " + "\n  ".join(failures)
    )


# --------------------------------------------------------------------------
# 2. definitional-rfl tripwire for `full` entries
# --------------------------------------------------------------------------

DECL_RE = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma)\s+"
    r"([A-Za-z_][\w.']*)",
    re.MULTILINE,
)

# The rfl class: a proof whose entire content is a definitional unfold.
RFL_TAIL_RE = re.compile(
    r"^(?:Iff\.)?rfl$|^by\s+(?:unfold\s+[\w.\s,]+;\s*)?rfl$"
)

# Entry ids allowed to cite an rfl-class declaration, each justified.
# (Definition entries — id containing "-def-" — are skipped wholesale: the
# documented definitional-`full` convention, see test_router.py's
# DEFINITIONAL_FULL_ALLOWLIST.)
# mf-caplet-price / mf-floorlet-price: Black-76 caplet/floorlet are genuine
# definitions load-bearing for the spine; the benchmark theorem is their
# definitional unfolding, which is the documented definitional-full pattern.
DEFINITIONAL_RFL_ALLOWLIST: set = {
    "mf-caplet-price",
    "mf-floorlet-price",
}


def _decl_tails(text: str):
    """Yield ``(decl_name, proof_tail)`` for every column-0 theorem/lemma.

    The block runs to the next column-0 non-space line; the proof tail is
    whatever follows the LAST ``:=`` in the block (good enough to recognize
    the rfl class: an `rfl` tail that terminates an inner `have` would not
    strip to exactly `rfl`)."""
    lines = text.splitlines()
    starts = []  # (line_idx, name)
    for idx, line in enumerate(lines):
        m = DECL_RE.match(line)
        if m:
            starts.append((idx, m.group(1)))
    for pos, (idx, name) in enumerate(starts):
        end = len(lines)
        for j in range(idx + 1, len(lines)):
            if lines[j][:1] not in ("", " ", "\t"):
                end = j
                break
        block = "\n".join(lines[idx:end])
        cut = block.rfind(":=")
        tail = block[cut + 2:].strip() if cut != -1 else ""
        yield name, tail


def _mathfin_decl_tail_index() -> dict:
    index: dict = {}
    for path in sorted(Path("MathFin").rglob("*.lean")):
        text = _strip_comments(path.read_text())
        for name, tail in _decl_tails(text):
            index.setdefault(name.split(".")[-1], []).append((str(path), tail))
    return index


def test_full_entries_are_not_definitional_rfl() -> None:
    index = _mathfin_decl_tail_index()
    failures = []
    for path, theorem in iter_entries():
        if theorem.get("metadata", {}).get("formalization_status") != "full":
            continue
        tid = theorem["id"]
        if "-def-" in tid or tid in DEFINITIONAL_RFL_ALLOWLIST:
            continue
        code = theorem.get("code", {}).get("lean", "")
        # (a) the snippet's own declarations (the old mc-thm-1.1.2 shape)
        for name, tail in _decl_tails(code):
            if tail and RFL_TAIL_RE.match(tail):
                failures.append(f"{tid} ({path.name}): snippet decl "
                                f"`{name}` is rfl-class: `{tail}`")
        # (b) the cited module theorems
        for full_name in sorted(set(PROOF_HEAD_RE.findall(code))):
            short = full_name.split(".")[-1]
            for fpath, tail in index.get(short, []):
                if tail and RFL_TAIL_RE.match(tail):
                    failures.append(f"{tid} ({path.name}): cites {full_name} "
                                    f"({fpath}) whose proof is rfl-class: "
                                    f"`{tail}`")
    assert not failures, (
        "`full` entries backed by definitional-rfl proofs (the reduced_core "
        "pattern in disguise — demote, derive, or allowlist with a "
        "justification):\n  " + "\n  ".join(failures)
    )


# --------------------------------------------------------------------------
# 3. blueprint spine ⊆ axiom audit
# --------------------------------------------------------------------------

# Spine nodes tagged on upstream constants (Mathlib / BrownianMotion
# namespaces) are out of audit scope by design.
def _blueprint_tagged_names() -> list:
    text = _strip_comments(BLUEPRINT_PATH.read_text())
    lines = text.splitlines()
    names = []
    attr_count = 0
    i = 0
    name_line = re.compile(r"^\s+([A-Za-z_][\w.']*)\s*$")
    while i < len(lines):
        if "attribute [blueprint" in lines[i]:
            attr_count += 1
            # single-line form: `attribute [blueprint "x"] Name`
            m = re.search(r"\]\s+([A-Za-z_][\w.']+)\s*$", lines[i])
            if m:
                names.append(m.group(1))
                i += 1
                continue
            # multi-line form: name on the first identifier-only line after
            # the line that closes the attribute (ends with `)]` or `]`).
            j = i
            while j < len(lines) and not lines[j].rstrip().endswith("]"):
                j += 1
            j += 1
            while j < len(lines) and not lines[j].strip():
                j += 1
            m2 = name_line.match(lines[j]) if j < len(lines) else None
            assert m2, (
                f"could not parse blueprint attribute near "
                f"{BLUEPRINT_PATH}:{i + 1}"
            )
            names.append(m2.group(1))
            i = j + 1
            continue
        i += 1
    assert len(names) == attr_count, (
        "blueprint tag parser drift: "
        f"{attr_count} attributes, {len(names)} names parsed"
    )
    return names


def _audited_names() -> set:
    return set(re.findall(r"#print axioms\s+([A-Za-z_][\w.']*)",
                          AUDIT_PATH.read_text()))


def test_blueprint_spine_is_audited() -> None:
    audited = _audited_names()
    missing = [
        name for name in _blueprint_tagged_names()
        if name.startswith("MathFin.") and name not in audited
    ]
    assert not missing, (
        "blueprint spine nodes missing from the curated axiom audit "
        "(every headliner must be axiom-pinned — add a #guard_msgs block to "
        "MathFin/AxiomAudit.lean):\n  " + "\n  ".join(missing)
    )


# --------------------------------------------------------------------------
# 4. generated exhaustive audit is fresh
# --------------------------------------------------------------------------

def test_axiom_audit_gen_is_fresh() -> None:
    assert GEN_PATH.exists(), (
        f"{GEN_PATH} is missing — run "
        "`python3 -m tools.verify.axiom_audit_gen --write`"
    )
    assert GEN_PATH.read_text() == generate(), (
        f"{GEN_PATH} is stale relative to the benchmark corpus — run "
        "`python3 -m tools.verify.axiom_audit_gen --write` and commit the "
        "result (generated artifacts are never hand-edited)"
    )


# --------------------------------------------------------------------------
# 5. the values review (the judgment lenses) actually happens
# --------------------------------------------------------------------------

# The eight judgment lenses (docs/values-review.md) cannot be checked by a
# machine — but "nobody looked" can. A recorded multi-agent review must
# cover the corpus to within one session's growth.
VALUES_REVIEW_PATH = Path("docs/values-review.md")
REVIEW_HEADER_RE = re.compile(
    r"^## \d{4}-\d{2}-\d{2} — commit [0-9a-f]{7,} — corpus (\d+)",
    re.MULTILINE,
)
REVIEW_SLACK_ENTRIES = 12


def test_values_review_is_current() -> None:
    text = VALUES_REVIEW_PATH.read_text()
    reviewed_counts = [int(m.group(1)) for m in REVIEW_HEADER_RE.finditer(text)]
    assert reviewed_counts, (
        f"{VALUES_REVIEW_PATH} has no parseable verdict block — run the "
        "values-review panel (see the protocol in that file) and record it"
    )
    corpus = sum(1 for _ in iter_entries())
    newest = max(reviewed_counts)
    assert corpus - newest <= REVIEW_SLACK_ENTRIES, (
        f"the corpus has {corpus} entries but the latest recorded values "
        f"review covered {newest} — more than {REVIEW_SLACK_ENTRIES} entries "
        "of unreviewed growth. Run the multi-agent values review "
        "(docs/values-review.md) and record the verdict before pushing more "
        "proof content."
    )
