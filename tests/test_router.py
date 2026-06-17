import json
import re
from pathlib import Path

from tools.verify.models import Backend, Domain
from tools.verify.router import Router


ALLOWED_FORMALIZATION_STATUSES = {
    "full",
    "library_wrapper",
    "reduced_core",
    "placeholder",
}

# Word-boundary match so legitimate words ("admitted", "admittedly", "sorries")
# don't false-positive; the real guarantee is AxiomAudit's build-time `sorryAx`
# check, this is the cheap textual gate.
SORRY_ADMIT_RE = re.compile(r"\b(?:sorry|admit)\b")

# A `full` benchmark must not encode its conclusion as an *assumed* field of a
# `Prop`-valued structure that the proof merely projects — that is the
# `reduced_core` pattern (the textbook statement bundled as a hypothesis and read
# off by a structural projection). The lazy match runs `structure` → the first
# `: Prop where`.
PROP_STRUCTURE_RE = re.compile(r"\bstructure\b[\s\S]*?:\s*Prop\s+where")

# The only legitimate `full` benchmarks that define a Prop-valued structure are
# those *defining a stochastic object* as a predicate: its bundled fields are the
# object's defining properties (not theorems), so projecting/deriving one is
# faithful for a *definition* benchmark. Any new `full` benchmark bundling a
# Prop-structure trips the test below, forcing a conscious choice between
# "genuine definition → allowlist with justification" and "assumed conclusion
# → reduced_core".
DEFINITIONAL_FULL_ALLOWLIST = {
    "bm-def-5.1.1",    # StandardBrownianMotion definition (Saporito Def 5.1.1)
    "cv-poisson-def",  # PoissonProcess definition
    # "pp-thm-3.3.5" was removed 2026-06-03: it is a THEOREM entry (marginal law)
    # whose conclusion is a projected structure field, so it was demoted to
    # reduced_core (see EXPECTED_REDUCED_CORE_THEOREMS) — definition entries keep
    # the allowlist convention; theorem entries do not.
}

PLACEHOLDER_PATTERNS = (
    "example : true := trivial",
    "∀ (b :",
    "∀ (x :",
    "(0 : ℝ) = 0",
    "formal placeholder",
)

EXPECTED_FULL_THEOREMS = {
    "bm-def-5.1.1",
    "cv-poisson-def",
    "mc-def-1.1.1",
    "mc-prop-1.2.3",
    "mc-prop-1.4.13",
    # 2026-06-05 Poisson-cluster + Itô-QV upgrade round: conclusions are now
    # DERIVED (PoissonSuperposition / PoissonThinning / PoissonCounting /
    # ItoProcessQV in Foundations/), not structure-field projections.
    "pp-thm-3.3.5",
    "pp-thm-3.3.9",
    "pp-thm-3.3.10",
    "sc-thm-7.4.5",
    # 2026-06-17 Caplet/floorlet round: Black-76 specialisation for the
    # interest-rate caplet/floorlet + parity theorem, mirroring the
    # swaption parity already on the spine.
    "mf-caplet-price",
    "mf-floorlet-price",
    "mf-caplet-floorlet-parity",
}

# Deliberate audit pins: entries kept at exactly `reduced_core` so they can
# neither silently regress to placeholder nor be re-promoted without a
# genuine derivation. (mc-thm-1.1.2 left this list 2026-06-06: the
# Ionescu-Tulcea path-measure derivation landed in
# Foundations/MarkovPathMeasure.lean and the entry is `full` now.)
EXPECTED_REDUCED_CORE_THEOREMS = {
    # pp-prop-3.3.6 stays reduced_core HONESTLY: the first interarrival's
    # exponential law + memorylessness are derived (PoissonInterarrival), but
    # the textbook's whole-sequence iid claim needs the strong Markov property.
    "pp-prop-3.3.6",
    # (mf-kelly-n-periods-linearity was demoted here 2026-06-06 by the
    # definitional-rfl tripwire and re-promoted the same day: the n-period
    # iid model is now real — Measure.pi of the two-point return law +
    # linearity of expectation in Performance/Kelly.lean.)
}

EXPECTED_NON_PLACEHOLDER_THEOREMS = {
    "bm-cor-5.3.4",
}


def _iter_theorems():
    for path in Path("benchmarks").glob("*.json"):
        data = json.loads(path.read_text())
        theorems = data.get("theorems", data)
        for theorem in theorems:
            yield path, theorem


# Lean module-system exposure guard. A `module`-header file whose declarations
# are not under a `public section` exports NOTHING: importers see no names while
# `lake build` stays green (this silently broke sc-thm-6.2.5 via the Wiener
# pair — the only two modules with zero in-library consumers — found 2026-06-04).
# No deliberately-private modules exist; add any future one here with a comment.
MODULE_PRIVATE_ALLOWLIST: set = set()

MODULE_HEADER_RE = re.compile(r"^module\s*$", re.MULTILINE)


def test_mathfin_module_files_expose_public_section() -> None:
    for path in Path("MathFin").rglob("*.lean"):
        if str(path) in MODULE_PRIVATE_ALLOWLIST:
            continue
        text = path.read_text()
        if MODULE_HEADER_RE.search(text) and "public section" not in text:
            raise AssertionError(
                f"{path} uses the Lean module system but has no `public section` — "
                "its declarations are module-private and invisible to importers "
                "while the build stays green. Add `@[expose] public section` after "
                "the module docstring (library-wide convention), or allowlist with "
                "a justification."
            )


def test_tooling_packages_not_imported_by_library() -> None:
    """Soundness boundary for ``ledger.PIN_EXCLUDED_PACKAGES``: tooling-only
    Lake deps (LeanArchitect's ``Architect``) may be imported ONLY by the
    blueprint leaf modules (``MathFin/Blueprint*``), which no benchmark entry
    can reach. If this import ever spreads into a proof module, the ledger's
    pin-hash exclusion becomes unsound — the fix is to remove the package
    from PIN_EXCLUDED_PACKAGES (restaling the corpus, as it then must)."""
    tooling_import_re = re.compile(
        r"^\s*(?:public\s+)?import(?:\s+all)?\s+"
        r"(Architect|Hammer|Duper|Auto|PremiseSelection)\b",
        re.MULTILINE,
    )
    allowed = {Path("MathFin/Blueprint.lean"), Path("MathFin/Blueprint/Export.lean")}
    for path in Path("MathFin").rglob("*.lean"):
        if path in allowed:
            continue
        m = tooling_import_re.search(path.read_text())
        if m:
            raise AssertionError(
                f"{path} imports the tooling-only package {m.group(1)} — "
                "library/benchmark code must never depend on the scout "
                "toolchain (see ledger.PIN_EXCLUDED_PACKAGES; hammer pilot "
                "files live under tests/, Architect only in "
                "MathFin/Blueprint*.lean)."
            )


def test_default_routes_are_lean_only() -> None:
    router = Router()

    for domain in Domain:
        decision = router.route(domain)
        assert decision.backends == [Backend.LEAN], (domain, decision.backends)


def test_benchmarks_do_not_expose_nonlean_code() -> None:
    # Lean is the sole backend; sympy/isabelle were stripped from the repo.
    for path, theorem in _iter_theorems():
        code_keys = set(theorem.get("code", {}))
        assert code_keys <= {"lean"}, (path, theorem["id"], code_keys)


def test_benchmarks_have_no_dropped_backend_residue() -> None:
    # No leftover sympy CAS references or isabelle_* metadata anywhere.
    for path, theorem in _iter_theorems():
        metadata = theorem.get("metadata", {})
        assert "cas_reference" not in metadata, (path, theorem["id"])
        assert "cas_reference_note" not in metadata, (path, theorem["id"])
        residue = [
            k for k in metadata
            if "isabelle" in k.lower() or "sympy" in k.lower() or "cas_" in k.lower()
        ]
        assert not residue, (path, theorem["id"], residue)


def test_benchmarks_do_not_contain_sorry_or_admit() -> None:
    for path, theorem in _iter_theorems():
        for backend, code in theorem.get("code", {}).items():
            match = SORRY_ADMIT_RE.search(code.lower())
            assert match is None, (path, theorem["id"], backend, match and match.group())


def test_full_benchmarks_do_not_bundle_assumed_prop_structures() -> None:
    # Turns the full-vs-reduced_core honesty convention into an enforced
    # invariant: a `full` benchmark may not bundle its conclusion as an assumed
    # Prop-structure field unless it is an explicitly-justified definitional
    # benchmark (see DEFINITIONAL_FULL_ALLOWLIST).
    for path, theorem in _iter_theorems():
        status = theorem.get("metadata", {}).get("formalization_status")
        if status != "full":
            continue
        code = "\n".join(theorem.get("code", {}).values())
        if PROP_STRUCTURE_RE.search(code) and theorem["id"] not in DEFINITIONAL_FULL_ALLOWLIST:
            raise AssertionError(
                f"{theorem['id']} ({path}) is `full` but defines a Prop-valued "
                "structure. If the proof projects an assumed conclusion it must be "
                "`reduced_core`; if it genuinely defines a stochastic object, add "
                "it to DEFINITIONAL_FULL_ALLOWLIST with a justification comment."
            )


def test_benchmarks_declare_formalization_status() -> None:
    for path, theorem in _iter_theorems():
        status = theorem.get("metadata", {}).get("formalization_status")
        assert status in ALLOWED_FORMALIZATION_STATUSES, (
            path,
            theorem["id"],
            status,
        )


def test_full_statuses_do_not_use_obvious_placeholders() -> None:
    for path, theorem in _iter_theorems():
        status = theorem.get("metadata", {}).get("formalization_status")
        code = "\n".join(theorem.get("code", {}).values())
        lowered = code.lower()
        has_placeholder = any(pattern.lower() in lowered for pattern in PLACEHOLDER_PATTERNS)

        if has_placeholder:
            assert status == "placeholder", (path, theorem["id"], status)
        if status in {"full", "library_wrapper"}:
            assert not has_placeholder, (path, theorem["id"], status)


def test_expected_promotions_are_full_theorems() -> None:
    statuses = {
        theorem["id"]: theorem.get("metadata", {}).get("formalization_status")
        for _, theorem in _iter_theorems()
    }

    for theorem_id in EXPECTED_FULL_THEOREMS:
        assert statuses.get(theorem_id) == "full", (
            theorem_id,
            statuses.get(theorem_id),
        )


def test_expected_reduced_cores_stay_reduced_core() -> None:
    statuses = {
        theorem["id"]: theorem.get("metadata", {}).get("formalization_status")
        for _, theorem in _iter_theorems()
    }

    for theorem_id in EXPECTED_REDUCED_CORE_THEOREMS:
        assert statuses.get(theorem_id) == "reduced_core", (
            theorem_id,
            statuses.get(theorem_id),
        )


def test_expected_placeholder_removals_are_not_placeholders() -> None:
    statuses = {
        theorem["id"]: theorem.get("metadata", {}).get("formalization_status")
        for _, theorem in _iter_theorems()
    }

    for theorem_id in EXPECTED_NON_PLACEHOLDER_THEOREMS:
        assert statuses.get(theorem_id) != "placeholder", (
            theorem_id,
            statuses.get(theorem_id),
        )
