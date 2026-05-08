"""Confidence scoring logic for verification results."""

from .models import (
    Backend,
    BackendResult,
    ConfidenceLevel,
    VerificationResult,
    VerificationStatus,
)


def _result_confidence(result: BackendResult) -> ConfidenceLevel:
    """Determine confidence level for a single backend result."""
    if result.status == VerificationStatus.SUCCESS:
        if result.backend in (Backend.LEAN, Backend.ISABELLE):
            return ConfidenceLevel.L5
        # SymPy symbolic check
        return ConfidenceLevel.L2

    if result.status == VerificationStatus.PARTIAL:
        if result.backend in (Backend.LEAN, Backend.ISABELLE):
            return ConfidenceLevel.L4 if result.sorry_count <= 1 else ConfidenceLevel.L3
        return ConfidenceLevel.L1

    return ConfidenceLevel.L0


def compute_overall_confidence(vr: VerificationResult) -> ConfidenceLevel:
    """Compute the overall confidence from all backend results.

    Priority:
    - L5 if any formal prover (Lean/Isabelle) succeeded fully
    - L4 if a formal prover partially succeeded (1 sorry)
    - L3 if a formal prover partially succeeded (>1 sorry)
    - L2 if SymPy symbolic check succeeded
    - L1 if SymPy numerical check succeeded
    - L0 otherwise
    """
    if not vr.results:
        return ConfidenceLevel.L0

    best = ConfidenceLevel.L0
    for result in vr.results.values():
        level = _result_confidence(result)
        if level > best:
            best = level

    return best


def annotate_cross_validation(vr: VerificationResult) -> None:
    """Mark metadata when both Lean and Isabelle succeed on the same theorem.

    Cross-validation by independent provers provides extra assurance
    beyond what either backend alone can give.
    """
    lean_ok = (
        Backend.LEAN in vr.results
        and vr.results[Backend.LEAN].status == VerificationStatus.SUCCESS
    )
    isabelle_ok = (
        Backend.ISABELLE in vr.results
        and vr.results[Backend.ISABELLE].status == VerificationStatus.SUCCESS
    )

    if lean_ok and isabelle_ok:
        # Can't mutate frozen TheoremStatement.metadata directly,
        # but the dict itself is mutable.
        vr.theorem.metadata["cross_validated"] = True
        vr.theorem.metadata["cross_validation_backends"] = ["lean", "isabelle"]
