"""Confidence scoring logic for verification results."""

from .models import (
    BackendResult,
    ConfidenceLevel,
    VerificationResult,
    VerificationStatus,
)


def _result_confidence(result: BackendResult) -> ConfidenceLevel:
    """Determine the confidence level for a single Lean backend result."""
    if result.status == VerificationStatus.SUCCESS:
        return ConfidenceLevel.L5
    if result.status == VerificationStatus.PARTIAL:
        return ConfidenceLevel.L4 if result.sorry_count <= 1 else ConfidenceLevel.L3
    return ConfidenceLevel.L0


def compute_overall_confidence(vr: VerificationResult) -> ConfidenceLevel:
    """Compute the overall confidence from all backend results.

    - L5 if Lean succeeded fully
    - L4 if Lean partially succeeded (≤1 sorry)
    - L3 if Lean partially succeeded (>1 sorry)
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
