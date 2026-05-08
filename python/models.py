"""Data models for the hybrid verification system."""

from __future__ import annotations

import time
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Protocol, runtime_checkable


class Domain(Enum):
    """Mathematical domain classification for routing."""
    MARKOV_CHAINS = "markov_chains"
    ERGODIC_THEORY = "ergodic_theory"
    CLT = "central_limit_theorem"
    MARTINGALES = "martingales"
    STOPPING_TIMES = "stopping_times"
    BROWNIAN_MOTION = "brownian_motion"
    MEASURE_THEORY = "measure_theory"
    STOCHASTIC_CALCULUS = "stochastic_calculus"
    SDES = "stochastic_differential_equations"
    MATHEMATICAL_FINANCE = "mathematical_finance"
    POISSON_PROCESSES = "poisson_processes"


class Backend(Enum):
    """Available verification backends."""
    LEAN = "lean"
    ISABELLE = "isabelle"
    SYMPY = "sympy"


class ConfidenceLevel(Enum):
    """Tiered confidence levels L0-L5."""
    L0 = 0  # No verification attempted or all failed
    L1 = 1  # Numerical spot-check only (SymPy numerical)
    L2 = 2  # Symbolic CAS verification (SymPy algebraic)
    L3 = 3  # Partial formal proof (sorry/admit present)
    L4 = 4  # Formal proof with caveats (axioms, partial)
    L5 = 5  # Full machine-checked formal proof

    def __lt__(self, other: ConfidenceLevel) -> bool:
        return self.value < other.value

    def __le__(self, other: ConfidenceLevel) -> bool:
        return self.value <= other.value

    def __gt__(self, other: ConfidenceLevel) -> bool:
        return self.value > other.value

    def __ge__(self, other: ConfidenceLevel) -> bool:
        return self.value >= other.value


class VerificationStatus(Enum):
    """Outcome of a single backend verification attempt."""
    SUCCESS = "success"
    PARTIAL = "partial"       # Proof has sorry/admit
    FAILED = "failed"
    TIMEOUT = "timeout"
    UNAVAILABLE = "unavailable"  # Backend not installed/reachable
    NOT_ATTEMPTED = "not_attempted"


@dataclass(frozen=True)
class TheoremStatement:
    """A theorem to be verified, with code for one or more backends."""
    id: str
    name: str
    description: str
    domain: Domain
    code: dict[Backend, str] = field(default_factory=dict)
    metadata: dict[str, Any] = field(default_factory=dict)

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> TheoremStatement:
        """Deserialize from a JSON-compatible dict."""
        domain = Domain(d["domain"])
        code = {Backend(k): v for k, v in d.get("code", {}).items()}
        return cls(
            id=d["id"],
            name=d["name"],
            description=d.get("description", ""),
            domain=domain,
            code=code,
            metadata=d.get("metadata", {}),
        )


@dataclass
class BackendResult:
    """Result from a single backend verification attempt."""
    backend: Backend
    status: VerificationStatus = VerificationStatus.NOT_ATTEMPTED
    confidence: ConfidenceLevel = ConfidenceLevel.L0
    raw_output: str = ""
    error_message: str = ""
    sorry_count: int = 0
    goals_remaining: int = 0
    elapsed_seconds: float = 0.0


@dataclass
class VerificationResult:
    """Aggregated result across all backends for a single theorem."""
    theorem: TheoremStatement
    results: dict[Backend, BackendResult] = field(default_factory=dict)
    overall_confidence: ConfidenceLevel = ConfidenceLevel.L0
    timestamp: float = field(default_factory=time.time)

    @property
    def is_verified(self) -> bool:
        """True if any backend achieved SUCCESS status."""
        return any(
            r.status == VerificationStatus.SUCCESS
            for r in self.results.values()
        )

    @property
    def best_result(self) -> BackendResult | None:
        """Return the result with highest confidence."""
        if not self.results:
            return None
        return max(self.results.values(), key=lambda r: r.confidence.value)


@runtime_checkable
class VerificationBackend(Protocol):
    """Protocol that all verification backends must implement."""

    @property
    def name(self) -> str: ...

    def is_available(self) -> bool: ...

    async def verify(
        self,
        theorem: TheoremStatement,
        timeout: float = 60.0,
    ) -> BackendResult: ...

    def shutdown(self) -> None: ...
