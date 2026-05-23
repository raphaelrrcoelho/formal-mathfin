"""SymPy-based symbolic verification backend.

Provides algebraic identity checks, moment computations, distribution
property verification, and numerical evaluations. Always returns L2
(symbolic) or L1 (numerical) confidence — never L5.
"""

from __future__ import annotations

import time
import traceback
from enum import Enum
from typing import Any

from .models import (
    Backend,
    BackendResult,
    ConfidenceLevel,
    TheoremStatement,
    VerificationStatus,
)


class SymPyCheckKind(Enum):
    """Types of SymPy verification checks."""
    ALGEBRAIC_IDENTITY = "algebraic_identity"
    MOMENT_COMPUTATION = "moment_computation"
    DISTRIBUTION_PROPERTY = "distribution_property"
    DERIVATIVE_CHECK = "derivative_check"
    INTEGRAL_CHECK = "integral_check"
    NUMERICAL_EVALUATION = "numerical_evaluation"


class SymPyVerifier:
    """Verification backend using SymPy for symbolic/numerical checks."""

    @property
    def name(self) -> str:
        return "sympy"

    def is_available(self) -> bool:
        try:
            import sympy  # noqa: F401
            return True
        except ImportError:
            return False

    def shutdown(self) -> None:
        pass  # No persistent resources

    async def verify(
        self,
        theorem: TheoremStatement,
        timeout: float = 60.0,
    ) -> BackendResult:
        """Run SymPy verification on the theorem."""
        start = time.monotonic()

        if not self.is_available():
            return BackendResult(
                backend=Backend.SYMPY,
                status=VerificationStatus.UNAVAILABLE,
                error_message="sympy not installed",
            )

        code = theorem.code.get(Backend.SYMPY)
        if not code:
            return BackendResult(
                backend=Backend.SYMPY,
                status=VerificationStatus.NOT_ATTEMPTED,
                error_message="No SymPy code provided for this theorem",
            )

        check_kind = theorem.metadata.get("sympy_check_kind")
        try:
            if check_kind:
                kind = SymPyCheckKind(check_kind)
                result = self._dispatch(kind, code, theorem.metadata)
            else:
                result = self._eval_code(code)

            elapsed = time.monotonic() - start

            if result.get("verified"):
                confidence = (
                    ConfidenceLevel.L2
                    if result.get("mode", "symbolic") == "symbolic"
                    else ConfidenceLevel.L1
                )
                return BackendResult(
                    backend=Backend.SYMPY,
                    status=VerificationStatus.SUCCESS,
                    confidence=confidence,
                    raw_output=str(result),
                    elapsed_seconds=elapsed,
                )
            else:
                return BackendResult(
                    backend=Backend.SYMPY,
                    status=VerificationStatus.FAILED,
                    confidence=ConfidenceLevel.L0,
                    raw_output=str(result),
                    error_message=result.get("error", "Check returned False"),
                    elapsed_seconds=elapsed,
                )

        except Exception as e:
            elapsed = time.monotonic() - start
            return BackendResult(
                backend=Backend.SYMPY,
                status=VerificationStatus.FAILED,
                confidence=ConfidenceLevel.L0,
                raw_output=traceback.format_exc(),
                error_message=str(e),
                elapsed_seconds=elapsed,
            )

    def _dispatch(
        self, kind: SymPyCheckKind, code: str, metadata: dict[str, Any]
    ) -> dict[str, Any]:
        """Dispatch to specialized check method."""
        handlers = {
            SymPyCheckKind.ALGEBRAIC_IDENTITY: self._check_algebraic_identity,
            SymPyCheckKind.MOMENT_COMPUTATION: self._check_moment,
            SymPyCheckKind.DISTRIBUTION_PROPERTY: self._check_distribution,
            SymPyCheckKind.DERIVATIVE_CHECK: self._check_derivative,
            SymPyCheckKind.INTEGRAL_CHECK: self._check_integral,
            SymPyCheckKind.NUMERICAL_EVALUATION: self._check_numerical,
        }
        handler = handlers[kind]
        return handler(code, metadata)

    def _eval_code(self, code: str) -> dict[str, Any]:
        """Evaluate a code string that should return a verification dict.

        The code is expected to define a `result` variable that is a dict
        with at least a 'verified' key.
        """
        import sympy  # noqa: F401

        namespace: dict[str, Any] = {"sympy": __import__("sympy")}
        # Controlled execution of user-provided verification code
        exec(code, namespace)  # noqa: S102

        if "result" in namespace:
            return namespace["result"]
        if "verified" in namespace:
            return {"verified": namespace["verified"], "mode": "symbolic"}
        return {"verified": False, "error": "Code did not set 'result' or 'verified'"}

    def _check_algebraic_identity(
        self, code: str, metadata: dict[str, Any]
    ) -> dict[str, Any]:
        """Check that an algebraic identity holds symbolically."""
        import sympy

        namespace: dict[str, Any] = {"sympy": sympy}
        exec(code, namespace)  # noqa: S102

        lhs = namespace.get("lhs")
        rhs = namespace.get("rhs")
        if lhs is None or rhs is None:
            return {"verified": False, "error": "Code must define 'lhs' and 'rhs'"}

        diff = sympy.simplify(lhs - rhs)
        verified = diff == 0
        return {"verified": verified, "mode": "symbolic", "diff": str(diff)}

    def _check_moment(
        self, code: str, metadata: dict[str, Any]
    ) -> dict[str, Any]:
        """Check moment computations (E[X], E[X²], Var[X], etc.)."""
        import sympy

        namespace: dict[str, Any] = {"sympy": sympy}
        exec(code, namespace)  # noqa: S102

        expected = namespace.get("expected")
        computed = namespace.get("computed")
        if expected is None or computed is None:
            return {
                "verified": False,
                "error": "Code must define 'expected' and 'computed'",
            }

        diff = sympy.simplify(expected - computed)
        verified = diff == 0
        return {"verified": verified, "mode": "symbolic", "diff": str(diff)}

    def _check_distribution(
        self, code: str, metadata: dict[str, Any]
    ) -> dict[str, Any]:
        """Check distribution properties (PDF integrates to 1, CDF limits, etc.)."""
        import sympy

        namespace: dict[str, Any] = {"sympy": sympy}
        exec(code, namespace)  # noqa: S102

        return namespace.get("result", {"verified": False, "error": "No result"})

    def _check_derivative(
        self, code: str, metadata: dict[str, Any]
    ) -> dict[str, Any]:
        """Check derivative computations."""
        import sympy

        namespace: dict[str, Any] = {"sympy": sympy}
        exec(code, namespace)  # noqa: S102

        expr = namespace.get("expr")
        var = namespace.get("var")
        expected = namespace.get("expected")
        if expr is None or var is None or expected is None:
            return {
                "verified": False,
                "error": "Code must define 'expr', 'var', and 'expected'",
            }

        computed = sympy.diff(expr, var)
        diff = sympy.simplify(computed - expected)
        verified = diff == 0
        return {
            "verified": verified,
            "mode": "symbolic",
            "computed": str(computed),
            "diff": str(diff),
        }

    def _check_integral(
        self, code: str, metadata: dict[str, Any]
    ) -> dict[str, Any]:
        """Check integral computations."""
        import sympy

        namespace: dict[str, Any] = {"sympy": sympy}
        exec(code, namespace)  # noqa: S102

        integrand = namespace.get("integrand")
        var = namespace.get("var")
        limits = namespace.get("limits")
        expected = namespace.get("expected")
        if integrand is None or var is None or expected is None:
            return {
                "verified": False,
                "error": "Code must define 'integrand', 'var', and 'expected'",
            }

        if limits:
            computed = sympy.integrate(integrand, (var, *limits))
        else:
            computed = sympy.integrate(integrand, var)

        diff = sympy.simplify(computed - expected)
        verified = diff == 0
        return {
            "verified": verified,
            "mode": "symbolic",
            "computed": str(computed),
            "diff": str(diff),
        }

    def _check_numerical(
        self, code: str, metadata: dict[str, Any]
    ) -> dict[str, Any]:
        """Run numerical evaluation and check tolerance."""
        namespace: dict[str, Any] = {"sympy": __import__("sympy")}
        exec(code, namespace)  # noqa: S102

        return namespace.get(
            "result",
            {"verified": False, "mode": "numerical", "error": "No result"},
        )
