"""Lean 4 verification backend using lean-interact."""

from __future__ import annotations

import logging
import shutil
import threading
import time
from typing import Any, Sequence

from .config import LeanRequireSpec
from .models import (
    Backend,
    BackendResult,
    ConfidenceLevel,
    TheoremStatement,
    VerificationStatus,
)

logger = logging.getLogger(__name__)


class LeanBackend:
    """Lean 4 backend using lean-interact's AutoLeanServer with Mathlib support."""

    def __init__(
        self,
        lean_version: str = "v4.30.0-rc1",
        mathlib: bool = True,
        mathlib_rev: str | None = None,
        extra_requires: Sequence[LeanRequireSpec] = (),
        local_project: str | None = None,
    ):
        self._lean_version = lean_version
        self._mathlib = mathlib
        self._mathlib_rev = mathlib_rev
        self._extra_requires = tuple(extra_requires)
        self._local_project = local_project
        self._server: Any = None
        self._project: Any = None
        self._lock = threading.Lock()

    @property
    def name(self) -> str:
        return "lean"

    def is_available(self) -> bool:
        """Check if lean-interact and the Lean toolchain are installed."""
        try:
            import lean_interact  # noqa: F401
        except ImportError:
            return False
        return shutil.which("lake") is not None

    def _ensure_server(self) -> None:
        """Lazily initialize the Lean server (defers expensive Mathlib setup).

        Two project modes:

        * ``LocalProject`` — used when ``local_project`` is set. Points at an
          existing Lake project on disk (its ``lakefile.lean`` is authoritative
          for ``require``s). Lake builds it once via ``auto_build=True`` then
          caches; benchmark snippets only need to typecheck against the
          pre-built library, so complex derivations that would OOM the REPL
          elaborator can live as real Lean files inside the project. The
          ``mathlib`` / ``mathlib_rev`` / ``extra_requires`` fields are
          ignored in this mode.
        * ``TempRequireProject`` — default. Synthesizes an ad-hoc project from
          the require list for each verification call. Fine for short
          wrappers; the whole proof has to elaborate from scratch in the
          single REPL turn.
        """
        if self._server is not None:
            return

        from lean_interact import (
            AutoLeanServer,
            LeanREPLConfig,
            LeanRequire,
            LocalProject,
            TempRequireProject,
        )

        if self._local_project:
            self._project = LocalProject(
                directory=self._local_project,
                auto_build=True,
            )
            config = LeanREPLConfig(
                project=self._project,
                verbose=False,
            )
            logger.info(
                "Lean server initialized (LocalProject=%s)",
                self._local_project,
            )
            self._server = AutoLeanServer(config)
            return

        require_list: list = []
        if self._mathlib:
            if self._mathlib_rev:
                require_list.append(
                    LeanRequire(
                        name="mathlib",
                        git="https://github.com/leanprover-community/mathlib4",
                        rev=self._mathlib_rev,
                    )
                )
            else:
                require_list.append("mathlib")
        for r in self._extra_requires:
            require_list.append(LeanRequire(name=r.name, git=r.git, rev=r.rev))

        if require_list:
            self._project = TempRequireProject(
                lean_version=self._lean_version,
                require=require_list if len(require_list) > 1 else require_list[0],
            )
            config = LeanREPLConfig(
                project=self._project,
                verbose=False,
            )
        else:
            config = LeanREPLConfig(
                lean_version=self._lean_version,
                verbose=False,
            )

        self._server = AutoLeanServer(config)
        logger.info(
            "Lean server initialized (mathlib=%s, extra=%s)",
            self._mathlib,
            [r.name for r in self._extra_requires],
        )

    async def verify(
        self,
        theorem: TheoremStatement,
        timeout: float = 60.0,
    ) -> BackendResult:
        """Verify a theorem using Lean 4."""
        start = time.monotonic()

        if not self.is_available():
            return BackendResult(
                backend=Backend.LEAN,
                status=VerificationStatus.UNAVAILABLE,
                error_message="lean-interact not installed",
            )

        code = theorem.code.get(Backend.LEAN)
        if not code:
            return BackendResult(
                backend=Backend.LEAN,
                status=VerificationStatus.NOT_ATTEMPTED,
                error_message="No Lean code provided for this theorem",
            )

        with self._lock:
            try:
                self._ensure_server()
                return self._run_verification(code, start)
            except Exception as e:
                elapsed = time.monotonic() - start
                logger.error("Lean verification failed: %s", e)
                return BackendResult(
                    backend=Backend.LEAN,
                    status=VerificationStatus.FAILED,
                    error_message=str(e),
                    elapsed_seconds=elapsed,
                )

    def _run_verification(self, code: str, start: float) -> BackendResult:
        """Execute Lean code and parse the response."""
        from lean_interact import Command

        response = self._server.run(Command(cmd=code))
        elapsed = time.monotonic() - start
        raw = str(response)

        # Parse the response. Newer lean-interact returns CommandResponse with a
        # `messages` list whose entries have `severity` ('error', 'warning', 'info').
        messages = getattr(response, "messages", []) or []
        error_msgs = [
            m for m in messages
            if getattr(m, "severity", None) == "error"
        ]

        # Fall back to legacy attributes
        legacy_errors = getattr(response, "errors", None)
        if not error_msgs and legacy_errors:
            error_msgs = legacy_errors

        has_errors_attr = getattr(response, "has_errors", None)
        if callable(has_errors_attr):
            errored = has_errors_attr()
        else:
            errored = bool(error_msgs)

        sorries = getattr(response, "sorries", [])
        sorry_count = len(sorries) if isinstance(sorries, list) else 0

        if errored:
            error_strs = []
            for m in error_msgs:
                data = getattr(m, "data", None)
                pos = getattr(m, "start_pos", None)
                if data is not None:
                    if pos is not None:
                        error_strs.append(f"line {getattr(pos, 'line', '?')}: {data}")
                    else:
                        error_strs.append(str(data))
                else:
                    error_strs.append(str(m))
            return BackendResult(
                backend=Backend.LEAN,
                status=VerificationStatus.FAILED,
                confidence=ConfidenceLevel.L0,
                raw_output=raw,
                error_message="; ".join(error_strs) if error_strs else "(unknown error)",
                elapsed_seconds=elapsed,
            )

        if sorry_count > 0:
            confidence = (
                ConfidenceLevel.L4 if sorry_count == 1 else ConfidenceLevel.L3
            )
            return BackendResult(
                backend=Backend.LEAN,
                status=VerificationStatus.PARTIAL,
                confidence=confidence,
                raw_output=raw,
                sorry_count=sorry_count,
                elapsed_seconds=elapsed,
            )

        # Success: no errors, no sorries
        return BackendResult(
            backend=Backend.LEAN,
            status=VerificationStatus.SUCCESS,
            confidence=ConfidenceLevel.L5,
            raw_output=raw,
            elapsed_seconds=elapsed,
        )

    def shutdown(self) -> None:
        """Shut down the Lean server and clean up."""
        with self._lock:
            if self._server is not None:
                try:
                    self._server.close()
                except Exception:
                    pass
                self._server = None

            if self._project is not None:
                try:
                    self._project.cleanup()
                except Exception:
                    pass
                self._project = None

        logger.info("Lean backend shut down")
