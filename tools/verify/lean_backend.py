"""Lean 4 verification backend using lean-interact."""

from __future__ import annotations

import logging
import os
import shutil
import threading
import time
from pathlib import Path
from typing import Any

from .models import (
    Backend,
    BackendResult,
    ConfidenceLevel,
    TheoremStatement,
    VerificationStatus,
)

logger = logging.getLogger(__name__)


# Substrings that mark a *dead REPL process* (as opposed to a normal Lean
# elaboration error, which comes back as a response, not an exception). When
# `lean-interact`'s underlying REPL subprocess dies — OOM kill, internal Lean
# crash, slow memory accumulation over a long-lived daemon session — `run()`
# raises rather than returning, and the server handle is then permanently
# unusable until respawned.
_SERVER_DEATH_MARKERS = (
    "closed unexpectedly",
    "server closed",
    "connection abort",
    "broken pipe",
    "not enough memory",
)


def _looks_like_server_death(exc: Exception) -> bool:
    """Heuristic: did this exception come from the REPL subprocess dying
    (so a restart can recover), rather than from the Lean code itself?"""
    if isinstance(
        exc,
        (ConnectionAbortedError, ConnectionResetError, ConnectionError,
         BrokenPipeError, EOFError),
    ):
        return True
    msg = str(exc).lower()
    return any(marker in msg for marker in _SERVER_DEATH_MARKERS)


# Upstream Lean REPL — tags every toolchain (v4.31.0, v4.30.0, …).
_DEFAULT_REPL_GIT = "https://github.com/leanprover-community/repl"


def _resolve_repl_source(project_dir: str) -> tuple[str | None, str | None]:
    """Pick ``(repl_git, repl_rev)`` for lean-interact's REPL.

    lean-interact's bundled default (``augustepoiroux/repl`` @ ``v1.3.17``) only
    has toolchain-tagged builds through ~v4.26, so on a v4.31 project it silently
    falls back to an older toolchain and the REPL cannot load the project's
    oleans (version mismatch) — the "daemon unfixable on v4.31" symptom. Upstream
    ``leanprover-community/repl`` tags each toolchain, so we point at it and pick
    the tag matching the project's ``lean-toolchain``. lean-interact then tries
    ``{rev}_lean-toolchain-{ver}`` and falls back to ``{rev}`` (the bare tag,
    which exists upstream). Override either with ``MATHFIN_REPL_GIT`` /
    ``MATHFIN_REPL_REV``.

    Returns ``(None, None)`` — meaning "use lean-interact's own defaults" — only
    when the toolchain file is unreadable and no env override is set.
    """
    repl_git = os.environ.get("MATHFIN_REPL_GIT", _DEFAULT_REPL_GIT)
    repl_rev = os.environ.get("MATHFIN_REPL_REV")
    if repl_rev is None:
        try:
            toolchain = Path(project_dir, "lean-toolchain").read_text().strip()
        except OSError:
            return None, None
        # e.g. "leanprover/lean4:v4.31.0" -> "v4.31.0"
        repl_rev = toolchain.split(":", 1)[1].strip() if ":" in toolchain else toolchain
    return repl_git, repl_rev


class LeanBackend:
    """Lean 4 backend driving lean-interact's AutoLeanServer against the
    in-repo Lake project (repo root by default).

    All authoritative project state lives in the Lake project: ``lakefile.lean``
    declares the dependency set, ``lake-manifest.json`` freezes transitive
    revisions, ``lean-toolchain`` pins the Lean version, and
    ``MathFin/*.lean`` holds the proof library. Benchmark snippets only
    typecheck against the prebuilt library, so complex derivations live as
    real Lean files (full ``lake build`` memory budget + incremental
    compilation + LSP authoring) and benchmarks just import + reference them
    by name.
    """

    def __init__(
        self,
        local_project: str = ".",
        *,
        memory_hard_limit_mb: int | None = None,
        max_total_memory: float = 0.8,
        max_process_memory: float | None = 0.8,
    ):
        """
        Args:
            local_project: Lake project directory.
            memory_hard_limit_mb: OS-enforced hard cap on the Lean process's
                resident memory. ``None`` (default) = no cap. Long-lived
                daemons should set this (e.g. ``8000``) so heavy proofs
                cannot OOM the host.
            max_total_memory: Soft cap on *system-wide* memory before the
                Lean server auto-restarts (proportion in [0,1]). Default
                0.8. Daemons should raise to ~0.9 to avoid mid-work restarts.
            max_process_memory: Soft cap on the Lean process memory (as a
                fraction of ``memory_hard_limit_mb``) before auto-restart.
                ``None`` disables. Daemons doing long sessions should set
                this to ``None`` so a slow leak doesn't kill the session.
        """
        self._local_project = local_project
        self._server: Any = None
        self._project: Any = None
        self._config: Any = None
        self._lock = threading.Lock()
        self._memory_hard_limit_mb = memory_hard_limit_mb
        self._max_total_memory = max_total_memory
        self._max_process_memory = max_process_memory

    @property
    def name(self) -> str:
        return "lean"

    def is_available(self) -> bool:
        try:
            import lean_interact  # noqa: F401
        except ImportError:
            return False
        return shutil.which("lake") is not None

    def _ensure_server(self, auto_build: bool = True) -> None:
        if self._server is not None:
            return

        from lean_interact import (
            AutoLeanServer,
            LeanREPLConfig,
            LocalProject,
        )

        self._project = LocalProject(
            directory=self._local_project,
            auto_build=auto_build,
        )
        repl_git, repl_rev = _resolve_repl_source(self._local_project)
        config_kwargs: dict[str, Any] = dict(
            project=self._project,
            verbose=False,
            memory_hard_limit_mb=self._memory_hard_limit_mb,
            # `enable_incremental_optimization` and `enable_parallel_elaboration`
            # are True by default — keep them; both help per-request latency
            # at modest memory cost.
        )
        if repl_rev is not None:
            # Override lean-interact's fork default with a toolchain-matched
            # upstream REPL so the daemon works on v4.31+ (see
            # `_resolve_repl_source`).
            config_kwargs["repl_git"] = repl_git
            config_kwargs["repl_rev"] = repl_rev
            logger.info("REPL source: %s @ %s (toolchain-matched)", repl_git, repl_rev)
        self._config = LeanREPLConfig(**config_kwargs)
        self._server = AutoLeanServer(
            self._config,
            max_total_memory=self._max_total_memory,
            max_process_memory=self._max_process_memory,
        )
        logger.info(
            "Lean server initialized (LocalProject=%s, hard_cap=%sMB, "
            "soft_total=%.2f, soft_proc=%s)",
            self._local_project,
            self._memory_hard_limit_mb,
            self._max_total_memory,
            self._max_process_memory,
        )

    def _restart_server(self) -> None:
        """Respawn a fresh REPL process against the **already-built** project.

        Reuses ``self._config`` (which holds the built ``LocalProject``), so this
        does NOT re-run ``lake build`` — it just starts a new REPL subprocess and
        reloads the prebuilt oleans (~30-60s warm), not the multi-minute cold
        build. Used to recover from a dead REPL mid-session. Caller must hold
        ``self._lock``.
        """
        if self._server is not None:
            try:
                self._server.close()
            except Exception:
                pass
            self._server = None
        if self._config is None:
            # Never successfully initialized — fall back to the full init path.
            self._ensure_server()
            return
        from lean_interact import AutoLeanServer

        self._server = AutoLeanServer(
            self._config,
            max_total_memory=self._max_total_memory,
            max_process_memory=self._max_process_memory,
        )
        logger.warning("Lean server respawned (fresh REPL against prebuilt project)")

    def run_raw(self, code: str, *, attempts: int = 2) -> Any:
        """Run one Lean command with **self-healing**.

        If the REPL subprocess dies (OOM / crash / accumulation over a long
        daemon session → ``run()`` raises, server handle then unusable), respawn
        a fresh REPL and retry — so a single heavy file cannot brick the daemon
        for the rest of the session. A genuine Lean *elaboration* error is
        returned as a response (not an exception) and is never retried.

        On exhausting retries the exception is re-raised, but the server is left
        freshly respawned so subsequent (different) requests still work. Caller
        must hold ``self._lock``.
        """
        from lean_interact import Command

        self._ensure_server()
        last_exc: Exception | None = None
        for attempt in range(attempts):
            try:
                return self._server.run(Command(cmd=code))
            except Exception as e:  # noqa: BLE001 — classify, then recover or re-raise
                last_exc = e
                if not _looks_like_server_death(e):
                    raise
                logger.warning(
                    "Lean REPL died (attempt %d/%d): %s — respawning",
                    attempt + 1, attempts, e,
                )
                self._restart_server()
        assert last_exc is not None
        raise last_exc

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
        response = self.run_raw(code)
        elapsed = time.monotonic() - start
        raw = str(response)

        messages = getattr(response, "messages", []) or []
        error_msgs = [
            m for m in messages
            if getattr(m, "severity", None) == "error"
        ]

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

            self._config = None

        logger.info("Lean backend shut down")
