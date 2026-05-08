"""Isabelle/HOL verification backend using isabelle-client."""

from __future__ import annotations

import asyncio
import logging
import re
import shutil
import subprocess
import tempfile
import threading
import time
from pathlib import Path
from typing import Any


_THEORY_BLOCK_RE = re.compile(
    r"^\s*theory\s+\S+\s+imports\s+(?P<imports>.*?)\s+begin\s+(?P<body>.*)\s+end\s*$",
    re.DOTALL,
)
_THEORY_NAME_RE = re.compile(r"^\s*theory\s+(?P<name>\S+)\s+imports\s+", re.DOTALL)


def _split_theory(code: str) -> tuple[str, tuple[str, ...]]:
    """Extract (body, imports) from a full Isabelle theory file.

    If the code is not a complete theory, return (code, ("Main",)).
    """
    m = _THEORY_BLOCK_RE.match(code)
    if not m:
        return code.strip(), ("Main",)

    raw_imports = m.group("imports").strip()
    # Imports are space-separated; quoted strings keep their quotes.
    parts: list[str] = []
    buf: list[str] = []
    in_quote = False
    for ch in raw_imports:
        if ch == '"':
            in_quote = not in_quote
            buf.append(ch)
        elif ch.isspace() and not in_quote:
            if buf:
                parts.append("".join(buf))
                buf = []
        else:
            buf.append(ch)
    if buf:
        parts.append("".join(buf))
    imports = tuple(parts) if parts else ("Main",)
    return m.group("body").strip(), imports

from .models import (
    Backend,
    BackendResult,
    ConfidenceLevel,
    TheoremStatement,
    VerificationStatus,
)

logger = logging.getLogger(__name__)


def _start_isabelle_server(
    log_file: str | None = None,
    name: str | None = None,
    port: int | None = None,
) -> tuple[str, subprocess.Popen[str]]:
    """Start Isabelle server without asyncio subprocess transports.

    `isabelle-client`'s helper returns an `asyncio.subprocess.Process` created
    inside `asyncio.run`. Keeping that object alive after its loop closes emits
    noisy "Event loop is closed" warnings during cleanup.
    """
    args = ["isabelle", "server"]
    if log_file is not None:
        args.extend(["-L", log_file])
    if port is not None:
        args.extend(["-p", str(port)])
    if name is not None:
        args.extend(["-n", name])

    process = subprocess.Popen(
        args,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
    )
    assert process.stdout is not None
    server_info = process.stdout.readline()
    if not server_info:
        process.terminate()
        raise ValueError("No stdout while starting the Isabelle server.")
    return server_info, process


# AFP session names that we know how to start. Imports of the form
# `"Ergodic_Theory.X"` or `"Markov_Models.X"` (i.e. anything whose qualifier
# matches a key here) cause the backend to switch to the configured AFP
# session for that theorem, instead of the default HOL-Probability heap.
_AFP_NAMESPACES: frozenset[str] = frozenset(
    {
        "Ergodic_Theory",
        "Markov_Models",
        "Stochastic_Matrices",
        "Perron_Frobenius",
        "Jordan_Normal_Form",
        "Coinductive",
        "Gauss_Jordan_Elim_Fun",
    }
)


def _imports_need_afp(imports: tuple[str, ...]) -> bool:
    for imp in imports:
        stripped = imp.strip().strip('"')
        # Imports look like `Ergodic_Theory.Invariants` or just `Main`.
        head, _, _ = stripped.partition(".")
        if head in _AFP_NAMESPACES:
            return True
    return False


class IsabelleBackend:
    """Isabelle backend supporting both inline (IsabelleConnector) and session modes.

    Multiple sessions (e.g. ``HOL-Probability`` and ``HybridVerifyAFP``) can be
    held open simultaneously. Each theorem is dispatched against the session
    declared in ``theorem.metadata['isabelle_session']``; if that is unset, the
    backend infers AFP usage from the imports list and falls back to the
    default session otherwise.
    """

    def __init__(
        self,
        session: str = "HOL-Probability",
        use_connector: bool = True,
        afp_session: str | None = None,
    ):
        self._session = session
        self._afp_session = afp_session
        self._use_connector = use_connector
        self._connector: Any = None
        # session-name -> (client, session_id, server_process)
        self._sessions: dict[str, tuple[Any, str, subprocess.Popen[str]]] = {}
        self._lock = threading.Lock()

    @property
    def name(self) -> str:
        return "isabelle"

    def is_available(self) -> bool:
        """Check if isabelle-client and the Isabelle executable are installed."""
        try:
            import isabelle_client  # noqa: F401
        except ImportError:
            return False
        return shutil.which("isabelle") is not None

    def _ensure_connector(self) -> None:
        """Lazily initialize the Isabelle connector."""
        if self._connector is not None:
            return

        from isabelle_client.isabelle_connector import IsabelleConnector

        self._connector = IsabelleConnector()
        logger.info("Isabelle connector initialized (session=%s)", self._session)

    def _ensure_session(self, session_name: str) -> tuple[Any, str]:
        """Lazily start (or fetch) the Isabelle session named ``session_name``.

        Returns ``(client, session_id)``. Each distinct session gets its own
        Isabelle server process so that switching between, say,
        ``HOL-Probability`` and ``HybridVerifyAFP`` does not require tearing
        down and rebuilding heaps for each verification call.
        """
        cached = self._sessions.get(session_name)
        if cached is not None:
            client, session_id, _ = cached
            return client, session_id

        from isabelle_client import get_isabelle_client

        server_info, server_process = _start_isabelle_server()
        client = get_isabelle_client(server_info)
        client.session_build(session=session_name)
        response = client.session_start(session=session_name)
        session_id = response[-1].response_body.session_id
        self._sessions[session_name] = (client, session_id, server_process)
        logger.info(
            "Isabelle session started (session=%s, id=%s)",
            session_name,
            session_id,
        )
        return client, session_id

    def _select_session(
        self, theorem: TheoremStatement, imports: tuple[str, ...]
    ) -> str:
        """Pick the session this theorem should be verified against."""
        explicit = theorem.metadata.get("isabelle_session") if theorem.metadata else None
        if isinstance(explicit, str) and explicit:
            return explicit
        if self._afp_session and _imports_need_afp(imports):
            return self._afp_session
        return self._session

    async def verify(
        self,
        theorem: TheoremStatement,
        timeout: float = 60.0,
    ) -> BackendResult:
        """Verify a theorem using Isabelle."""
        start = time.monotonic()

        if not self.is_available():
            return BackendResult(
                backend=Backend.ISABELLE,
                status=VerificationStatus.UNAVAILABLE,
                error_message="isabelle-client not installed",
            )

        code = theorem.code.get(Backend.ISABELLE)
        if not code:
            return BackendResult(
                backend=Backend.ISABELLE,
                status=VerificationStatus.NOT_ATTEMPTED,
                error_message="No Isabelle code provided for this theorem",
            )

        # Run the synchronous verification in a worker thread because
        # `isabelle_client.start_isabelle_server` uses `asyncio.run` internally,
        # which fails when called from a running event loop.
        def _run() -> BackendResult:
            with self._lock:
                try:
                    if self._use_connector:
                        return self._verify_connector(code, start)
                    else:
                        return self._verify_session(code, theorem, start)
                except Exception as e:
                    elapsed = time.monotonic() - start
                    logger.error("Isabelle verification failed: %s", e)
                    return BackendResult(
                        backend=Backend.ISABELLE,
                        status=VerificationStatus.FAILED,
                        error_message=str(e),
                        elapsed_seconds=elapsed,
                    )

        return await asyncio.to_thread(_run)

    def _verify_connector(self, code: str, start: float) -> BackendResult:
        """Verify using IsabelleConnector (inline mode)."""
        from isabelle_client.isabelle_connector import IsabelleTheoryError

        self._ensure_connector()

        body, imports = _split_theory(code)

        try:
            self._connector.build_theory(body, imports=imports)
            elapsed = time.monotonic() - start
            raw = f"Theory built successfully (imports={imports}):\n{body}"

            # Check for sorry in the code
            sorry_count = code.lower().count("sorry")
            if sorry_count > 0:
                confidence = (
                    ConfidenceLevel.L4 if sorry_count == 1 else ConfidenceLevel.L3
                )
                return BackendResult(
                    backend=Backend.ISABELLE,
                    status=VerificationStatus.PARTIAL,
                    confidence=confidence,
                    raw_output=raw,
                    sorry_count=sorry_count,
                    elapsed_seconds=elapsed,
                )

            return BackendResult(
                backend=Backend.ISABELLE,
                status=VerificationStatus.SUCCESS,
                confidence=ConfidenceLevel.L5,
                raw_output=raw,
                elapsed_seconds=elapsed,
            )

        except IsabelleTheoryError as e:
            elapsed = time.monotonic() - start
            return BackendResult(
                backend=Backend.ISABELLE,
                status=VerificationStatus.FAILED,
                confidence=ConfidenceLevel.L0,
                raw_output=str(e),
                error_message=str(e),
                elapsed_seconds=elapsed,
            )

    def _verify_session(
        self, code: str, theorem: TheoremStatement, start: float
    ) -> BackendResult:
        """Verify using session mode (use_theories for .thy files)."""
        _, imports = _split_theory(code)
        session_name = self._select_session(theorem, imports)
        client, session_id = self._ensure_session(session_name)

        # Write theory to a temp file. Isabelle requires the file name and the
        # theory name passed to use_theories to match a complete theory header.
        m = _THEORY_NAME_RE.match(code)
        theory_name = (
            m.group("name").strip('"')
            if m
            else f"Verify_{theorem.id.replace('-', '_')}"
        )
        with tempfile.TemporaryDirectory() as tmpdir:
            thy_path = Path(tmpdir) / f"{theory_name}.thy"
            thy_path.write_text(code)

            response = client.use_theories(
                session_id=session_id,
                theories=[theory_name],
                master_dir=tmpdir,
                watchdog_timeout=0,
            )

        elapsed = time.monotonic() - start
        raw = str(response)

        # Parse structured responses for real Isabelle theory errors. The
        # serialized response contains an `errors=[]` field even on success.
        errors: list[str] = []
        for item in response:
            body = getattr(item, "response_body", None)
            for error in getattr(body, "errors", []) or []:
                errors.append(getattr(error, "message", str(error)))
            if getattr(body, "ok", True) is False:
                errors.append(str(body))
        sorry_count = raw.lower().count("sorry")

        if errors:
            return BackendResult(
                backend=Backend.ISABELLE,
                status=VerificationStatus.FAILED,
                confidence=ConfidenceLevel.L0,
                raw_output=raw,
                error_message="\n".join(errors),
                elapsed_seconds=elapsed,
            )

        if sorry_count > 0:
            confidence = (
                ConfidenceLevel.L4 if sorry_count == 1 else ConfidenceLevel.L3
            )
            return BackendResult(
                backend=Backend.ISABELLE,
                status=VerificationStatus.PARTIAL,
                confidence=confidence,
                raw_output=raw,
                sorry_count=sorry_count,
                elapsed_seconds=elapsed,
            )

        return BackendResult(
            backend=Backend.ISABELLE,
            status=VerificationStatus.SUCCESS,
            confidence=ConfidenceLevel.L5,
            raw_output=raw,
            elapsed_seconds=elapsed,
        )

    def shutdown(self) -> None:
        """Shut down the Isabelle backend (all open sessions)."""
        with self._lock:
            for session_name, (client, session_id, server_process) in list(
                self._sessions.items()
            ):
                try:
                    client.session_stop(session_id)
                except Exception:
                    pass
                try:
                    client.shutdown()
                except Exception:
                    pass
                if server_process:
                    try:
                        server_process.terminate()
                        server_process.wait(timeout=5)
                    except Exception:
                        try:
                            server_process.kill()
                        except Exception:
                            pass
                logger.debug("Isabelle session shut down (session=%s)", session_name)
            self._sessions.clear()
            self._connector = None

        logger.info("Isabelle backend shut down")
