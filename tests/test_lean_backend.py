"""Unit tests for the daemon's Lean elaboration wrapper (`LeanBackend.run_raw`).

These use a FAKE lean-interact server — no Lean process is booted — so they run
on the host with zero memory cost (the memory doctrine is about live Lean envs).
`run_raw` imports `Command` from lean_interact, so the module must be importable;
skip cleanly if it is not (e.g. a CI pytest job without the extra installed).
"""

import pytest

pytest.importorskip("lean_interact")  # run_raw does `from lean_interact import Command`

from tools.verify.lean_backend import LeanBackend, _ELAB_TIMEOUT_S


class _FakeServer:
    """Records the kwargs each `.run` call receives; behaviour is injected."""

    def __init__(self, behavior):
        self._behavior = behavior
        self.calls: list[dict] = []

    def run(self, request, *, timeout=None, **kw):
        self.calls.append({"timeout": timeout})
        return self._behavior(request, timeout)


def _backend_with(server) -> LeanBackend:
    # bypass __init__ (which would want a real project) — run_raw needs only
    # `_server` set; `_ensure_server` early-returns when it is not None.
    b = LeanBackend.__new__(LeanBackend)
    b._server = server
    return b


def test_run_raw_bounds_each_elaboration_with_a_finite_timeout():
    # the root cause of the daemon wedging forever: run() was called with no
    # timeout (lean-interact's DEFAULT_TIMEOUT is None → the socket read blocks
    # indefinitely on a spinning tactic). run_raw MUST pass a finite timeout.
    srv = _FakeServer(lambda req, timeout: "RESPONSE")
    out = _backend_with(srv).run_raw("import Mathlib\n#check 1")
    assert out == "RESPONSE"
    assert srv.calls[0]["timeout"] == _ELAB_TIMEOUT_S
    assert _ELAB_TIMEOUT_S is not None and _ELAB_TIMEOUT_S > 0


def test_run_raw_timeout_surfaces_cleanly_and_does_not_retry():
    # a spinning elaboration: lean-interact kills the REPL and raises TimeoutError.
    # run_raw must NOT retry (re-running the same code just spins again) and must
    # surface a clear failure the daemon can return to the client.
    def spin(req, timeout):
        raise TimeoutError(
            f"The Lean server did not respond in time (timeout={timeout}) and is now killed.")

    srv = _FakeServer(spin)
    with pytest.raises(RuntimeError, match="timed out"):
        _backend_with(srv).run_raw("theorem x : False := by nlinarith")
    assert len(srv.calls) == 1  # exactly one attempt — no retry-spin
