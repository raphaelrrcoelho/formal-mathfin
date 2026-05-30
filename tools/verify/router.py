"""Domain-based routing to verification backends.

Lean is the sole verification backend; every domain routes to it. The
routing layer (table + parallel flag) is retained from the multi-backend
era but now degenerates to single-backend dispatch.
"""

from __future__ import annotations

from dataclasses import dataclass

from .models import Backend, Domain

DEFAULT_ROUTING: dict[Domain, list[Backend]] = {
    Domain.MARKOV_CHAINS:        [Backend.LEAN],
    Domain.ERGODIC_THEORY:       [Backend.LEAN],
    Domain.CLT:                  [Backend.LEAN],
    Domain.MARTINGALES:          [Backend.LEAN],
    Domain.STOPPING_TIMES:       [Backend.LEAN],
    Domain.BROWNIAN_MOTION:      [Backend.LEAN],
    Domain.MEASURE_THEORY:       [Backend.LEAN],
    Domain.STOCHASTIC_CALCULUS:  [Backend.LEAN],
    Domain.SDES:                 [Backend.LEAN],
    Domain.MATHEMATICAL_FINANCE: [Backend.LEAN],
    Domain.POISSON_PROCESSES:    [Backend.LEAN],
}

# Parallel dispatch is a no-op with a single backend; retained so the
# RoutingDecision shape stays stable for callers.
PARALLEL_DOMAINS: set[Domain] = set()


@dataclass
class RoutingDecision:
    """Result of routing a theorem to backends."""
    backends: list[Backend]
    parallel: bool = False

    @property
    def primary(self) -> Backend:
        """The first (preferred) backend."""
        return self.backends[0]


class Router:
    """Routes theorems to appropriate verification backends."""

    def __init__(
        self,
        routing_table: dict[Domain, list[Backend]] | None = None,
        parallel_domains: set[Domain] | None = None,
    ):
        self._routing = routing_table or DEFAULT_ROUTING
        self._parallel_domains = parallel_domains or PARALLEL_DOMAINS

    def route(self, domain: Domain) -> RoutingDecision:
        """Determine which backends to use for a given domain."""
        backends = self._routing.get(domain, [Backend.LEAN])
        parallel = domain in self._parallel_domains and len(backends) > 1
        return RoutingDecision(backends=backends, parallel=parallel)

    def override(self, domain: Domain, backends: list[Backend]) -> None:
        """Override routing for a specific domain."""
        self._routing[domain] = backends
