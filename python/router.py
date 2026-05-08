"""Domain-based routing to verification backends."""

from __future__ import annotations

from dataclasses import dataclass

from .models import Backend, Domain

# Default routing table: domain → ordered list of backends to try.
# Based on current formalization coverage:
# - Lean+Isabelle: Markov chains and ergodic-theory reduced cores where present
# - Isabelle: CLT (AFP/HOL-Probability libraries)
# - Lean: Martingales, stopping times, Brownian motion (Mathlib)
# - Both: Measure theory, Poisson processes
DEFAULT_ROUTING: dict[Domain, list[Backend]] = {
    # Markov chains: Mathlib has Kernel.IsMarkovKernel; AFP/HOL-Probability has full
    # Markov_Models. Try Lean first (faster + works on smaller heaps), then Isabelle.
    Domain.MARKOV_CHAINS:       [Backend.LEAN, Backend.ISABELLE],
    Domain.ERGODIC_THEORY:      [Backend.ISABELLE, Backend.LEAN],
    Domain.CLT:                 [Backend.ISABELLE],
    Domain.MARTINGALES:         [Backend.LEAN],
    Domain.STOPPING_TIMES:      [Backend.LEAN],
    Domain.BROWNIAN_MOTION:     [Backend.LEAN],
    Domain.MEASURE_THEORY:      [Backend.LEAN, Backend.ISABELLE],
    # Stochastic calculus / SDEs / finance: Mathlib still lacks the full Brownian
    # motion / Itô integral / Black-Scholes development, but many benchmark
    # entries contain a formally checkable algebraic or analytic core. Try Lean
    # first when such code is present, then Isabelle where code exists.
    Domain.STOCHASTIC_CALCULUS: [Backend.LEAN, Backend.ISABELLE],
    Domain.SDES:                [Backend.LEAN, Backend.ISABELLE],
    Domain.MATHEMATICAL_FINANCE:[Backend.LEAN, Backend.ISABELLE],
    # Poisson process: Mathlib's `poissonMeasure`/`poissonPMF` formalization (no full process yet).
    Domain.POISSON_PROCESSES:   [Backend.LEAN, Backend.ISABELLE],
}

# Domains where parallel dispatch to multiple formal provers is useful
PARALLEL_DOMAINS: set[Domain] = {
    Domain.MEASURE_THEORY,
    Domain.POISSON_PROCESSES,
}


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
        backends = self._routing.get(domain, [Backend.LEAN, Backend.ISABELLE])
        parallel = domain in self._parallel_domains and len(backends) > 1
        return RoutingDecision(backends=backends, parallel=parallel)

    def override(self, domain: Domain, backends: list[Backend]) -> None:
        """Override routing for a specific domain."""
        self._routing[domain] = backends
