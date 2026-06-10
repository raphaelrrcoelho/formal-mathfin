# Documentation

| File | One-line | When to read |
|---|---|---|
| [`blueprint.md`](blueprint.md) | The deductive spine — a dependency graph from Brownian motion to Black–Scholes, each node linked to its Lean proof. | **First**, to see the BM → Black-Scholes deductive arc and what's proved vs gated. |
| [`coverage.md`](coverage.md) | Per-theorem audit with faithfulness status and verification evidence. | Before claiming any specific theorem is "proved." Source of truth for what's `full` vs `library_wrapper` vs `reduced_core`. |
| [`architecture.md`](architecture.md) | Design principles: the seven structural-principle modules, the three-tier honesty model, the bridge methodology. | When deciding where a new theorem belongs, or to understand why the library is shaped the way it is. |
| [`leaps.md`](leaps.md) | The 2026-05-23 "leaps": static Girsanov (the risk-neutral measure *derived*, `BSCallHyp` made a theorem), the genesis cascade (physical→EMM→pricing spine), and Margrabe's multivariate exchange option. Includes the honest abstraction boundary and what stays gated. | To understand how the EMM stops being an axiom, and how the multivariate / change-of-measure results compose. |
| [`bridges.md`](bridges.md) | Catalogue of bridges from `Foundations/` to pricing modules — the additive constructors that connect BM/martingale infra to BS/Bachelier/binomial. | When extending Foundations and wanting to make it usable from a pricing module without breaking existing consumers. |
| [`patterns.md`](patterns.md) | Distilled Lean / Mathlib proof patterns + technical idioms + workflow notes + anti-patterns. | Before writing a non-trivial proof, especially if it touches gaussian / martingale / convexity / Lp machinery. |
| [`roadmap.md`](roadmap.md) | Strategic depth-vs-breadth framing + tactical phase log of completed milestones. | When picking the next theorem to formalise, or to understand the historical trajectory. |
| [`upstreaming.md`](upstreaming.md) | Log + playbook for contributing MathFin results upstream to brownian-motion / Mathlib (live: issue #440 → PR #446). | When submitting a `Foundations/` result upstream, or checking a contribution's status. |
| [`values-review.md`](values-review.md) | The eight judgment lenses and the per-round verdict log — the review panel that closes every proof-content session. | To see the quality bar and what each round found, fixed, and deferred. |

## Cross-references

- For the storefront pitch and the at-a-glance tables, see [`../README.md`](../README.md).
- For the contributor workflow (how to add a theorem, run the build, open a PR), see [`../CONTRIBUTING.md`](../CONTRIBUTING.md).
- For upstream-PR drafts targeting Mathlib / BrownianMotion, see [`../upstream/`](../upstream/).

## Provenance

The four core docs (`coverage.md`, `bridges.md`, `patterns.md`,
`roadmap.md`) were promoted from root-level `FORMALIZATION_STATUS.md`,
`BRIDGE_AUDIT.md`, `LEARNINGS.md`, and a merge of `MATH_DEPTH_ROADMAP.md` +
`QUANTFIN_ROADMAP.md` during the 2026-05-23 reorganization.
