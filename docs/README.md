# Documentation

| File | One-line | When to read |
|---|---|---|
| [`coverage.md`](coverage.md) | Per-theorem audit with faithfulness status and verification evidence. | Before claiming any specific theorem is "proved." Source of truth for what's `full` vs `library_wrapper` vs `reduced_core`. |
| [`architecture.md`](architecture.md) | Design principles: the seven structural-principle modules, the three-tier honesty model, the bridge methodology. | When deciding where a new theorem belongs, or to understand why the library is shaped the way it is. |
| [`leaps.md`](leaps.md) | The 2026-05-23 "leaps": static Girsanov (the risk-neutral measure *derived*, `BSCallHyp` made a theorem), the genesis cascade (physical→EMM→pricing spine), and Margrabe's multivariate exchange option. Includes the honest abstraction boundary and what stays gated. | To understand how the EMM stops being an axiom, and how the multivariate / change-of-measure results compose. |
| [`bridges.md`](bridges.md) | Catalogue of bridges from `Foundations/` to pricing modules — the additive constructors that connect BM/martingale infra to BS/Bachelier/binomial. | When extending Foundations and wanting to make it usable from a pricing module without breaking existing consumers. |
| [`patterns.md`](patterns.md) | Distilled Lean / Mathlib proof patterns + technical idioms + workflow notes + anti-patterns. | Before writing a non-trivial proof, especially if it touches gaussian / martingale / convexity / Lp machinery. |
| [`roadmap.md`](roadmap.md) | Strategic depth-vs-breadth framing + tactical phase log of completed milestones. | When picking the next theorem to formalise, or to understand the historical trajectory. |
| [`superpowers/specs/`](superpowers/specs/) | Design specs for major changes (e.g. the 2026-05-23 reorganization). | Historical context for why the repo is structured this way. |

## Cross-references

- For the storefront pitch and the at-a-glance tables, see [`../README.md`](../README.md).
- For the contributor workflow (how to add a theorem, run the build, open a PR), see [`../CONTRIBUTING.md`](../CONTRIBUTING.md).
- For upstream-PR drafts targeting Mathlib / BrownianMotion, see [`../upstream/`](../upstream/).

## Provenance

The four core docs (`coverage.md`, `bridges.md`, `patterns.md`,
`roadmap.md`) were promoted from root-level `FORMALIZATION_STATUS.md`,
`BRIDGE_AUDIT.md`, `LEARNINGS.md`, and a merge of `MATH_DEPTH_ROADMAP.md` +
`QUANTFIN_ROADMAP.md` during the 2026-05-23 reorganization. See
[`superpowers/specs/2026-05-23-repo-reorganization-design.md`](superpowers/specs/2026-05-23-repo-reorganization-design.md)
for the structural rationale.
