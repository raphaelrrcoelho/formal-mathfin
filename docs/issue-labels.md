# Issue label taxonomy

This taxonomy gives maintainers and contributors a shared vocabulary for
triaging work. Labels should answer four questions:

- **What part of the project is affected?** Use one `area:*` label.
- **What kind of work is it?** Use one `type:*` label.
- **How hard is it for a contributor?** Use one `difficulty:*` label.
- **What is the current state?** Use one `status:*` label.

Use `good first issue` and `help wanted` as public entry-point labels on top of
the taxonomy when the task is ready for outside contributors.

## Area labels

| Label | Use for |
|---|---|
| `area:lean` | Lean theorem files under `MathFin/` and proof architecture. |
| `area:docs` | Markdown docs, README content, onboarding, troubleshooting, and cross-links. |
| `area:coverage` | `docs/coverage.md`, theorem status wording, and faithfulness evidence. |
| `area:blueprint` | `docs/blueprint.md`, blueprint exports, and dependency graph documentation. |
| `area:tooling` | Python verification tools, scripts, ledger logic, and generated audits. |
| `area:ci` | GitHub Actions, Docker images, build gates, and release automation. |
| `area:upstream` | Mathlib, BrownianMotion, Zulip, or other upstream coordination. |

## Type labels

| Label | Use for |
|---|---|
| `type:bug` | Something expected to work is broken. |
| `type:proof` | A new Lean theorem, proof repair, or theorem generalization. |
| `type:docs` | Documentation-only work. |
| `type:refactor` | Structure or naming changes that should preserve behavior and theorem statements. |
| `type:tooling` | Changes to verification scripts, exports, or developer tooling. |
| `type:research` | Open investigation where the implementation path is not yet clear. |
| `type:maintenance` | Routine cleanup, dependency updates, or housekeeping. |

## Difficulty labels

| Label | Use for |
|---|---|
| `difficulty:good-first` | Small, well-scoped task with enough context in the issue body. Add `good first issue` too. |
| `difficulty:small` | Straightforward change for someone familiar with the repo. |
| `difficulty:medium` | Requires repo context, Lean fluency, or careful validation. |
| `difficulty:hard` | Requires deep domain knowledge, theorem design, or upstream coordination. |

## Status labels

| Label | Use for |
|---|---|
| `status:needs-triage` | New issue that has not been classified yet. |
| `status:needs-info` | Waiting on clarification before work should start. |
| `status:ready` | Scoped enough for a contributor to pick up. |
| `status:in-progress` | Someone is actively working on it. |
| `status:blocked-upstream` | Blocked on Mathlib, BrownianMotion, or another external project. |
| `status:blocked-design` | Blocked on a modeling, theorem-shape, or architecture decision. |
| `status:review` | PR exists and maintainer review is the next step. |

## Triage examples

| Issue | Suggested labels |
|---|---|
| Add a glossary entry for no-arbitrage terms | `area:docs`, `type:docs`, `difficulty:good-first`, `status:ready`, `good first issue` |
| Repair a stale coverage row after a theorem rename | `area:coverage`, `type:docs`, `difficulty:small`, `status:ready` |
| Prove a new Black-Scholes Greek | `area:lean`, `type:proof`, `difficulty:medium`, `status:ready` |
| Draft an upstream BrownianMotion issue | `area:upstream`, `type:research`, `difficulty:hard`, `status:blocked-design` |
| Fix a failing build workflow | `area:ci`, `type:bug`, `difficulty:medium`, `status:ready` |

## Bootstrap commands

Maintainers can create the taxonomy with `gh label create`:

```bash
gh label create "area:lean" --color "0e8a16" --description "Lean theorem files and proof architecture"
gh label create "area:docs" --color "0075ca" --description "Markdown docs, onboarding, troubleshooting, and cross-links"
gh label create "area:coverage" --color "5319e7" --description "Coverage table, faithfulness status, and verification evidence"
gh label create "area:blueprint" --color "1d76db" --description "Blueprint graph, exports, and dependency documentation"
gh label create "area:tooling" --color "fbca04" --description "Python verification tools, scripts, ledger logic, and generated audits"
gh label create "area:ci" --color "d4c5f9" --description "GitHub Actions, Docker images, build gates, and release automation"
gh label create "area:upstream" --color "bfd4f2" --description "Mathlib, BrownianMotion, Zulip, or other upstream coordination"

gh label create "type:bug" --color "d73a4a" --description "Something expected to work is broken"
gh label create "type:proof" --color "5319e7" --description "Lean theorem, proof repair, or theorem generalization"
gh label create "type:docs" --color "0075ca" --description "Documentation-only work"
gh label create "type:refactor" --color "c2e0c6" --description "Structure or naming change that should preserve behavior"
gh label create "type:tooling" --color "fbca04" --description "Verification scripts, exports, or developer tooling"
gh label create "type:research" --color "b60205" --description "Open investigation where the path is not yet clear"
gh label create "type:maintenance" --color "fef2c0" --description "Routine cleanup, dependency updates, or housekeeping"

gh label create "difficulty:good-first" --color "7057ff" --description "Small, well-scoped task for new contributors"
gh label create "difficulty:small" --color "c5def5" --description "Straightforward change for someone familiar with the repo"
gh label create "difficulty:medium" --color "fbca04" --description "Requires repo context, Lean fluency, or careful validation"
gh label create "difficulty:hard" --color "b60205" --description "Requires deep domain knowledge or upstream coordination"

gh label create "status:needs-triage" --color "ededed" --description "New issue that has not been classified yet"
gh label create "status:needs-info" --color "d876e3" --description "Waiting on clarification before work should start"
gh label create "status:ready" --color "0e8a16" --description "Scoped enough for a contributor to pick up"
gh label create "status:in-progress" --color "fbca04" --description "Someone is actively working on it"
gh label create "status:blocked-upstream" --color "b60205" --description "Blocked on Mathlib, BrownianMotion, or another external project"
gh label create "status:blocked-design" --color "d93f0b" --description "Blocked on a modeling, theorem-shape, or architecture decision"
gh label create "status:review" --color "1d76db" --description "PR exists and maintainer review is the next step"
```
