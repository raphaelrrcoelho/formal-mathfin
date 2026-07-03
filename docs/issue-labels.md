# Issue label taxonomy

This taxonomy gives maintainers and contributors a shared vocabulary for
triaging work. Labels should answer four questions:

- **What part of the project is affected?** Use one `area:*` label.
- **What kind of work is it?** Use one `type:*` label.
- **How hard is it for a contributor?** Use one `difficulty:*` label.
- **What is the current state?** Use one `status:*` label.

Use `good first issue` and `help wanted` as public entry-point labels on top of
the taxonomy when the task is ready for outside contributors.

Colors are consistent per dimension so an issue's labels read at a glance:
`area:*` share one hue, `type:*` another, while `difficulty:*` and `status:*`
use a semantic scale (green → amber → red).

## Area labels

The mathematical areas mirror the `MathFin/` subdirectories, so a contributor
can filter to the part of the library they know; the last three are
cross-cutting.

| Label | Use for |
|---|---|
| `area:foundations` | `MathFin/Foundations/` — Itô calculus, Brownian motion, stochastic integration, martingales, Poisson, Markov, and SDEs. |
| `area:black-scholes` | `MathFin/BlackScholes/` — the Black-Scholes model, greeks, and the pricing PDE. |
| `area:futures` | `MathFin/Futures/` — Black-76 futures options, caplets, and swaptions. |
| `area:binomial` | `MathFin/Binomial/` — CRR binomial trees and convergence to Black-Scholes. |
| `area:fixed-income` | `MathFin/FixedIncome/` — bonds, term structure, and interest-rate models. |
| `area:portfolio` | `MathFin/Portfolio/` — portfolio choice, Kelly, and Merton problems. |
| `area:performance` | `MathFin/Performance/` — Sharpe ratio and other performance measures. |
| `area:risk` | `MathFin/RiskMeasures/` — VaR, CVaR, and coherent risk measures. |
| `area:actuarial` | `MathFin/Actuarial/` — actuarial and insurance pricing. |
| `area:defi` | `MathFin/DeFi/` — decentralized-finance models. |
| `area:tooling` | Python verification tools, scripts, ledger logic, and generated audits under `tools/` and `scripts/`. |
| `area:docs` | Markdown docs, README content, onboarding, coverage/blueprint prose, and cross-links. |
| `area:ci` | GitHub Actions, Docker images, build gates, and release automation. |

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
| Repair a stale coverage row after a theorem rename | `area:docs`, `type:docs`, `difficulty:small`, `status:ready` |
| Prove a new Black-Scholes Greek | `area:black-scholes`, `type:proof`, `difficulty:medium`, `status:ready` |
| Generalize an Itô-formula hypothesis | `area:foundations`, `type:proof`, `difficulty:hard`, `status:ready` |
| Draft an upstream BrownianMotion issue | `area:foundations`, `type:research`, `difficulty:hard`, `status:blocked-upstream` |
| Fix a failing build workflow | `area:ci`, `type:bug`, `difficulty:medium`, `status:ready` |

## Bootstrap commands

Maintainers can create the taxonomy with `gh label create`:

```bash
# area:* — one shared blue
gh label create "area:foundations"  --color "1d76db" --description "Foundations/ — Itô, Brownian motion, stochastic integration, martingales, Poisson, Markov, SDEs"
gh label create "area:black-scholes" --color "1d76db" --description "BlackScholes/ — the Black-Scholes model, greeks, and the pricing PDE"
gh label create "area:futures"      --color "1d76db" --description "Futures/ — Black-76 futures options, caplets, and swaptions"
gh label create "area:binomial"     --color "1d76db" --description "Binomial/ — CRR binomial trees and convergence to Black-Scholes"
gh label create "area:fixed-income" --color "1d76db" --description "FixedIncome/ — bonds, term structure, and interest-rate models"
gh label create "area:portfolio"    --color "1d76db" --description "Portfolio/ — portfolio choice, Kelly, and Merton problems"
gh label create "area:performance"  --color "1d76db" --description "Performance/ — Sharpe ratio and other performance measures"
gh label create "area:risk"         --color "1d76db" --description "RiskMeasures/ — VaR, CVaR, and coherent risk measures"
gh label create "area:actuarial"    --color "1d76db" --description "Actuarial/ — actuarial and insurance pricing"
gh label create "area:defi"         --color "1d76db" --description "DeFi/ — decentralized-finance models"
gh label create "area:tooling"      --color "1d76db" --description "Verification tools, scripts, ledger logic, and generated audits"
gh label create "area:docs"         --color "1d76db" --description "Markdown docs, onboarding, coverage/blueprint prose, and cross-links"
gh label create "area:ci"           --color "1d76db" --description "GitHub Actions, Docker images, build gates, and release automation"

# type:* — one shared purple
gh label create "type:bug"         --color "5319e7" --description "Something expected to work is broken"
gh label create "type:proof"       --color "5319e7" --description "Lean theorem, proof repair, or theorem generalization"
gh label create "type:docs"        --color "5319e7" --description "Documentation-only work"
gh label create "type:refactor"    --color "5319e7" --description "Structure or naming change that should preserve behavior"
gh label create "type:tooling"     --color "5319e7" --description "Verification scripts, exports, or developer tooling"
gh label create "type:research"    --color "5319e7" --description "Open investigation where the path is not yet clear"
gh label create "type:maintenance" --color "5319e7" --description "Routine cleanup, dependency updates, or housekeeping"

# difficulty:* — green → red scale
gh label create "difficulty:good-first" --color "0e8a16" --description "Small, well-scoped task for new contributors"
gh label create "difficulty:small"      --color "c2e0c6" --description "Straightforward change for someone familiar with the repo"
gh label create "difficulty:medium"     --color "fbca04" --description "Requires repo context, Lean fluency, or careful validation"
gh label create "difficulty:hard"       --color "d93f0b" --description "Requires deep domain knowledge or upstream coordination"

# status:* — grey (new) → green (go) → amber (active) → red (blocked) → blue (review)
gh label create "status:needs-triage"     --color "ededed" --description "New issue that has not been classified yet"
gh label create "status:needs-info"       --color "fef2c0" --description "Waiting on clarification before work should start"
gh label create "status:ready"            --color "0e8a16" --description "Scoped enough for a contributor to pick up"
gh label create "status:in-progress"      --color "fbca04" --description "Someone is actively working on it"
gh label create "status:blocked-upstream" --color "b60205" --description "Blocked on Mathlib, BrownianMotion, or another external project"
gh label create "status:blocked-design"   --color "e99695" --description "Blocked on a modeling, theorem-shape, or architecture decision"
gh label create "status:review"           --color "c5def5" --description "PR exists and maintainer review is the next step"
```
