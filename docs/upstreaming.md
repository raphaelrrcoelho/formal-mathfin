# Upstreaming to `brownian-motion`

**Date:** 2026-05-27
**Scope:** How MathFin Lean results get contributed back to
[`RemyDegenne/brownian-motion`](https://github.com/RemyDegenne/brownian-motion)
(and Mathlib): the live submission status, the per-contribution record, and the
reusable workflow.

## Executive summary

Some `MathFin/Foundations/` results are general-interest probability /
stochastic-process lemmas that belong *upstream*, not in a mathematical-finance library.
Draft files targeting other repos' module trees live under `upstream/` (our `lake`
never builds them; catalogue in `upstream/README.md`). This doc logs what has been
*submitted* as a PR and how to do it again.

As of 2026-05-27 the first full submission is **PR #446** (issue #440, stochastic
intervals): CI-green, claimed, ready for review.

## Submitted contributions

| target | contribution | PR | status |
|---|---|---|---|
| brownian-motion | stochastic intervals; `]]σ,τ]]` predictable + an elementary predictable set (issue #440) | [#446](https://github.com/RemyDegenne/brownian-motion/pull/446) | ready for review — CI green, claimed (2026-05-27) |

Staged but not yet submitted (drafts only, under `upstream/`): `brownian-motion/Martingale.lean`,
`mathlib/RealTail.lean`.

## Record: #440 — stochastic intervals (PR #446)

**What it is.** `namespace ProbabilityTheory`, `BrownianMotion/StochasticIntegral/StochasticInterval.lean`
+ its import line. Five interval defs over a general `[Preorder ι]` (`stochasticIcc/Ico/Ioc/Ioo`,
`stochasticGraph`) and, on `ℕ`: `stochasticIoc.measurableSet_predictable` (any stopping times)
and `stochasticIoc.exists_elementaryPredictableSet` (bounded `τ`). The math lives in our repo at
`MathFin/Foundations/StochasticInterval.lean` (dc17e84); the ported draft at
`upstream/brownian-motion/StochasticInterval.lean` (283b8ce).

**Porting deltas (our repo → upstream).** `namespace MathFin` → `ProbabilityTheory`;
`import Mathlib` → specific `public import Mathlib.Probability.Process.Stopping`; def typeclass
`[PartialOrder ι]` → `[Preorder ι]` (minimal; `stochasticGraph_eq` split into its own
`[PartialOrder ι]` section to avoid an instance diamond); `fun =>` → `fun ↦`. Validated green
against our pin via the lean-repl daemon (overwrite onto a `MathFin` module path →
`scripts/lean-check.sh` → `git checkout` to restore; the daemon only fast-checks files it
recognises as modules).

**The audit bar.** Degenne's review is pass-or-fail on style/math/slop. Checked against merged
files (`SimpleProcess.lean`, `Predictable.lean`): module system, specific `public import`s,
`ProbabilityTheory` namespace, `variable` block shape, `private` helpers, `fun ↦`, ≤100 cols,
the `measurableSet_predictable_*` naming family + `rw [set identity]; build from rectangle lemmas`
proof shape. Our file matches; `measurableSet_predictable` is a near-twin of their
`measurableSet_predictable_Iic_prod`.

**Predictable scope nuance (open question for Degenne).**
`lem:elementaryPredictableSet_stochasticInterval` is ℕ + bounded in the blueprint — exact match.
But `lem:predictable_stochasticInterval` is stated *generally* (any stopping time / time domain),
while we prove only `ℕ`. So we: prove the ℕ case (#440's body asks for "the lemmas above it" and
the section is ℕ-focused); do **not** `\leanok` the general statement (no overclaim); and flagged
it in the PR body for Degenne to decide (narrow the blueprint to ℕ, or keep it general with ours
as the discrete case). General/continuous-time predictability is a separate argument.

**#439 don't-reinvent check.** Issue #439 showed Degenne's reflex: he found the crossing-time
lemmas already in Mathlib and marked them `\mathlibok`. So we checked our two private `WithTop ℕ`
helpers against Mathlib's ENat API (`add_one_le_iff`, `lt_coe_add_one_iff`, `lt_add_one_iff`):
`coe_lt_iff_coe_succ_le` already delegates to `ENat.add_one_le_iff`; `lt_coe_iff_le_coe_sub_one`
is a problem-specific left-endpoint reformulation, not a verbatim duplicate. Nothing to remove.

**Version reconciliation.** Our pin (BrownianMotion `16d15eb`, Lean `rc1`, Mathlib `f233061`) is
~10 commits behind upstream `master` (`fa590b1`, Lean `rc2`, Mathlib `c87cc97`, incl. Mathlib
bump #443). We **decoupled**: did *not* bump the whole MathFin portfolio; their CI built against
their toolchain and passed (10m41s). Verified the API we depend on is unchanged on latest master
(`ElementaryPredictableSet` byte-identical; stopping times modelled `Ω → WithTop ι` against
`Filtration ι` throughout). The `kex-y/BP-cadlag` branch that appears to delete the interval
statements is a stale Dec-2025 branch (it predates them), not an active rework.

## Reusable workflow

**Setup.** Fork checkout: `/mnt/c/Users/rapha/Documents/Code/brownian-motion`. Remotes:
`origin` = upstream (RemyDegenne), `fork` = ours (raphaelrrcoelho). The local
`upstreaming-dashboard` branch is stale — always `git fetch origin` and branch off `origin/master`.

1. **Author + validate in our repo first.** Stage the file under `upstream/brownian-motion/`;
   validate green via the lean-repl daemon (overwrite-onto-a-`MathFin`-module-path trick above).
2. **Branch off latest master in a worktree** (keeps the user's fork checkout untouched):
   `git worktree add -b <branch> ../<dir> origin/master`.
3. **Drop the file in** at its module path, add an alphabetical `public import` line to
   `BrownianMotion.lean`, commit (`feat: …`, **no `Co-Authored-By`**), `git push fork <branch>`.
4. **PR-first, claim-after-green.** Open a *draft* PR
   (`gh pr create --draft --base master --head <owner>:<branch>`); let their CI ("Build project",
   ~10-min Lean build) validate against their toolchain. If green: `gh issue comment <n> --body
   "claim"` and `gh pr ready <pr>`.

**Conventions / lessons.**
- *Code-only PRs.* Degenne manages the blueprint `\leanok`/`\lean{}` himself (said so on #439) —
  don't touch `cadlag.tex`/`lean_decls` and risk a `checkdecls` red.
- *Decoupled validation.* Don't drag the whole MathFin portfolio onto upstream's pin to validate
  one file; their CI is the source of truth for the upstream build.
- *Claiming an issue needs an explicit user directive* — it's a public post under the user's
  identity (the agent's auto-classifier blocks it from a mere question).
- *Match the bar, don't overclaim.* Port to their exact conventions; never `\leanok` a blueprint
  statement we've only proved a special case of — flag the gap and let the maintainer decide.
- PR titles `feat: …`; bodies terse (`Closes #N` + any scope caveat), lowercase.
