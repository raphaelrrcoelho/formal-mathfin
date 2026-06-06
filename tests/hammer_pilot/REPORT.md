# LeanHammer pilot — verdict: DO NOT ADOPT (this rev × this toolchain)

Date: 2026-06-06. Branch `hammer-pilot`. Hammer @ `c997b8dc` (main,
targets Lean v4.30.0 **stable**) on our `v4.30.0-rc2` + Mathlib `c87cc97`.
Privacy held throughout: every pilot file pins
`set_library_suggestions sineQuaNonSelector.intersperse currentFile`
(local symbolic selection); no goal context left the machine.

## Evidence

15 goals extracted verbatim from MathFin proof sites (PilotA algebra/
inequalities, PilotB measure-theory premise lookups, PilotC stretch).
A and B were run; C was skipped as decision-irrelevant after A+B.

| Goal class | Result |
|---|---|
| A1 field identity (our `grind` CLOSES this) | tactic "succeeds" → **kernel rejects**: `(kernel) unknown constant '_example._proof_7'` |
| A2/A3/A5 nlinarith-class | `grind => sorry` suggestions + same kernel rejection / heartbeat timeout |
| A4 division-monotone | pipeline exhausted ("aesop failed") |
| A1–A5 with `{disableGrind := true}` (pure Aesop+Zipperposition+Duper) | **0/5**, suggestions degenerate to `sorry` |
| B1 `Integrable.const_mul` lookup | `grind => sorry` + kernel rejection |
| B2 `Measurable` exp-affine | same |
| B3 `MemLp.integrable_sq` lookup | same |
| B4 `Finset.sum_le_sum` | deterministic heartbeat timeout |
| B5 exp/div composite | deterministic heartbeat timeout |
| **Wall clock, PilotB (5 goals)** | **9366 s ≈ 2.6 h** (~31 min/goal; paper reports <10 s avg) |

Score: **0/10 kernel-accepted**, with a *systematic* failure mode, not a
capability gap: hammer's grind driver emits auxiliary constants
(`_example._proof_N`) that never reach the kernel environment — every
"found" proof is rejected at kernel replay, in both the REPL daemon AND
plain `lake env lean`. Root cause consistent with the one-step toolchain
skew (their main targets v4.30.0 stable; grind's internals moved between
rc2 and stable). The latency is a second, independent disqualifier.

Where hammer found *anything*, our existing toolkit already had it
(`grind` closes A1 directly — see docs/patterns.md "In-Lean automation");
where our toolkit fails (nonlinear inequalities), hammer failed too.

## What worked

- Build integration: Hammer+Duper+auto+premise-selection compile green
  against our pins (1157 jobs) with mathlib-last ordering (batteries kept
  at Mathlib's rev — no Mathlib rebuild) and the lean-toolchain rewrite
  guard (lake update DID rewrite it to v4.30.0; restored from snapshot).
- Privacy configuration: local selector ran throughout (the wall-clock
  profile is local-compute-bound; no cloud endpoint contacted).
- Ledger: the Hammer cluster is in `PIN_EXCLUDED_PACKAGES` — adding the
  dep restaled **zero** of 267 entries (boundary test enforces no library
  import).

## Re-evaluation trigger

Re-pilot on the `v4.30.0-rc2 → v4.30.0-stable` toolchain bump (lean-interact
0.11.4 already supports stable; LeanHammer main targets it exactly):

```bash
git checkout hammer-pilot && docker compose -f docker/docker-compose.yml \
  run --rm --entrypoint sh verify -c 'cd /app && lake env lean tests/hammer_pilot/PilotA.lean'
```

If reconstruction lands kernel-clean there, re-run the full pilot and
revisit adoption (with the self-hosted premise server for recall —
`set_option premiseSelection.apiBaseUrl` — still privacy-local).
