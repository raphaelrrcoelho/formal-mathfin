# Program architecture — owning the corner across more than one field

**Date:** 2026-08-06 · **Status:** design proposal · **Companion:** [`applied-areas.md`](applied-areas.md)

The question: how should the repos be shaped for (1) maximum ownership of the
formally-verified-applied-mathematics corner, (2) the best autoformalization
foundry, (3) fastest theorem-coverage expansion, and (4) a mathematical
architecture that stays pristine?

---

## 0. The diagnosis — these are not four goals, they are two pairs

**Ownership and foundry quality are aligned and compounding.** Every additional
domain enriches the same three assets the foundry runs on: the proof-state cache,
the retrieval corpus, and the obstruction telemetry. A normalized goal state reached
in `Foundations/ItoIntegralL2` genuinely can recur in a time-series L² projection
argument — it is the same Hilbert machinery. `pipeline.toml` already says the state
cache is self-gating until cross-target recurrence is nonzero. **A second domain is
how that number becomes nonzero.** Multi-domain is not a tax on the foundry; it is
the foundry's training signal.

**Coverage expansion and pristine architecture are genuinely opposed.** Throughput
dilutes curation. This is the pair that needs engineering, because *discipline does
not survive contact with a working autoformalizer that lands a theorem every two
days.* Any plan that reconciles these two by resolving to be careful will fail.

So the architecture has one job in each direction: make the first pair's compounding
**mechanical** (one foundry, shared caches), and make the second pair's conflict
**structural** (a promotion ladder with machine-enforced ratios) rather than a matter
of vigilance.

---

## 1. Topology — four layers

```
L0  commons/            Lean. Field-neutral substrate Mathlib lacks. A DEPARTURE LOUNGE.
L1  apparatus/          Python pkg + Lean meta + reusable CI. The honesty machinery.
L2  formal-mathfin/     Domain library.  ── independent Lake projects
    formal-econometrics/     Domain library.
L3  foundry/            One retargetable pipeline. Domain content is DATA.
```

Four repos at steady state, not one per idea and not one big one.

### L0 `commons` — the ownership play

Field-neutral mathematics that several applied libraries need and Mathlib does not
have. From the substrate audit: **Brouwer and Kakutani fixed points** (absent —
verified), the **pointwise Birkhoff ergodic theorem** (absent), empirical-process
basics, mixing conditions.

**The rule that keeps it from becoming a junk drawer: it is a departure lounge, not
a home.** Every declaration carries an upstream target and an owner; a CI report ages
them; nothing is allowed to live there permanently. A `commons` that accepts code
with no upstream target is a `utils/` directory with better branding, and it will
rot the same way.

**Why this layer is the ownership move.** Owning the most theorems in econometrics is
a weak claim — EconCSLib can outproduce us and probably will. Being the group whose
code everyone else *imports* is the claim that compounds. Brouwer is missing from
Mathlib; general equilibrium, Nash existence, and every fixed-point equilibrium
argument need it. Build and upstream it and EconCSLib, the GE projects, and everyone
after them consume our work.

> **Upstreamed lemmas are the only theorems that cannot be out-produced.**

The muscle already exists — `docs/upstreaming.md`, BrownianMotion PR #446 merged.
This layer makes it a program rather than an occasional courtesy.

### L1 `apparatus` — the honesty machinery, extracted once

Today `tools/verify/` (ledger, coverage report, axiom-audit generator, corpus
model, blueprint render) and the three gate test-suites are excellent and are
**welded to one corpus**. Extract to a pip-installable package plus a set of
`workflow_call` GitHub workflows that domain libraries call in three lines.

Contents: ledger, coverage report, `axiom_audit_gen`, blueprint exporter/renderer,
values-review cadence test, forbidden-text gates, `formalization_status` schema,
HF dataset publisher.

What stays domain-side: the pillar/bridge vocabulary, the blueprint prose, the
benchmark JSONs, `AxiomAudit.lean`'s curated headliners.

This is what stops the second library from being a copy-paste of the first that
drifts out of sync within a quarter — the standard way a two-library program
quietly becomes one maintained library and one stale one.

### L2 Domain libraries — independent Lake projects, deliberately

Not a monorepo. Two reasons, and the first is decisive:

1. **The memory doctrine.** One Lean-loaded process on the box, ever. A shared Lake
   project means an econometrics edit re-elaborates finance, and you cannot build
   one library while checking another. Independence is what makes the box usable.
2. Each field's pillars/bridges should be answerable to that field. A shared build
   dilutes exactly the architectural claim that makes each library worth having.

Cost, stated honestly: `commons` must stay **thin**, because every domain library
rebuilds against it and a fat commons multiplies build cost by the number of
libraries.

### L3 `foundry` — one pipeline, domain content as data

The coupling audit says this is cheap. "MathFin" appears roughly thirty times across
`probe/`, and essentially all of it is (a) library-name strings in prompts, (b) the
pedagogical example constant `MathFin.zcb`, (c) `MathFin/<Section>/` path prefixes.
There is no hardcoded repo checkout path. **The dependence is lexical, not
structural.**

So:

```
foundry/domains/<name>/
  house.md         the house doctrine (currently house_context.py's embedded prose)
  exemplars.json   the domain's example constants — replaces MathFin.zcb
  pillars.yaml     pillar/bridge vocabulary for the depth gate and the judge
  pointers.yaml    module map for the depth gate's "consumes a real def" check
  target.toml      repo, branch, namespace prefix, Lake root
```

`probe/` becomes domain-free. The depth gate, triviality gate, semantic repair
cascade, decomposer, and gate battery all transfer unchanged — they are already
domain-neutral logic wearing domain-specific prompts.

---

## 2. The promotion ladder — how (3) and (4) stop fighting

The mechanism: **let the corpus grow fast in a tier that does not claim to be
architecture, and make promotion into the architecture a separate, gated act.**

| Tier | Requirements | Growth |
|---|---|---|
| **T0 frontier** | kernel-checked · axiom-clean · ledger row · declared `formalization_status` | fast — this is what the foundry produces |
| **T1 spine** | T0 **plus** consumed by ≥1 other declaration *or* cited by a bridge · blueprint-tagged with honest prose · survived a values review | slow |
| **T2 keystone** | T1 **plus** makes two pillars one theorem (a bridge) | rare, hand-picked |

This is `formalization_status` lifted one level: from *how faithful is this to its
source* to *how load-bearing is this in the architecture*. Both are declared, both
are enforced, neither is a vibe. A T0 entry is not second-class — it is honestly
labelled, which is the whole house style.

### The two ratios, machine-enforced

**Leaf fraction.** Declarations with proof-term in-degree 0 that are not headline
results. A rising leaf fraction *is* the operational definition of drifting from a
theory toward a catalogue. This is the single most valuable number the program can
track, and it is currently not measured.

**Spine density.** Spine entries per 100 frontier entries; bridges per pillar.

**Gate the derivative, not the level.** Frontier may grow without limit. But if
spine density falls more than X% below its trailing average, or leaf fraction rises
past its trailing average, CI goes yellow and the values review is *forced* rather
than merely due. That converts "pristine architecture" from a virtue into a build
status — the same trick `test_values_review_is_current` already plays with cadence.

**Buildability.** `blueprint_export` + LeanArchitect already produce a dependency
graph, but over the 29 hand-curated spine nodes in `docs/blueprint_nodes.json`, not
the corpus. `axiom_audit_gen.collect_proof_position_names()` already extracts
corpus→MathFin citations (305 names) — that is the *outer* edge set. Whole-corpus
in-degree needs a Lean meta pass over `ConstantInfo` value dependencies, or a
coarser module-level approximation from `importGraph`, which is already a
dependency. Modest build, high leverage.

**Set the thresholds by measuring first.** Phase 1 is computing today's leaf
fraction and spine density on the 348-entry corpus. Picking a number before knowing
the current value is how you get a gate that either never fires or fires constantly.

---

## 3. Making the foundry compound

Beyond domain packs:

**Shared, domain-partitioned caches.** `runs/state-cache.json`, `runs/gate-cache.json`
and the embedding cache are per-run today. Promote to a store partitioned by domain
but queried across all of them. The gate cache must stay generation-keyed on the
Mathlib/Lean pin — that invalidation is already implemented and must not be lost in
the move.

**A held-out eval set.** To claim "best foundry" there has to be a number that is
not overfit to the targets used for tuning. Freeze N targets per domain, never tune
on them, and report per tick: first-pass close rate, tokens per accepted theorem,
gate-rejection mix, spine-promotion rate. Without a held-out set the obstruction
report measures the tuning, not the tool. This is the difference between a foundry
that is improving and one that appears to be.

**Route by tier, not only by difficulty.** The foundry may produce T0 freely; T1
promotion should require a distinct review pass. Do not let the component optimizing
throughput also decide what is architecturally load-bearing — that is precisely the
conflict §0 says cannot be resolved by good intentions.

**Point the foundry at `commons`.** A Brouwer construction is an excellent foundry
target: hard, self-contained, no domain vocabulary, and the payoff is upstream
ownership. It is also a genuine test of the decomposer, which is what that path was
built for.

---

## 4. Sequencing — one timing rule that matters more than the rest

> **Extract exactly once, when library two starts. Not before, not after.**

Before is speculative generality — the seams get guessed wrong, and a wrong seam in
shared infrastructure is worse than duplication. After is a de-duplication across
two live corpora, each with its own drift, which is the expensive version.

Concretely: **formal-econometrics phase 0 should deliberately copy the apparatus.**
Run its first ~20 entries on the copy, note what actually diverged, and extract L1
against that evidence. The second library is the forcing function that reveals which
abstractions are real; do not pre-empt it.

| When | Move |
|---|---|
| Now | Foundry domain packs (`domains/mathfin/` first, extracted from `house_context.py` + `af_prompts.py`) — mechanical, testable against the existing corpus, and it makes library two a config change |
| Now | Measure leaf fraction and spine density on the 348-entry corpus. Numbers first, thresholds later |
| Library 2 phase 0 | Copy the apparatus deliberately. Do not extract yet |
| Library 2 at ~20 entries | Extract L1 `apparatus` against observed divergence. Cut over both libraries |
| When a second domain needs it | Create L0 `commons`, seeded with Brouwer/Kakutani, upstream-tagged from day one |
| Library 3 | Revisit whether a GitHub org is warranted |

**On the org:** it makes the collection legible as a program rather than scattered
personal projects, which is worth real money for an ownership claim. But the repo
URL is load-bearing in the Zenodo DOI, the arXiv paper, and the HF dataset. GitHub
redirects, so a move is survivable rather than catastrophic — but the cost only
grows as more links accumulate. **This is closer to now-or-never than it appears.**
Decide deliberately rather than by drift.

---

## 5. What not to do

- **A monorepo.** The memory doctrine forbids it outright.
- **Extracting the apparatus before library two exists.** You will guess the seams
  wrong.
- **A `commons` without mandatory upstream targets.** That is a `utils/` package.
- **Competing on theorem count.** EconCSLib is at 40k lines. The defensible position
  is the faithfulness contract — kernel-enforced scope declarations against their
  LLM-as-judge — and the upstreamed substrate. Volume is the one axis where we lose.
- **Letting the foundry promote its own output to spine.** See §3.
