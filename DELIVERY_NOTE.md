# Delivery Note

This repository is a reproducible Lean 4 / Isabelle verification artifact for stochastic-process benchmark statements drawn from Saporito-style course material.

The current honest status is:

- **25 entries** are delivery-claim ready (`full + library_wrapper`): 13 real derivations or structural definitions, 12 direct Mathlib invocations.
- **40 entries** are `reduced_core`: either algebraic/analytic core checks or Lean specifications where the textbook conclusion is encoded as a structure axiom rather than derived.
- **0 entries** are `placeholder`.

A previous round of edits over-stated the audit by promoting 45 specification-based entries to `full`. Those promotions were rolled back: a structure with the textbook conclusion as a field, projected via `:= h.conclusion_field`, is not a derivation, and the audit should reflect that. After the rollback, real-proof work began on the Tier-A list in `docs/superpowers/specs/2026-05-06-real-proof-tiers.md`. The first delivery from that list is `mart-thm-2.2.9` (discrete martingale transform), now derived from `martingale_nat`, the conditional-expectation pull-out, and `condExp_sub`.

## What Is Ready To Say

Safe wording:

> We built a reproducible Lean 4 / Isabelle verification artifact covering 65 stochastic-process benchmark statements. All active prover obligations type-check. Under a strict faithfulness audit, 25 entries are full or direct library-backed theorem formalizations: 13 derive the textbook conclusion (or are structural definitions), 12 directly invoke a named Mathlib theorem whose statement matches the benchmark. The remaining 40 entries are `reduced_core`: the active code is honest but is either a narrower algebraic/analytic check or a Lean specification structure that pins down the textbook STATEMENT (so any inhabitant satisfies it by construction) without DERIVING the conclusion. No entries are `placeholder`. The artifact identifies precisely where current Lean/Isabelle libraries support the course material and where new stochastic-process infrastructure is required.

Avoid:

> We formally proved all theorems in the course.

That claim is not supported. The honest version:

> We have faithful Lean STATEMENTS for all 65 textbook theorems, real derivations or library-backed proofs for 25 of them, and explicit specifications for the remaining 40 documenting what a real proof would need to construct.

## Current Numbers

Refresh with:

```bash
python3 -m python.coverage_report
```

Current report:

```text
theorems: 65
active Lean-only: 40
active Isabelle-only: 0
active Lean+Isabelle: 25
Lean code entries: 65
Isabelle code entries: 25
quarantined SymPy references: 55

full theorem statements: 13
library theorem wrappers: 12
reduced formal cores: 40
placeholders/stubs: 0
delivery-claim ready: 25
```

## Why This Is Valuable Even At 20/65

- A runnable benchmark suite for stochastic-process formalization with reproducible Docker verification.
- Clear separation of formal prover checking from CAS-style symbolic checking.
- Precise Lean specifications for every textbook theorem — these document what a future Mathlib-grade construction must produce, and they are useful targets for collaboration.
- A three-tier roadmap (`FORMALIZATION_ROADMAP.md` + `docs/superpowers/specs/2026-05-06-real-proof-tiers.md`) showing which theorems support real Lean proofs today (Tier A: ~10 entries, including conditional Jensen and Doob L^p that Mathlib flags as TODOs), which require building Brownian motion (Tier B), and which require the stochastic-integral layer (Tier C, research-grade).

## Suggested Message To Saporito

Draft:

> Professor Saporito,
>
> I have been building a reproducible Lean 4 / Isabelle verification artifact around stochastic-process results from your course material. It now covers 65 benchmark statements with all active prover obligations type-checking. Under a strict audit:
>
> - 20 entries are real derivations or direct Mathlib-library invocations.
> - 45 entries are Lean specifications: the structure encodes the textbook hypotheses and conclusion in Lean, so it precisely documents the theorem, but it does not derive the conclusion from foundational primitives.
> - 0 entries are placeholders.
>
> The honest goal of this round is to map the Lean stochastic-process landscape: which textbook theorems support real Lean proofs today (with current Mathlib), which require Brownian motion to be built first (years-of-Mathlib-effort scale), and which require the stochastic-integral layer (research-grade). The roadmap document lays out about 10 theorems where a real Lean proof is achievable in the near term — including conditional Jensen's inequality and Doob's L^p inequality, which Mathlib flags as TODOs and where my work would land upstream.
>
> If useful as a collaboration seed, I would value your guidance on which theorems are mathematically most important to attack first in the Tier-A near-term-achievable set.

## What To Send

Include:

- `DELIVERY_NOTE.md`
- `FORMALIZATION_STATUS.md`
- `FORMALIZATION_ROADMAP.md`
- `docs/superpowers/specs/2026-05-06-real-proof-tiers.md`
- `README` or short command note pointing to Docker
- `benchmarks/`
- `python/coverage_report.py`
- `tests/test_router.py`
- `docker/Dockerfile.verify`
- `docker/docker-compose.yml`

Core commands:

```bash
python3 -m pytest tests/test_router.py
python3 -m python.coverage_report
docker compose -f docker/docker-compose.yml run --rm verify benchmarks/cross_validated.json --config hybrid_verify.toml --timeout 240
```

For full benchmark verification:

```bash
for f in benchmarks/*.json; do
  docker compose -f docker/docker-compose.yml run --rm verify "$f" --config hybrid_verify.toml --timeout 240
done
```
