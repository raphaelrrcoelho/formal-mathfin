# Values review — the final verification

The mechanical gates (`tests/test_values.py`, `AxiomAudit*.lean`, the
verification ledger, the CI gates in `build.yml`) enforce everything a
machine can check. This protocol covers what a machine cannot: the judgment
lenses that define the repo's quality bar. The **review is judgment** — a
multi-agent panel reading the work — and the **pipeline enforces that it
happens**: `tests/test_values.py::test_values_review_is_current` fails when
the corpus has grown more than 12 entries past the last recorded verdict
below. A regex cannot check "beautiful"; a regex can check "nobody looked."

## The eight lenses

1. **Inspired math quality** — each result earns its place: a structural
   fact or a clean mechanism, not bookkeeping dressed as a theorem.
2. **Mathlib / BrownianMotion (Degenne) coherence** — consume the libraries'
   machinery, never re-derive it; choose the canonical upstream API; no thin
   wrappers around single upstream lemmas.
3. **Zero slop** — no opaque discharges where a certificate-shaped proof
   exists, no ring-fallback hiding the conceptual step, no duplicated
   sub-derivations, no dead hypotheses.
4. **Architectural ingenuity** — the decomposition is the right shape: each
   lemma carries one idea, the pieces compose so future results get cheaper,
   nothing is proved at the wrong level of generality.
5. **First principles** — conclusions are derived from honest hypotheses;
   no hypothesis secretly contains the conclusion; no theorem that is its
   own definition unfolded.
6. **Mathlib / BrownianMotion idiomatic register** — naming, hypothesis
   style, namespace and `variable` discipline, statement shapes a Mathlib
   reviewer would accept.
7. **Concept clarity** — every docstring tells the honest mathematical
   story (what is proved, from what, what is *not* claimed); a strong
   probabilist reads the statement and says "yes, that is the theorem."
8. **Beautiful, elegant math** — the proof is the obviously-right argument
   once seen; the writeup neither obscures a beautiful idea nor dresses up
   a trivial one.

## Protocol

- **When**: at the close of any session that adds or changes proof content;
  at latest every 12 corpus entries (the CI ratchet's slack — one session's
  growth).
- **How**: at least three independent review agents, the lenses split among
  them, reading the session's diff and its context (read-only; never running
  Lean). Findings are triaged blocking / minor / nit. **Blocking findings
  are fixed before the verdict is recorded**; minor findings become recorded
  actions with owners (usually: next session's opening move).
- **Record**: append a verdict block below, headed exactly
  `## YYYY-MM-DD — commit <sha> — corpus <N>` (the test parses this line),
  with per-lens verdicts and the findings ledger. Verdicts are honest:
  PASS-WITH-NOTES is a normal outcome; an undeserved PASS is itself a values
  violation.

## Verdict log

## 2026-06-06 — commit f1b0dcd — corpus 269

**Scope**: commits `9db04f8` (Merton dominance + classic display + Markov
path law), `aec693d` (values-gates round), `f1b0dcd` (HF publish CI) — four
new Lean modules, one bridge lemma, the enforcement tooling.
**Panel**: three agents — (coherence + idiomatic), (slop + first principles
+ architecture), (clarity + inspired math + prose honesty).

| lens | verdict |
|---|---|
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS |
| zero slop | PASS |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS-WITH-NOTES |
| beautiful, elegant math | PASS |

**Blocking findings**: none.

**Checks that mattered**: `bsV_spot_tangent_le` duplicates no Mathlib
support-line lemma (it is the delta-substituted form, needing the
closed-form Greek); the Markov factorization is genuinely derived (base
case computes through `traj_map_frestrictLe` + `partialTraj_self` +
`piUnique`; inductive step through the comp-product marginal recursion —
no step smuggles the conclusion); `mertonCallTerm_eq_bsV`'s trivial proof
is a feature (it validates the definition is the BS value, and two modules
consume it); "jump risk is never free" is an exact gloss of the inequality
under its hypotheses; the classic display matches Merton (1976) eq. (16)
weights/rates/vols precisely; the converse direction of the Markov
characterization is nowhere claimed.

**Recorded actions**:
1. *(done in this commit)* corpus-iteration was triplicated across
   `axiom_audit_gen.py` / `hf_dataset.py` / `ledger.py` — extracted
   `tools/verify/corpus.py`; the two new tools now share it. `ledger.py`
   deliberately untouched (verified load-bearing hashing code) — fold into
   its next structural pass.
2. *(nit, open)* `MertonClassicDisplay.lean` docstring: "absorbs the jump
   factor" is terse about the mechanism (the rate-shift identity supplies
   it two paragraphs later); sharpen on next touch of the file.
3. *(nit, accepted)* the rfl-tripwire's tail regex is documented
   "good enough" in-file; a Lean-aware scanner is not worth its weight while
   the catch rate is this good (1 for 1 on first run).
