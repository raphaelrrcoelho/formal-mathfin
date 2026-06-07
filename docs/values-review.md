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

## 2026-06-07 — commit 14ca008 — corpus 269

**Scope**: commit `14ca008` — Summit A′ (the time-dependent Itô formula:
three new Foundations modules + the process-weight generalization of
`WeightedQuadraticVariation`), the Kelly n-period iid model re-promotion,
and the wiring (`sc-thm-7.1.2` + `mf-kelly-n-periods-linearity` → `full`,
AxiomAudit Summit A′ section, blueprint spine node, docs).
**Panel**: three agents — (coherence + idiomatic), (slop + first principles
+ architecture), (clarity + inspired math + beauty).

| lens | verdict |
|---|---|
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS-WITH-NOTES |
| zero slop | PASS-WITH-NOTES |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS-WITH-NOTES |
| concept clarity | PASS-WITH-NOTES |
| beautiful, elegant math | PASS |

**Blocking findings**: none.

**Checks that mattered**: the boundary-cancellation algebra of the named-limit
core was verified symbolically — the discrete 2D identity makes the unbounded
`f(T,B_T) − f(0,B₀)` cancel, so "the L² estimate only ever sees three
vanishing terms" is literally true, not prose; the Kelly repair is genuine
first principles (`integral_log_kellyReturnMeasure` *computes* the two-point
integral, `kellyGrowth_n_periods` is real linearity of expectation over
`Measure.pi` — no step is `rfl`); a dead-hypothesis sweep over every new
public theorem found every binder consumed (including both joint-continuity
hypotheses of the CLM theorem); every `nlinarith` carries certificate hints
(the `(u+v+w)² ≤ 3(u²+v²+w²)` step via the three cross-difference squares);
no Mathlib lemma yields joint continuity from bounded one-variable partials,
so the corner-split Lipschitz route of `continuous_uncurry_of_bdd_partials`
is canonical, and `tendsto_riemann_L2_process` duplicates no Mathlib
Riemann-DCT result (bespoke `NNReal` `timeMeasure`); the `sc-thm-7.1.2`
snippet matches `ito_formula_td_L2_bddDeriv` hypothesis-for-hypothesis, and
the unbounded-coefficient gap is named everywhere it matters.

**Fixed before this verdict** (triaged minor, fixed in `14ca008`):
1. `integral_increment_sq` duplication — the TDRemainder copy re-derived
   `ItoIsometryAdapted.integral_increment_sq` at the bare `MathFin` namespace
   (a latent ambiguity trap since `ItoFormulaTD` opens that namespace);
   deleted, the call site consumes the existing lemma, the genuinely-new
   `integrable_increment_sq` companion stays.
2. Three dead nonneg `have`s in `tendsto_ito_remainder_td` left by the
   memLp hoist (self-caught pre-panel, confirmed by the panel's sweep).
3. `tendsto_riemann_continuous` had been widened to public with a docstring
   claiming the Itô layers consume it — they consume the L² wrappers;
   reverted to `private` with the honest description.
4. `docs/blueprint.md` BS-PDE section still called `sc-thm-7.1.2` "still
   `reduced_core`"; rewritten to the bounded-regime status (the deferral
   argument stands: the BS value function's Γ is unbounded as `S → 0`).
5. Kelly horizon-binder drift (`T : ℕ` vs the file's new `n : ℕ` register)
   in `kelly_n_periods_deriv_at_kelly` + its benchmark snippet.

**Recorded actions**:
1. *(minor, DONE same day — consolidation follow-up commit)*
   increment-second-moment fact consolidated: `ItoIsometryAdapted` now
   imports `WienerIntegralL2` (acyclic) and `integral_increment_sq` /
   `integral_two_increment` are one-step instances of
   `covariance_increment_aux` (diagonal and shared-start), `hBmeas` dropped
   from both signatures as dead; module docstring's stale "(non-`module`)
   file" re-derivation apology rewritten. The `SimpleProcess`/`L2Predictable`
   unification remains the only deferred item of that paragraph.
2. *(minor, DONE same day — same commit)* the Term-II scaffolding hoist
   completed: private `measurable_pathIntegral` + `abs_pathIntegral_le` are
   the single home of the path-integral measurability/bound, consumed by
   `tendsto_riemann_L2_process`, the new per-`n` companion
   `integrable_riemann_defect_sq`, and `memLp_pathIntegral_process`;
   `tendsto_weighted_qv_process` lost its 19-line duplicate block.
3. *(nit, RESOLVED — no action at this pin)* `abs_sub` is **not** deprecated
   in the pinned Mathlib: it is the live `to_additive` companion of
   `theorem mabs_div` (`Algebra/Order/Group/Abs.lean:81`), and the bridges
   elaborate with zero deprecation warnings. The reviewer's claim was a
   newer-Mathlib artifact — the documented public-loogle-vs-pin caveat.
   Re-check at the next toolchain bump.
4. *(nit, accepted)* `coverage.md`'s "pre-re-audit historical record" line is
   deliberately stale provenance; the panel flagged it, the file already
   frames it as such — no action.
5. *(nit, DONE same day — same commit)* `PoissonCounting`'s two unused-`hr`
   warnings (pre-existing, surfaced by the consolidation rebuild) pruned as
   a dead-positivity cascade: three private Gamma-CDF calculus lemmas
   (`hasDerivAt_gamma_antideriv`, `integral_gammaPDFReal_sub_succ`,
   `integral_gammaPDFReal_one`) never needed `0 < r` — the telescoping
   antiderivative identities are formal algebra; public signatures
   untouched.

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
