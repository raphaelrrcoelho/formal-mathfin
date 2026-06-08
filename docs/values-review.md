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

## 2026-06-08 — commit 3beb170 — corpus 269

**Scope**: the Feynman–Kac → BS-PDE *keystone core* — step 1 (kernel-side heat equation
`∂_t U = ½ ∂_xx U` for sub-Gaussian payoffs, in `Foundations/FeynmanKacHeatEquation`: the
completing-the-square mean-shift, the sub-Gaussian envelope, the spatial kernel bound, three
diff-under-integral derivatives, the `feynmanU_heat_equation` identity) + the bridge
`bsV_eq_discount_feynmanU` (bsV = discounted heat flow, making `feynmanU` load-bearing for pricing)
and Delta-via-FK `hasDerivAt_bsV_S_fk` (in `BlackScholes/PDEFromFeynmanKac`). The full `∂_τ`/PDE
assembly is deferred (its brute-force domination is infeasible — see below).
**Panel**: three Sonnet reviewers (coherence+idiomatic · zero-slop+architecture ·
inspired-math+first-principles+clarity+beauty) reading the diff, + Opus synthesis and judgment.

| lens | verdict |
|---|---|
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS-WITH-NOTES |
| zero slop | PASS-WITH-NOTES |
| architectural ingenuity | PASS-WITH-NOTES |
| first principles | PASS |
| idiomatic register | PASS-WITH-NOTES |
| concept clarity | PASS-WITH-NOTES |
| beautiful, elegant math | PASS-WITH-NOTES |

**Blocking finding (fixed in this commit's follow-up)**: `PDEFromFeynmanKac` carried ~112 lines of
orphaned, never-consumed `∂_τ` domination scaffolding (`hasDerivAt_kernelCurve`, `heatKernel_curve_le`,
`integrable_tau_bound`) — machinery for a brute-force differentiate-under-the-integral that
heartbeat-times-out and is being abandoned for a leaner route. Removed (recoverable from `3beb170`);
the file now holds only the FK representation, the bridge, and the FK-Delta, with an honest module
docstring.

**Recorded actions (deferred to the next FK round, batched to avoid re-staling the ledger)**:
1. *(top priority — leaner + elegant + architecture; all three panels)* `hasDerivAt_phi`,
   `hasDerivAt_feynmanU_t/_x/_xx` are the same dominated-convergence proof at different parameters;
   unify into ONE parametric `hasDerivAt_feynmanU_param` (≈200 → ≈100 lines).
2. failing 1, extract the verbatim-duplicated `heatKernel_temporal_le`, polynomial-bound, and
   `hFt_int` blocks as shared private helpers (≈35 lines).
3. *(concept clarity)* `exp_mul_heatKernel` docstring over-claims "Cameron–Martin mean shift" — it is
   the completing-the-square identity (the *analytic core* of the shift, not the measure-change
   theorem); retitle honestly.
4. *(idiomatic)* `open Real` is declared but `Real.` is qualified ~200×; drop it.
5. *(architecture)* `callPayoff_continuous`/`le_exp` are call-payoff facts → `BlackScholes/Call.lean`.
6. *(zero slop)* `hasDerivAt_feynmanU_xx`'s closing `linarith [show … ring]` should mirror `_x`'s
   clean `calc … ring`.

**Declined (Sonnet suggestions overruled on the math)**:
- "compose `hasDerivAt_kernelCurve` from the `∂_t` + `∂_y` partials" — wrong: the curve moves both
  kernel arguments, so total = sum-of-partials ONLY under joint differentiability, which the
  partial-`HasDerivAt`s do not provide; the from-scratch differentiation of the explicit kernel is
  the correct route.
- "`heatKernel_shift_le` without variance-widening (same-`t` bound)" — false: `K(t,z−x)/K(t,z−x₀)`
  is unbounded in `z`; widening to `2t` is essential for the domination.

**Verdict**: the keystone core is sound, honest, and largely elegant — the inspired ideas
(kernel-side differentiation, the mean-shift, the heat-equation collapse) are present and correct.
The first-try slop (the duplicated diff-under-integral template; the brute-force `∂_τ` scaffolding) is
the natural debris of a large climb: the scaffolding is removed here, the duplication is scheduled for
a parametric pass.

## 2026-06-07 — commit 321eb4f — corpus 269

**Scope**: commit `321eb4f` — `bsV_eq_feynmanU` (the Feynman–Kac representation of
the Black–Scholes call price) in the new bridge module
`MathFin/BlackScholes/PDEFromFeynmanKac.lean`, plus its umbrella import. This is
step 2 of the Feynman–Kac → BS PDE keystone (which makes the previously
consumer-less `Foundations.FeynmanKacHeatEquation.feynmanU` load-bearing for
pricing); steps 1 (kernel-side heat equation), 3 (change of variables) and 4
(assembly) remain in progress.
**Panel**: three Sonnet agents on the mechanical lenses — (coherence + idiomatic
register), (zero slop + dead-code/forbidden-text), (architecture + first-principles
+ docstring fidelity) — and Opus on the judgment lenses (inspired math, first
principles, concept clarity, beauty).

| lens | verdict |
|---|---|
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS-WITH-NOTES |
| zero slop | PASS |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS (after the fix below) |
| beautiful, elegant math | PASS |

**Blocking findings**: one, fixed before this verdict. The theorem docstring's
"Proof chain" described a *two-step* route (`feynmanU_eq_integral_of_map` with
`B = id` over `gaussianReal 0 (σ²τ)`, then a **separate** `integral_map` rescale)
that was never written: the actual proof is a *single* `feynmanU_eq_integral_of_map`
with `B = (σ√τ · ·)` over the standard normal, the variance rescale discharged as
its hypothesis `hmap`. The docstring — the concept-clarity instrument — was
rewritten to describe the one-step proof that exists.

**Checks that mattered**: all four hypotheses are consumed (`hS` via
`Real.exp_log` and the `BSCallHyp` constructor; `hK`/`hσ` via `BSCallHyp`; `hτ`
via `Real.sq_sqrt` and `BSCallHyp`) — no dead binders; forbidden-text scan clean
(no `sorry`/`native_decide`/`?`-tactics/etc.); the statement is a genuine identity,
not a disguised `rfl` (the closed-form `bsV` and the integral `feynmanU` are
definitionally distinct) and not vacuous; it consumes the canonical upstream API
(`gaussianReal_map_const_mul`, `feynmanU_eq_integral_of_map`, `bs_call_formula`,
`HasLaw.id`) with no thin wrappers or re-derivations; the NNReal-coercion block and
the two `neg_mul` reconciliations are load-bearing glue, not slop; correct
file/layer (a `BlackScholes/` bridge over the Foundations FK layer) at the right
generality (the concrete call payoff baked in, not over-abstracted).

**Declined reviewer flags** (with reason):
1. *(minor)* "redundant `public import MathFin.BlackScholes.Call`" — declined: this
   file directly consumes `bs_call_formula`/`bsTerminal`/`BSCallHyp`, so the
   explicit import is correct direct-dependency hygiene; the file's transitive-import
   comment scopes only the Mathlib base, not directly-used modules.
2. *(minor)* "`NNReal.coe_mk` is deprecated" — declined: the pinned-Mathlib build is
   warning-clean, so this is the documented public-Mathlib-newer-than-pin artifact
   (the same class as the `abs_sub` false positive in the `14ca008` review).
3. *(nit)* "'until now consumed by nothing' is stale" — declined: "until now
   consumed by nothing, becomes load-bearing" is self-consistent and correct.

**Recorded actions**:
1. *(minor, out of scope — future cleanup)* the exp-sign convention mismatch
   between `Call.lean` (`Real.exp (-r * T)`) and `PDE.lean` (`Real.exp (-(r * τ))`)
   forces two cosmetic `neg_mul` reconciliations in this file; unify the convention
   in a pass over the lower BS modules.

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
