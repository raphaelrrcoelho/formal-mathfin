# Learnings

Notes from the 2026-05-22 session that pushed `docs/roadmap.md`'s
three depth-theorem candidates to completion (continuous K-convexity bridge,
multi-step Merton tree, full reflection-principle bijection — Phases 15
and 16). This document captures what worked, what was harder than expected,
and patterns worth reusing.

It is *not* a reference for what's in the library — that's `README.md`,
`docs/coverage.md`, and the source itself. It is a record of the
*how*: idioms, traps, and structural intuitions.

## Structural patterns

### Three-scale unification

A single mathematical principle often manifests at multiple scales of
resolution: payoff (discrete combinatorial), finite-state price (discrete
linear combination), continuous price (calculus). The cleanliness payoff of
formalisation is naming the principle once and writing the three scales as
corollaries.

Example: **K-convexity** of the call now lives at three scales in
`BlackScholes/StrikeConvexity.lean`:

* `convexOn_call_payoff` — payoff `K ↦ max(S − K, 0)` convex (combinatorial:
  `sup` of an affine function and zero).
* `callPrice_finiteState_convexOn_K` (in `ConvexPricingFunctional.lean`) —
  pricing under non-negative state prices preserves convexity.
* `bsV_strike_convexOn` — continuous BS price convex on `(0, ∞)` via
  `convexOn_of_deriv2_nonneg'` and the closed-form second derivative.

Before this session, the three lived as essentially independent claims.
Now the second-derivative computation in `BreedenLitzenberger.lean`
(`lognormalTerminalPDF_nonneg`) reads as "the infinitesimal face of the
same convexity," and `Spreads.lean` reads it as "the discrete face."

The pattern generalises. Wherever a property holds at a payoff level and
is preserved by a non-negative pricing functional, three scales suffice.

### One-period inequality + induction → multi-step theorem

Discrete dynamic-programming arguments lift from one period to `n` periods
by induction *if and only if* you have a monotonicity lemma for the
one-period operator. The structure:

1. Prove the substantive content as a one-period inequality
   (`call_one_period_continuation_dominates_intrinsic`).
2. Prove monotonicity of the one-period operator
   (`binomialOptionPriceOnePeriod_mono`).
3. The multi-step result is induction: at step `n+1`, the European recursion
   gives `one-period(binomialPrice n at daughters)`. By IH, the daughter
   values are bounded; by monotonicity, the bound lifts; the one-period
   inequality closes the step.

Used in `americanCallPrice_le_binomialPrice`. The Bellman-`max` structure
of `americanPrice` makes both intrinsic and continuation bounds visible.

### Algebraic-identity / counting-bijection decoupling

For combinatorial-bijection theorems, separate the *algebraic identity* on
the path level from the *counting* statement at the cardinality level. The
algebraic identity has no decidability or hitting-time prerequisites and
proves cleanly by sum decomposition. The counting bijection then uses the
identity as one ingredient and adds first-hitting-time machinery
(`Finset.min'`) for the other.

Used in `Binomial/PathReflection.lean`:

* `walkPos_reflectAfter_ge` — algebraic identity, no hitting-time anywhere.
* `firstHit`, `HitsLevel`, `reflectAtFirstHit`, `reflectionPrincipleEquiv` —
  counting layer, built on top.

The algebraic identity is what generalises. The counting layer is a clean
application; if a different reflection-style theorem needs a different
counting structure (e.g. ballot problem), the identity remains the same.

## Lean / Mathlib technical idioms

### Type-inference traps with coerced lambdas

```lean
-- WRONG (in a Finset (Fin n) context):
(Finset.univ : Finset (Fin n)).filter (fun i => (i : ℕ) < k)
-- Error: Lean picks i : ℕ from the (i : ℕ) annotation, then Finset.univ
-- has wrong type.

-- RIGHT (option 1): annotate the lambda argument
(Finset.univ : Finset (Fin n)).filter (fun (i : Fin n) => (i : ℕ) < k)

-- RIGHT (option 2): use `.val` to avoid coercion ambiguity
(Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)
```

Pattern: whenever a lambda is passed to a polymorphic function and the
argument type is ambiguous, explicit annotation or `.val` resolves it.
Cost the reflection-principle file ~20 minutes of debugging until the
fix landed in one shot. Worth catching early.

### `abbrev` vs `def` for Decidable propagation

```lean
-- WRONG: blocks typeclass synthesis from seeing through.
def HitsLevel (a : ℤ) (ω : Fin n → Bool) : Prop :=
  (hittingSet ω a).Nonempty
-- Then: `if h : HitsLevel a ω then ...` fails Decidable synthesis.

-- RIGHT:
abbrev HitsLevel (a : ℤ) (ω : Fin n → Bool) : Prop :=
  (hittingSet ω a).Nonempty
-- Now `Decidable (HitsLevel a ω)` is found via `Decidable ((...).Nonempty)`.
```

`abbrev` is `@[reducible] def` — Lean's typeclass system sees through it
during instance search. `def` is opaque to the elaborator. Use `abbrev`
for predicates whose decidability comes from an underlying construction.

### `omega` and the `set` tactic

`set x := expr with x_def` introduces an alias and rewrites occurrences,
but `omega` *does not always* see through the resulting hypotheses. When
omega's counterexample-display shows two different opaque variables that
ought to be the same, the culprit is often a `set` alias not being
unfolded.

Fix: avoid `set` for the variables that flow into omega's hypotheses.
Write out the long expressions or introduce `have` lemmas first.

### `convexOn_of_deriv2_nonneg'` for open intervals

Mathlib has two variants:

* `convexOn_of_deriv2_nonneg` — wants `ContinuousOn` and differentiability
  on the *interior*. For closed intervals.
* `convexOn_of_deriv2_nonneg'` — wants differentiability on the set
  itself. For *open* sets like `Set.Ioi 0`.

`bsV_strike_convexOn` uses the `'` variant since BS is only defined for
`K > 0`. Choose the variant by domain openness.

### `HasDerivAt.congr_of_eventuallyEq` for `deriv f` identification

To prove that `deriv f` has a specific value at a point, when `f` has a
known closed-form derivative, the pattern is:

```lean
-- Local equality of derivatives in a neighborhood:
have h_ev : (fun K' => deriv f K') =ᶠ[nhds K] explicit_first_deriv := by
  filter_upwards [open_set.mem_nhds h_K_pos] with K' hK'
  exact (hasDerivAt_f hK').deriv

-- Transport HasDerivAt of the explicit form to HasDerivAt of `deriv f`:
have h_KK_for_deriv_f : HasDerivAt (deriv f) (second_deriv K) K :=
  h_KK.congr_of_eventuallyEq h_ev
```

Used in `deriv_bsV_eventuallyEq` and the third hypothesis of
`bsV_strike_convexOn`. This is *the* idiom for "second derivative via
intermediate explicit first derivative."

### `Subtype.ext` for `Equiv.left_inv` / `Equiv.right_inv`

When proving `left_inv` / `right_inv` of an `Equiv` between subtypes, a
naive `ext` may peel into pointwise function equality (since the underlying
type may be a function type), which is the wrong granularity.

```lean
-- Use:
left_inv ω := Subtype.ext (by ...)  -- the (by ...) proves val equality
```

Peels exactly one layer (Subtype to underlying value), leaving the
function-level equality to be discharged by the involution.

Used in `reflectionPrincipleEquiv`.

## Workflow patterns

### Daemon-first, lake-build-last

The Lean REPL daemon (`./scripts/lean-check.sh`) checks a single file in
5–30 s by reusing pre-loaded Mathlib oleans. Full `lake build` re-elaborates
the changed module's transitive dependents (often 5–15 minutes).

Workflow:

1. Edit a file.
2. Daemon-check it.
3. Iterate on errors until daemon green.
4. Run `lake build` once at the end (or before committing) to confirm
   cross-file integrity.

The reflection-principle file went through ~6 daemon-check iterations
before reaching `success: true`. Each iteration ~30s. Equivalent
lake-build iterations would have been ~30 minutes total instead of 3.

Caveats: the daemon doesn't write `.olean`s for downstream imports. After
the daemon green-lights a file, the umbrella import won't pick up changes
until a full `lake build` (or daemon restart). For multi-file refactors,
prefer one daemon-check per file plus a final lake build.

### Concrete LOC estimates calibrate

The roadmap predicted:

* Multi-step Merton: ~150 LOC. Actual: ~105.
* Continuous convexity: ~150 LOC. Actual: ~80 (file extension).
* Reflection principle full: ~300 LOC. Actual algebraic core ~180,
  bijection ~190 — ~370 total.

The roadmap was within ~20%. This kind of estimation matters when
deciding between "one focused session" and "spread across multiple
sessions." A 600-LOC roadmap is plausibly one session of focused work;
a 1500-LOC one is not.

### Cleanup-as-you-go beats cleanup-pass-later

The push-neg deprecation warnings in `MertonAmericanCallTree.lean` had
been pending across sessions. Folding the two replacements
(`push_neg at h` → `have h := not_le.mp h`) into the same commit as the
Phase 16-B work added ~5 lines of diff but eliminated the warnings
permanently. A dedicated cleanup pass would have been larger and harder
to motivate.

Apply: when you touch a file, fix the inline warnings if they're trivial
(< 5-minute effort each). Don't accumulate a backlog of "cleanup later"
items.

## Open opportunities

Notes on what would extend this session's work, with rough scope estimates.

### Discrete IVT for ±1 walks (~50 LOC)

The reflection-principle bijection currently requires `HitsLevel a ω` as
a hypothesis on both sides. With a discrete intermediate-value theorem
(`walkPos ω n ≥ a ⟹ HitsLevel a ω`), the right-hand side simplifies to
`{ω : walkPos ω n = 2a − b}` (no hitting condition). This unblocks the
classical **maximal-distribution theorem**

> `|{ω : max_k walkPos ω k ≥ a}| = 2 · |{ω : walkPos ω n ≥ a}| − |{ω : walkPos ω n = a}|`

which is the formula barrier-option pricers actually use.

IVT proof: induction on `n`, using `walkPos_succ` (step changes by ±1).
Likely ~50 LOC.

### Variance-optimal hedging in finite-state markets (~250 LOC)

Given a contingent claim `X : ι → ℝ` on a finite probability space and a
tradable subspace, the variance-optimal hedge is the orthogonal projection
in `L²(q)`. Concretely: minimise `E^q[(X − Δ · S)²]` over deltas in some
linear span. The minimiser is the projection.

This uses real linear algebra (orthogonal projection in inner product
space) and would establish the foundational version of the "quadratic
hedging" toolkit. Mathlib has `InnerProductSpace`, `orthogonalProjection`,
etc. — should slot in cleanly.

### First-hit on the upcrossing side (~80 LOC)

Currently `firstHit` requires `HitsLevel a ω` as a proof argument
(`(hittingSet ω a).min' h`). An alternative: define
`firstHit? ω a : Option ℕ` returning `none` for non-hit paths. This is
more ergonomic for computational reasoning and matches the typical
mathematical narrative ("the first hit, if it exists").

Could refactor `firstHit` into `firstHit?` and provide convenience
helpers. Mostly notation work, but unlocks cleaner downstream theorems.

## Anti-patterns to avoid

### "Just unfold the def" without checking what gets exposed

`unfold X at hyp` rewrites the *occurrence in `hyp`* but not in the goal.
If the goal also contains `X`, the hypothesis and goal will mention
different terms — and `omega`/`linarith` won't unify them.

Pattern that bit the `firstHit_le` proof: I had

```lean
have h_mem := (...).min'_mem h
unfold hittingSet at h_mem
-- Now h_mem talks about `(Finset.range (n+1)).filter (...)`
-- Goal still talks about `firstHit ω a h`
-- omega sees these as different opaque variables.
```

Fix: keep the hypothesis at the level of the goal's terms, and extract the
needed numeric facts via cleaner predicates.

### Multiple `set` calls in a proof passed to `omega`

`set` introduces local aliases, but their definitional unfolding is
fragile under tactics that work with hypothesis context. If a proof needs
to compare two terms that are *definitionally equal* via a `set` alias,
write out the terms explicitly rather than relying on the aliases.

### Over-folding small lemmas

The temptation when refactoring is to fold small modules into parent
files. This can hurt clarity when the small module names a distinct
principle. `BlackScholes/StrikeConvexity.lean` was *not* folded into
`StrikeGreeks.lean` despite their proximity — because K-convexity is a
*principle*, while strike Greeks are *computations*. Naming wins out
over collocation.

Conversely, the original Phase-13 modules (Quanto, CDS, etc.) *were*
folded into their parents because each was a one-shot algebraic check, not
a principle.

Rule: fold when the file is one algebraic check. Don't fold when the file
names a principle that downstream code cites.

### Wrapper lemmas around single Mathlib calls

Don't write a thin finance-specific wrapper around one Mathlib lemma. The
wrapper adds a layer of name lookup with zero structural content.

Anti-example (deleted):

```lean
-- DON'T: `pointwiseConvexCombination_eq` was a 4-line wrapper that
-- restated `ConvexOn.smul` with finance variable names. Consumers should
-- just call `ConvexOn.smul` directly.
```

Rule: if your "lemma" is `:= someMathlibLemma` with renamed arguments,
delete it and have the caller invoke the Mathlib lemma directly. The
exception is the *principle module* pattern (above), where a structural
fact is named even though its proof is short.

## Structural-reduction patterns (Phase 24+ batch)

### "This thing IS already that thing under variable renaming"

The cleanest closed-form proofs of recent phases share one shape: showing
that a seemingly-new construction is *literally* an instance of an existing
result at a different parameterisation, after which the new result is a
zero-line corollary of the old.

Phase 24 — **PowerCall**: `(S_T)^a` viewed as a standard BS terminal at
*effective spot* `S_0^a · exp((a−1)rT + a(a−1)/2 · σ²T)` and *effective
volatility* `aσ`. Then `e^{−rT} · E[max((S_T)^a − K, 0)] =
bs_call_formula(Š_0, K, r, aσ, T)` whole — no new gaussian integral.

Phase 25 — **ChooserComposition**: `chooserPrice =
bsV(K, T) + bsP(K · e^{−r(T−t_1)}, t_1)` falls out of pointwise PCP at
the chooser date + linearity of expectation. The chooser is *literally*
a portfolio of call + adjusted-strike put.

Phase 27 — **KMVMertonStructural**: KMV's `kmvPD` is *the same probability*
as the BS `bsd2`-form `Q(V_T > F)`. The pre-existing algebraic identity
`1 − kmvPD = Φ(bsd2)` is upgraded to actual probability content via
`riskNeutralProb_S_T_gt_K`.

Pattern: when a new closed form sits in front of you, before reaching for
new gaussian integration, ask "what existing closed form is this an
instance of?" If the answer is "BS-call at a different parameterisation,"
the proof reduces to algebraic identification + reuse.

This is the same discipline as the principle modules (the consumer of a
principle is its instance), one level finer-grained: each *new* closed
form ought to be an instance of an *old* one whenever the algebra allows.

### Factorisation as the bridge between calculus and algebra

When proving `HasDerivAt f f' x` for `f` of polynomial form, factorise
both `f` and `f'` aggressively before reaching for `convert` or
`linear_combination`. The proofs collapse when Lean can match the factored
forms term-by-term.

Used in `DurationSensitivity.lean` (`hasDerivAt_coupon_term`):
the per-cashflow derivative `d/dy [c / (1+y)^n] = −n c / (1+y)^{n+1}`
bundles the `n = 0` and `n ≥ 1` cases by `field_simp + ring` *after*
factoring out the common `c / (1+y)^{n+1}`. Without factoring, ring
hits a polynomial-degree blowup; with factoring, it's one line.

Same shape in `ConvexitySensitivity.lean` (`hasDerivAt_modNum_term`):
the second derivative is the first derivative applied a second time, with
factored intermediates.

Rule: aggressive `field_simp` *before* `ring`; `push_cast` *before*
`field_simp` if there are `Nat.cast` numerals.

## Workflow additions

### Push to completion when ~80% done

Mid-derivation stopping points are expensive: the proof state is in your
head but not on disk. If you're 80% through a multi-step derivation and
the remaining 20% is mostly algebra-chasing, push to completion rather
than leave a `sorry` for "later." Future-you opening the file cold has to
re-load the entire proof context, which usually costs more than just
finishing in the current session.

Counterexample (don't do this): leaving `sorry` placeholders in
load-bearing files. They block downstream consumers and pollute
`#print axioms`. Use `sorry` only in scratch / exploratory files that
won't be imported.

### Cleanup pass after every major proof

After landing a multi-hundred-line proof, do a structural −10–20% line
trim before closing the milestone. The first version of a complex proof
tends to over-decompose intermediate steps; the second pass folds them
back together. The discipline keeps the codebase from accreting noise.

Concrete evidence: `proposals/bm-martingales/Martingale.lean` went from
392 → 292 lines (−25%) as a single cleanup commit after the proof
mechanics landed.

### Match domain choice to target benchmark FIRST

When formalising an upstream-targeted result, decide the domain / index
type / Lp exponent based on what the *target benchmark* expects, *before*
writing the supporting infrastructure. Choosing first and writing second
saves a refactor pass.

Concrete evidence: the L^p continuous-martingale-convergence work shipped
with `p : ℝ`-indexed `eLpNorm` because that's what `Mathlib.MeasureTheory`
takes. An earlier version with `p : ℕ≥1` had to be rewritten.

## Upgrade-properly patterns (2026-06-04 batch)

Patterns from the Path-1 session that converted seven reduced cores to full
derivations (optional sampling inequality, covariance-PSD, Rockafellar–Uryasev,
Newton convergence, KMV survival, the American/Snell pair).

### Pointwise-certificate minimality

To prove a variational characterization `m = min_c g(c)` — attained at `c*` —
hunt for a *pointwise* inequality whose integral collapses to `m` for *every*
`c`, with equality exactly at `c*`. No calculus, no convexity machinery, no
derivative of the objective.

Concrete: Rockafellar–Uryasev (`RiskMeasures/RockafellarUryasev.lean`). The
certificate is `(L − c)⁺ ≥ (L − c)·𝟙_{Z > z}` (the `α`-tail event); integrating
against the Gaussian density gives `g(c) ≥ CVaR` in three integral evaluations,
and at `c = VaR` the positive part vanishes exactly off the tail — equality.
The certificate *is* the reason the minimum sits at VaR; a `deriv`-based proof
would hide it.

### Linearization-subtracted integral remainder

Second-order Taylor control from *first-order* tools, at the sharp constant:
to bound `f y − f x − f'(x)(y − x)`, apply the FTC
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) to the auxiliary
`g w := f w − f'(x)·w` on the segment — its derivative is `f' w − f'(x)`,
which a Lipschitz hypothesis on `f'` bounds by `L·|w − x|`, *linear* in the
distance to `x`. Integrating the linear bound gives `(L/2)·|y − x|²` — the
sharp Newton–Kantorovich constant — with no `ContDiff`, no `iteratedDeriv`,
no second derivative anywhere. (The uniform mean-value bound
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` proves the same shape
but doubles the constant: the derivative deviation *vanishes at* `x`, and
only the integral sees that.)

Concrete: `newtonStep_quadratic_error` (`BlackScholes/NewtonConvergence.lean`)
— the whole "Newton is quadratic at `L/(2m)`" content is this plus the
error–times–derivative identity `(x⁺ − r)·f'(x) = f'(x)(x − r) − f(x)`.

### Inequality = equality + monotone part (decomposition transport)

To upgrade an *equality* theorem about martingales to the *inequality* version
for submartingales, do not re-run the equality's proof with inequalities
threaded through. Doob-decompose `f = M + A`, transport the equality on `M`
(Mathlib's theorem, consumed as-is), prove the compensator `A` monotone
(its increments are `μ[f_{k+1} − f_k | ℱ_k] ≥ 0` — literally the submartingale
property), and recombine with `condExp_mono`.

Concrete: `submartingale_optional_sampling`
(`Foundations/OptionalSamplingInequality.lean`) = Mathlib's
`Martingale.stoppedValue_ae_eq_condExp_of_le` + `predictablePart` monotonicity.
The decomposition is the *conceptual* picture, and the proof is exactly it.

### Identification theorems ground scalar recursions in path space

When the library holds a scalar/Markov recursion (a function of the current
state) and the textbook theorem is about an adapted *process* on paths, do not
rebuild the scalar layer. Build the path-space object abstractly, prove its
clauses there (dominance, supermartingale, adaptedness, minimality), then prove
ONE induction — the identification `scalar recursion = discounted path object`
— and every clause transports to the scalar object for free.

Concrete: `snellAux_eq_discounted_americanPrice`
(`Binomial/SnellEnvelope.lean`): `snell q Z N k ω = e^{−rk}·americanPrice
(N−k) (S_k ω)`. Four abstract Snell clauses + one induction = the genuine
supermartingale/intrinsic statements about `americanPrice`, with the
node-average conditional expectation made explicit. Same instrument as the
"this IS already that" structural reduction, but for *recursions* rather than
single formulas.

## In-Lean automation: `grind` (2026-06-06 batch)

Empirical trial of the core `grind` tactic (in toolchain since 4.22; we are
on 4.30) against 17 goals extracted verbatim from MathFin proof sites. The
boundary is sharp and worth internalizing.

### Where grind wins — make it the first call

8/10 in its lane, including goals our current proofs work harder for:

* **Field identities with `≠ 0` side conditions** — the full risk-parity
  contribution identity (`Portfolio/RiskParity.lean`) closes by bare `grind`,
  *including the un-normalized form with commuted denominators*
  (`σ₁ + σ₂` and `σ₂ + σ₁` mixed) that forces a manual
  `rw [show σ₂ + σ₁ = σ₁ + σ₂ from by ring]` before `field_simp; ring`.
  Congruence closure absorbs the commutation; the denominator non-vanishing
  is consumed from the hypothesis.
* **Division goals with ℕ-cast denominators** — the telescoping increment
  `(k+1)·t/(n+1) − k·t/(n+1) = t/(n+1)` closes with *no* explicit
  `(n:ℝ) + 1 ≠ 0` hypothesis: grind derives it from cast nonnegativity.
* **Goals linear in nonlinear atoms** — `1 − cos u = 2·sin(u/2)²` from the
  double-angle + Pythagorean hypotheses (atoms `cos u`, `sin(u/2)²`,
  `cos(u/2)²` enter linearly). Our proof used `nlinarith [h2, h3]`; grind
  needs no hints.
* **ℕ arithmetic** (truncated subtraction, cast pushing) — subsumes `omega`
  via cutsat.

### Where grind loses — keep nlinarith

0/7 on nonlinear *real inequalities* (power-mean `(e+f+g)² ≤ 3(e²+f²+g²)`,
`w² ≤ w` on `[0,1]`, `t² ≤ 4s²` from `t/2 < s`, products of hypotheses like
`a ≤ b → 0 ≤ z → az ≤ bz`). This is exactly the FRO's in-progress Year-3
nonlinear-arithmetic workstream — re-test on future toolchain bumps.

Passing the nlinarith certificates as grind parameters
(`grind [sq_nonneg (e - f), …]`) recovers *some* of these (the power-mean
closes), but fails where nlinarith multiplies hypotheses *together*
(`w² ≤ w` needs `w·(1−w) ≥ 0`, a product of `h0` and `h1` — grind does not
search hypothesis products). Hint-for-hint, nlinarith remains strictly
stronger on this class.

### Trap

The `unusedVariables` linter false-positives on binders consumed only inside
grind-generated proof terms (a `≠ 0` hypothesis the proof genuinely needs gets
flagged unused). Kernel-checked soundness is unaffected; don't "fix" the
warning by deleting the hypothesis — the proof breaks.

Authoring order going forward: `grind` → (if nonlinear-inequality shaped)
`nlinarith [certificates]` → `positivity`/`gcongr`/`bound` for the structured
inequality families.

## Canonical forms (2026-06-09, values round 6)

**Discount-factor exponent**: in NEW files write `Real.exp (-(r * τ))` —
the parenthesised product under one negation, the repo's 2:1 majority form.
`Call.lean`-era `Real.exp (-r * T)` is grandfathered: the realized cost of
the split is exactly three `neg_mul` reconciliations at the bridges
(`PDEFromFeynmanKac` ×2, `MertonJumpDiffusion` ×1), accepted permanently in
round 6 — a unifying sweep would re-stale a large ledger slice for zero
mathematical content.

## Mathlib house-style golf (2026-07-10, BM PR #484 maintainer review)

Distilled from a BrownianMotion maintainer's review of our upstream PR #484
(`isStoppingTime_tauMeshLift` + `tendsto_iSup_setIntegral_tauMesh_zero` in
`DoobMeyer.lean`). The review was ALL idiomatic golf plus one architectural
lift — no math errors — so it reads as the repo's binding house style. Every
item was verified compiling at the v4.31.0 pin. These map directly onto our own
zero-slop / idiomatic-register / coherence / concept-clarity lenses; adopt them
in MathFin proofs too, not just upstream contributions.

### The golf checklist (most transferable first)

1. **Bare proof term over `by exact` / `by exact_mod_cast`.** If `h : A` and the
   goal is defeq to `A`, pass `h`. A subtype `mesh ι n = {x : ι // x ∈ …}` has
   `v ≤ u` *defeq* to `(↑v : ι) ≤ ↑u`, so `le_trans hv hu` needs no cast. A stray
   `exact_mod_cast` usually masks an already-defeq coercion.
2. **Let Lean insert coercions; never hand-write them.** `WithTop ι`,
   subtype→base, `ℝ≥0 → ℝ`, `⊥`/`⊤` coercions elaborate from context in `≤`,
   set-builder, and argument position: `{ω | f ω ≤ (s : WithTop ι)}` → `… ≤ s`;
   `fun c => (c : ℝ) / 2` → `fun c => c / 2`; `fun u => ((u : ι) ≤ s)` →
   `fun u => u ≤ s`.
3. **Bind ∀-vars in the `have` signature, not via `intro`.**
   `have h (v : T) : P v := by …` beats `have h : ∀ v, P v := by intro v; …`.
4. **Fold `have h := e; simp … at h; exact h` into `simpa … using e`.**
5. **No gratuitous `classical`.** `LinearOrder ι` already gives `DecidableLE`, so
   `Finset.univ.filter (· ≤ s)` needs none. Reach for it only for a genuinely
   nonconstructive `Decidable`/choice.
6. **`set x := e with hx` only if you rewrite with `hx`.** To merely unfold `x`
   inside the proof, drop `with hx` and use `simp [x]` (the local def is
   simp-usable). Fewer named artifacts; often deletes a helper `have` outright.
7. **Minimal typeclass, matching neighbours.** Don't assume `IsFiniteMeasure`
   when the callees need only `SigmaFiniteFiltration`; check each dependency's
   actual requirement. Instance implications
   (`[IsFiniteMeasure μ] → SigmaFiniteFiltration μ 𝓕`) mean weakening a lemma
   never breaks a stronger-hypothesis caller. Over-assuming is a coherence smell.
8. **Fewer `have`s; mix forward + backward reasoning** (`suffices`,
   `show … from`, `simp`/`simpa`) so the argument's SHAPE stays visible. A long
   ladder of `have`s hides structure. (Balance against concept-clarity — don't
   over-golf past readability.)
9. **Lift the reusable abstraction; don't tailor the proof to one call site.**
   The review's headline. Extract the bespoke ε–δ core into a general,
   Mathlib-worthy lemma
   (`UniformIntegrable.eLpNorm_tendsto_zero_of_iSup_measure_tendsto_zero`), prove
   it once, apply it. Work out the honest side-conditions — here just
   measurability of the sets: because the lemma consumes `UniformIntegrable X p μ`
   directly it inherits any `p` (the `ε = ∞` case falls to `le_top`), so despite
   the reviewer's hint NO `p ≠ ∞` is needed. This is our anti-wrapper /
   consume-the-idiomatic-lemma value aimed at our own code.
10. **Delete parens the parser doesn't need.**
11. **`↦` over `=>` in `fun` and binders** (a leanprover-community style-guide
    rule). Keep a single declaration internally consistent; the file at large
    mixes the two.
12. **Collapse a trivial two-step `calc` into one term.** A `calc` whose second
    step is just an equality (`… ≤ x := h; _ = y := heq`) is `h.trans_eq heq`
    (or `.trans`) — drop the `calc` entirely. If a `calc` genuinely stays, the
    `calc` keyword goes on its own line when the head term/relation wraps.
13. **Squeeze, don't ε–δ, for `Tendsto _ _ (𝓝 0)`.** A hand-rolled
    `rw [ENNReal.tendsto_nhds_zero]; intro ε …; filter_upwards …` collapses to
    `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ ↦ zero_le) …` once you have an eventual upper
    bound that itself → 0 — e.g. `C / ENNReal.ofReal (b c)` via
    `ENNReal.tendsto_ofReal_atTop` + `ENNReal.Tendsto.const_div`. The squeeze
    reads as the actual argument (`0 ≤ ⨆ ≤ C/(b c) → 0`).

### Local-build gotchas hit while verifying (transferable)

- `set x := e` (no `with`) makes `x` opaque to `simpa [T] using <term>` when the
  term mentions `e` unfolded — `simp [T]` rewrote `T` *inside* `T.max'`, so
  `↑({…}.max')` no longer matched the goal's folded `↑x`. Fix: bind `x ∈ T` first
  (`have hu_mem : u ∈ T := T.max'_mem hTne`), THEN `simpa [T]` unfolds only the
  filter, leaving `x` intact.
- `ae_all_iff.2 fun t => ht t` needs the index type pinned, or Lean infers it as
  the uncountable base `ι` → `Countable ι` synthesis failure. Ascribe the BINDER —
  `ae_all_iff.2 fun t : mesh ι k ↦ ht t` — which then inlines straight into
  `filter_upwards [...]` with no separate `have : ∀ᵐ ω, ∀ t : mesh ι k, …`.
- `UniformIntegrable` is a `def` reducing to `And`, so `hd.myLemma` dot-notation
  resolves against `And` (`invalidField`). Call `UniformIntegrable.myLemma hd …`
  by full name; positional field access `hd.2.1` for the `UnifIntegrable`
  component is fine.
- `hv.trans h` (dot notation) FAILS where `le_trans hv h` succeeds when the middle
  term needs a subtype→base coercion: dot resolves `.trans` against `hv`'s type
  (`mesh ι n`), pinning the middle to `mesh ι n` and refusing `↑u : ι`. Use the
  `le_trans` / `_root_.`-qualified form so the expected type drives the coercion.
  This is the flip side of item 1 — the coercion IS defeq, but only when
  elaboration is expected-type-driven, which dot notation defeats.
- Deleting a declaration ORPHANS its preceding `omit …/include …/attribute … in`
  modifier onto the NEXT declaration. If that next declaration is a `variable (…)`,
  the modifier silently breaks the variable's registration, so under `lake build`
  (`autoImplicit` false) every later use of that variable is an "Unknown identifier"
  — a whole-file cascade from one root cause. The warm daemon (`autoImplicit` TRUE)
  MASKS it. When deleting a lemma, check the line above for an `omit … in` and
  delete it too. (2026-07-10: hoisting a lemma out of `GirsanovAdaptedTheta` orphaned
  its `omit` onto `variable (hB …)` → 60+ `hB`-unknown errors.)
- `have h := e; simp only [L] at h; exact h` does NOT always fold to
  `simpa only [L] using e`. When `exact h` was closing by full defeq — instance-path
  differences (`HasDerivAt.const_mul` producing the `NormedAlgebra` path vs the
  goal's plain `AddCommGroup`), or `id` unfolding — `simpa`'s weaker post-simp
  matching fails with a type mismatch. Build-verify every simpa-fold; the daemon's
  `lean-check` can pass one that `lake build` later rejects.

## Provenance header for source-consulted proofs

When a proof is developed with an external formalization or textbook as a *source*
(not a template — our design and Mathlib idiom lead; see the values doctrine), the file
carries an attribution block in its copyright header and the benchmark entry a machine-checkable
provenance marker, so the "our design, source consulted" claim is honest and cannot drift.

- **File header** (after `Authors:`), e.g. `MathFin/Actuarial/SurvivalModel.lean`:
  > The definitions and proofs here are our own, following this library's conventions … `<Source>`
  > … was consulted as a source for the classical result set, and is cited here with thanks and
  > with the author's kind permission.

  State the design as OURS; cite the source with its license and (where applicable) the author's
  permission. Never "Mathematical design © <them>" or "translated/re-formalized from".
- **Benchmark entry**: `metadata.provenance.source: "<slug>"` (e.g. `afp-actuarial-mathematics`),
  optionally `issue` + `upstream`. `tools/formalization_yaml.py` counts these per source and emits a
  mechanical disclosure ("N proof(s) authored in our own design, with … consulted as a source and
  cited"); `tests/test_formalization_yaml.py` pins the count so it tracks the live corpus.
- **coverage.md**: one disclosure line per source-consulted batch.

## Continuous-time FTAP / conditional-expectation idioms (2026-07-11 batch)

Distilled from the continuous first-FTAP frame (`Foundations/ContinuousMarket.lean`).

### Bilinear `condExp` pull-out for predictable-weighted martingale increments
The building block of the forward FTAP — "a `𝓕_s`-measurable bounded weight against a martingale
increment integrates to `0`" — is Mathlib's **`condExp_bilin_of_stronglyMeasurable_left`**
(`Mathlib/MeasureTheory/Function/ConditionalExpectation/PullOut.lean`):
`Q[fun ω ↦ B (φ ω) (g ω) | m] =ᵐ fun ω ↦ B (φ ω) (Q[g | m] ω)` for `φ` `m`-strongly-measurable.
- `B` must be a **continuous** bilinear map `F →L[ℝ] E →L[ℝ] G`. For the real inner product use
  **`innerSL ℝ`** (`⟪·,·⟫_ℝ`), NOT `innerₗ` (that is only `→ₗ`, and the pull-out needs `→L`).
- Then `∫ ⟪φ, Δ⟫ dQ = ∫ Q[⟪φ,Δ⟫|𝓕_s] dQ` (`integral_condExp`) `= ∫ ⟪φ, Q[Δ|𝓕_s]⟫ dQ` (pull-out
  under `integral_congr_ae`) `= 0`, since `Q[S t − S s | 𝓕 s] = 0` for a martingale.
- Increment integrability: Cauchy–Schwarz `‖⟪φ,Δ⟫‖ ≤ ‖φ‖·‖Δ‖ ≤ K·‖Δ‖` + `Integrable.mono'` with
  `AEStronglyMeasurable.inner`; `Martingale.integrable i` gives `Integrable (S i) Q`.

### `Martingale` is a bare `And` on this pin — `.1`/`.2`, and `.adapted` does NOT exist
`Martingale f 𝓕 μ := StronglyAdapted 𝓕 f ∧ ∀ i j, i ≤ j → μ[f j | 𝓕 i] =ᵐ[μ] f i`. So:
- adaptedness is **`hS.1 i : StronglyMeasurable[𝓕 i] (f i)`** (via the `And`) — `hS.adapted` errors
  with `And.adapted` (mirrors the `UniformIntegrable`-is-a-`def` gotcha above);
- the tower is **`hS.2 i j hij`**; the named lemmas `Martingale.condExp_ae_eq` and
  `Martingale.integrable` DO exist and are fine to use by dot notation.

### Sub-namespace variant frames — and the build gate, not the daemon, catches the collision
`MathFin.IsEMM` already exists (`FTAPDiscrete`). A second `IsEMM` under bare `namespace MathFin`
collides. Variant frames sub-namespace: `MathFin.OnePeriod`, `MathFin.OnePeriodVector`, and now
`MathFin.ContinuousMarket`. The isolated warm-daemon `lean-check` PASSES (it never loads the sibling
module), so only `lake build MathFin` (the umbrella) surfaces
`environment already contains 'MathFin.IsEMM'`. One more entry in the daemon-masks / build-verifies
column: name collisions join `autoImplicit` and instance-path `simpa`-folds there.

### Lift the shared *vanishing* primitive, let each setting supply its own zero-integral
When two forward-FTAP settings both close through "nonneg + `∫ = 0` ⟹ positive set is null,"
extract exactly THAT (`ae_zero_of_nonneg_of_integral_zero`, `Foundations/NoArbitrageCore.lean`) and
let each side reach `∫ = 0` its own way — the discrete one via a martingale transform started at `0`
(`∫ V_T = ∫ V_0 = 0`), the continuous one term-by-term via the pull-out. Do NOT force a
martingale-shaped shared lemma onto the continuous setting, which has no martingale to hand: that
was the plan's first cut, and it produced an over-general core whose docstring overclaimed its
consumers. Match the abstraction to what is actually shared.

### CI runs `lake lint`, `lake build MathFin` does NOT (docBlame on struct data fields)
A green local `lake build MathFin` can still push RED: CI (`build.yml` via `lean-action`) also runs
`lake lint` (Batteries `runLinter` over `MathFin`), the same env-linters Mathlib uses. The common
new-`structure` catch is **`docBlame`: every non-`Prop` DATA field needs a `/-- … -/` docstring**
(`SimpleStrategy`'s `N`/`time`/`hold` failed; the `Prop` fields `mono`/`meas`/`bdd` and the `Prop`
structure `IsEMM` are exempt). Run `lake build MathFin && lake lint` (daemon DOWN) before pushing —
and REBUILD first: `runLinter` reads the olean's doc metadata, so linting after only a docstring
edit lints the stale olean and re-reports the old failures at the old line numbers.

### Small syntax pointers
- `Fin.castSucc_lt_succ` takes `i` **implicit** — `(Fin.castSucc_lt_succ (i := i)).le`, or let it
  unify; do NOT apply it to `i` positionally (`... i` → "function expected").
- `condExp_of_stronglyMeasurable hm hf hint : Q[f | m] = f` is a real **`=`**, not `=ᵐ`; use it in
  `rw`, or lift with `.symm ▸` where an `=ᵐ` is expected.
- `integrable_finsetSum` / `integral_finsetSum` are the current spellings; the `_finset_sum` forms
  are deprecated (the daemon is silent, `lake build` warns — fix on sight, zero-slop).

## Market-making Riccati / calculus idioms (2026-07-16 batch)

### Mathlib has no `tanh` calculus at this pin (v4.31.0)
- `loogle 'Real.tanh, HasDerivAt'` → **0 results**; `Real.deriv_tanh` absent. Derive it:
  `hasDerivAt_tanh x : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x` from `Real.tanh_eq_sinh_div_cosh`
  + `HasDerivAt.div` (`sinh`/`cosh`, `cosh x ≠ 0` via `Real.cosh_pos`). The `tanh → 1` limit at `atTop`
  is also absent — defer it (or build via `tanh x = 1 - 2/(exp(2x)+1)`) if it isn't on the critical path.
- `HasDerivAt.div` yields the function as **`sinh / cosh` (Pi-div), not `fun y => sinh y / cosh y`**, and
  `Real.tanh`'s defeq to `sinh/cosh` is **not exposed for `exact`** — rewrite the goal's *value* to the
  div-form, rewrite the head with `funext … Real.tanh_eq_sinh_div_cosh`, then `field_simp; ring`.

### `HasDerivAt` combinators build Pi-level functions — annotate to collapse `convert`
- `hA.neg.mul_const c`, `.sub`, … produce `((-A) * c - B) - C` (Pi `Sub`/`Neg`), NOT a single `fun s => …`.
  So `convert h using 1` against a `fun s => …` goal leaves a spurious **function-equality** subgoal, and
  `field_simp`/`ring` then report **"made no progress"** (they're staring at a function goal, not an equation).
  Fix: give the `have` the single-lambda **type annotation** (defeq to the combinator term via `Pi.sub`/`Pi.neg`
  unfolding) so `convert … using 1` leaves ONLY the derivative-value goal. Diagnose a stuck `convert` with
  `exact h` — the type-mismatch prints both the combinator's Pi-form and the target lambda.

### Polynomial identity with `1/(2z)`: `field_simp` needs a beta-reduced goal + nonzero facts
- `ring` alone can't cancel `z²/(2z) = z/2` (no `z ≠ 0`); `field_simp` must clear it first, and it also needs
  `z ≠ 0` / `2*z ≠ 0` in context and no `(fun y => …) x` residue. The `field_simp; ring` closure of such a
  verification **self-certifies** hand-derived coefficients — a wrong sign/coefficient fails `ring`, so a green
  build IS the check (used for the market-making `B`/`C` ODE right-hand sides).

### `axiom_audit_gen` pins `:= MathFin.X` re-export HEADS only
- A benchmark proved by an anonymous constructor `:= ⟨MathFin.a …, MathFin.b …⟩` gets **none** of its cited
  constants auto-pinned (the gen matches `:=\s*\(*\s*MathFin\.…`). Fine when they're trivial + ledger-covered;
  add to the curated `AxiomAudit.lean` if you want them pinned.

### ★ Review subagents must NOT touch the daemon
- A review subagent that runs `./scripts/lean-check.sh` / `docker` will bring the lean-repl daemon up **and tear
  it back down**, killing the controller's warmed daemon. Instruct review subagents to **read files only — never
  run docker/lake/lean-check**. (Cost a daemon restart mid-run.)

## Matrix Riccati via spectral reduction (2026-07-16, multi-asset follow-on)

The matrix analogue of `a(t) = Â·tanh(Â(T−t))` (BEGV Prop. 2, `MatrixMarketMakingRiccati.lean`), with
**no matrix `tanh`/`exp`** (both absent at the pin) and **no Mathlib matrix-differentiation** (also absent).

### Spectral reduction — define diagonalised, reduce the ODE per eigenvalue
- For Hermitian `Â = U·diag(λ)·Uᴴ` (`U = hÂ.eigenvectorUnitary`, `λ = hÂ.eigenvalues`), **define** the matrix
  function as `U · diagonal (fun i => <scalar closed form> (λ i)) · star U`. Then the matrix ODE reduces, on each
  eigenvalue, to the already-proven *scalar* lemma. No matrix transcendental is ever built.
- `Matrix.IsHermitian.spectral_theorem` at this pin is stated via `conjStarAlgAut` (namespace **`Unitary`**):
  `A = Unitary.conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))`, and
  `Unitary.conjStarAlgAut_apply` is `@[simp] rfl`: `u * x * star u`.
- `conjStarAlgAut U` is a `⋆`-alg hom ⇒ **`map_mul`** collapses conjugated products with zero `star U*U=1`
  juggling: `Â*Â = U·diag(λ)·star U · U·diag(λ)·star U = U·diag(λ²)·star U` via
  `conv_lhs => rw [hÂ.spectral_theorem]; rw [← map_mul, diagonal_mul_diagonal, Unitary.conjStarAlgAut_apply]`.
  (Over ℝ, `RCLike.ofReal ∘ λ` cleans up with `simp [Function.comp, sq]`.)

### Matrix-valued `HasDerivAt` — open the operator norm, lift `diagonalLinearMap`
- Mathlib has **no** `HasDerivAt` for matrix-valued maps and **no default** norm on `Matrix` (diamond avoidance).
  `open scoped Matrix.Norms.Operator` (the `L∞` operator norm — `NormedRing` + `NormedAlgebra`) turns
  `HasDerivAt.const_mul U`, `.mul_const (star U)`, `.const_smul c` on matrices on. The operator-norm
  `AddCommGroup` is **defeq** to the default `Matrix.addCommGroup`, so a goal stated with the default instance is
  closed by `exact` (not `simpa`) after the derivative is built.
- Diagonal-core derivative: `hasDerivAt_pi.2 (fun i => <scalar deriv>)` for the Pi part, then lift through
  `(Matrix.diagonalLinearMap (R:=ℝ) (n:=n) (α:=ℝ)).toContinuousLinearMap.hasFDerivAt (x := g t)`
  `|>.comp_hasDerivAt t hpi`, close with `simp only [Function.comp_def]; exact`. (`ContinuousLinearMap.hasFDerivAt`
  needs its point `x` supplied — bind it to `g t`.)
- Conjugation-preserves-Hermitian: `isHermitian_mul_mul_conjTranspose B hA : (B·A·Bᴴ).IsHermitian`, with
  `isHermitian_diagonal` (real ⇒ `TrivialStar`) and `star M = Mᴴ` via `star_eq_conjTranspose`.

### Change-of-variables / positive-diagonal collapses (M2)
- `diagonal (√dᵢ)⁻¹ * diagonal (√dᵢ) = 1`: `diagonal_mul_diagonal` + `inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (hd i))`
  + `diagonal_one`. For `D₊^{-½}·D₊·D₊^{-½}=1` the funext goal after `field_simp` is `d i = √(d i) ^ 2` → close
  with **`Real.sq_sqrt (hd i).le`** (not `Real.mul_self_sqrt`, which is `√·√`).
- Reassociate a sandwiched product `(Dm·a·Dm)·X·(Dm·a·Dm) = Dm·a·(Dm·X·Dm)·a·Dm` with `simp only [Matrix.mul_assoc]`
  (both sides normalise to the same right-associated factor sequence), then collapse the centre with the `=1` lemma.
- **ℕ vs ℝ smul**: a bare `2 • M` defaults to **ℕ**-smul, which `smul_smul` (single scalar action) can't fuse with
  a `(1/2 : ℝ) •`. Write `(2 : ℝ) •` in the statement when the proof does smul algebra.
- `pow_two` bridges `x*x` (from `diagonal_mul_diagonal`) and `x^2` inside a `diagonal (fun i => …)` equality —
  `simp only [pow_two]` makes both sides identical, avoiding a `ring` on the post-`congr` shape (which emits a
  spurious noncommutative "Try this: ring_nf" **info** even though the build is kernel-valid).
- **`Σ` is a reserved token** (Sigma types) — never an identifier; name the covariance `cov`. (Also [[girsanov]]:
  never capital Σ in idents.)

## Extending an isometry to an `L²` closure — `extendOfNorm` into a submodule (2026-07-18 batch)

From the Itô–Lévy integral CLM (`Foundations/PoissonCompensatedIntegralOperator`): building
`f.extendOfNorm e : Eₗ →L F` where the dense domain `Eₗ` is a *submodule* of the ambient `L²`, not a
full space. The continuous Itô CLM dodged this by making its codomain a full `Lp` of a bespoke
trimmed measure; when you instead extend to a `Submodule.topologicalClosure`, these are the traps.

### Target-as-closure makes density soft — no bespoke `σ`-algebra
- To extend `emb : E →ₗ Lp` by continuity you need `DenseRange`. Rather than characterise which `L²`
  functions are hit (a from-scratch predictable `σ`-algebra), **define the target as the closure of
  the range**: `levyClosure := (LinearMap.range emb).topologicalClosure`, `embCorestrict :=
  emb.codRestrict levyClosure (fun V => Submodule.le_topologicalClosure _ (mem_range_self _ V))`.
- `DenseRange embCorestrict` is then a *soft* topological fact: `Topology.IsInducing.subtypeVal.dense_iff`
  reduces it to `↑x ∈ closure (Subtype.val '' range embCorestrict)`; the image is `↑(range emb)`
  (`← Set.range_comp; rfl`), whose closure is `↑levyClosure` **by construction**
  (`← LinearMap.coe_range, ← Submodule.topologicalClosure_coe`), and `x.2` finishes. No induction, no
  `σ`-algebra.
- v4.31.0 names (loogle misses several — the `Inducing→IsInducing` rename put them under `Topology`):
  `Topology.IsInducing` / `.subtypeVal` / `.dense_iff`, `Submodule.topologicalClosure_coe`
  (`↑s.topologicalClosure = closure ↑s`), `LinearMap.coe_range` (NOT `range_coe`),
  `Submodule.coe_norm` (`‖x‖ = ‖↑x‖`, a `rfl` `simp` lemma), `Submodule.le_topologicalClosure` (takes
  the submodule explicitly), `denseRange_inclusion_iff`.

### ★ The submodule-codomain instance diamond (and how to bridge it)
- `extendOfNorm` needs `[SeminormedAddCommGroup Eₗ]`, which derives `Eₗ`'s `AddCommMonoid` via the
  **`AddCommGroup`** path; a bare `_ →ₗ[ℝ] ↥sub` picks `Submodule.addCommMonoid` (the semiring path).
  On `↥(Submodule …)` these are defeq (the norm/module instances would not typecheck otherwise) but
  **not at the transparency the elaborator uses for the explicit `LinearMap` `AddCommMonoid` argument**
  → a bare `f.extendOfNorm e` fails with an "application type mismatch" on the `AddCommMonoid` slot.
  `set_option backward.isDefEq.respectTransparency false` does **not** help.
- **Bridge for a `def`**: state it as a tactic block and let the *goal type* pin the instances —
  `refine LinearMap.extendOfNorm (E := ↥Src) (F := Cod) f ?_; exact e`. The CLM goal
  `Eₗ →L[ℝ] F` fixes `Eₗ = ↥levyClosure` with its seminormed-group instances, so `exact e` is a single
  cheap `isDefEq` at default transparency. (`f.extendOfNorm (by exact e)` alone is "stuck, goal has
  metavariables" — `E` isn't pinned yet inside the argument.)
- **Bridge for the downstream norm lemma**: `unfold <thedef>` to expose the def's *already-bridged*
  `extendOfNorm` term, then `exact norm_extendOfNorm_eq_of_isometry hdense key H` — but the lemma app
  re-triggers the diamond `whnf`, which is heavy-but-**finite** (~50 s), so wrap the theorem in
  `set_option maxHeartbeats 1000000 in`. `key : ∀ V, ‖f V‖ = ‖e V‖` via `rw [Submodule.coe_norm]`
  (drop the subtype norm to the ambient one) `; exact <the isometry on the dense range>`.

### Workflow: relocating a lemma restales its whole transitive importer set
- The jump tower must not import `WienerIntegral` (it pulls in `BrownianMotion`), so the shared kernel
  `norm_extendOfNorm_eq_of_isometry` was lifted into a new `Mathlib`-only leaf
  `Foundations/ExtendOfNormIsometry.lean`, re-imported (and re-exported) by `WienerIntegral` and
  imported by the operator file. **Cost**: changing `WienerIntegral`'s *source* restaled **every**
  ledger entry that transitively imports it (the whole Itô/finance chain — 36 entries, a ~50-min
  daemon `ledger verify`). Lift-to-a-shared-leaf is the right call for a genuinely generic kernel, but
  budget the re-verify; if the tree is hot and the lemma is one-off, keeping it local is cheaper.

## Statement design (for the formalizer / drafter) (2026-07-18)

The drafter's job is a faithful, in-depth *statement* — the hardest failures are
not proof failures but statement failures. Design for these before writing `:= by
sorry`.

- **Shape hard side-conditions to be inherited, not asserted.** When the object is
  a limit/closure, define it inside a class closed under the operation so the
  condition is free: `levyClosure := (LinearMap.range emb).topologicalClosure` makes
  `DenseRange` a soft `IsInducing.subtypeVal.dense_iff` fact — no bespoke σ-algebra.
  Carve a `Submodule` (carrier + three closure proofs) rather than a `structure` +
  `Module` instance. Diagonalize a matrix problem so the ODE reduces to the scalar
  lemma. A draft that instead *asserts* the side-condition as a new hypothesis is
  the wrong shape.
- **Casts go outward around lattice/arith ops** to match library normal form:
  `↑(min p t)`, not `min ↑p ↑t` — a coe-inward statement fails to unify downstream,
  and a co-occurring "stuck metavariable" is a *symptom* of the cast mismatch, not a
  separate problem. Fix the cast, not the instance.
- **Name derived measures/σ-algebras** (`trimMeasure_T`, a predictable σ-algebra) as
  defs; never inline `(P.trim …)` in a statement — the inlined form carries a
  σ-algebra-instance mismatch the named def avoids.
- **State Lp-class facts in `=ᵐ`/`condExp` form, not pointwise.** For a process whose
  value is an Lp class, honest pointwise `Adapted` is awkward; the conditional-
  expectation identity is the real content and it elaborates.
- **State shared hypotheses in the eta-form the consumers want** (`fun ω ↦ B t ω - B s
  ω`, not Pi-`sub`), so a defeq `exact` propagates instead of a rewrite failing.
- **Don't quantify integrals over `↥Submodule`** — instance synthesis (`BorelSpace
  ↥K`) fails; stay in the ambient space with subset/membership hypotheses.
- **Natural generality** (already in the drafter contract, restated here): `s.Nonempty`
  over a member-witness; `A ≠ 0` over provable positivity; the minimal typeclass the
  callees need.

## Repair table (compiler error → fix) (2026-07-18)

The recurring error→fix mappings from the grind history. Try the mapped fix before
a general search; most are one-line and defeq-driven.

| Error signature | Fix |
|---|---|
| "did not find an occurrence" / "made no progress" with `(fun … ↦ …) x` or a Pi-`+`/`-`/`*` of lambdas in the goal | `show` the beta-reduced goal / `simp only []`; or type-annotate the `have` with the single-lambda form. Diagnose a stuck `convert` with `exact h`. |
| Unknown identifier `X` | grep the **pinned** `.lake/packages/mathlib` for `X` and `Namespace.X` (loogle tracks a newer pin — upper bound only); if a sibling edited this session declares `X`, it's stale-olean: rebuild, don't respell. |
| "typeclass instance problem is stuck `C args ?m.N`" | name the implicit at the call site (`(μ := μ)`), `@`-apply, or bind a fully-typed `have` first. |
| "Function expected at `zero_le` … type `0 ≤ ?m`" | drop the applied argument, use the bare term; toggle the primed/unprimed variant. |
| "unexpected token 'omit'/'set_option'; expected 'lemma'" | move the `… in` modifier **above** the docstring. |
| mass "unknown namespace MeasureTheory" in a file importing a just-edited sibling | stale olean — rebuild the dep; do not edit the proof. |
| Type mismatch of `Measurable`/`AEStronglyMeasurable` differing only in the `MeasurableSpace` instance | drop the explicit type annotation (let it infer the sub-σ), or `letI`-pin it. |
| "Invalid field `f`" on an `And`/`Exists`/def-reducing-to-`And` | call `Namespace.f h …` by full name, or `obtain ⟨…⟩` first. |
| "No goals to be solved" | delete the trailing tactic (cascade after a root error — fix only the first). |
| "Ambiguous term X" (`intervalIntegral` vs `MeasureTheory`) | qualify by the goal's integral syntax. |
| "failed to synthesize `LE Type`/`OfNat Type`" | `ℝ≥0` misparsed as `ℝ ≥ 0` — add `open scoped NNReal`; `𝓝` → `open Topology`. |
| cast mismatch inside a `fun n : ℕ ↦ …` | put the ℕ-consuming atom leftmost, or ascribe the binder; write `(2:ℝ) •`, never `2 •`. |
