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
