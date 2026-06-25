# Design: finite-Ω multi-period FTAP (scalar, NA ⟺ EMM)

- **Date:** 2026-06-24
- **Status:** approved design, pre-implementation
- **Author:** Raphael Coelho
- **Topic:** discrete-time Fundamental Theorem of Asset Pricing, finite probability space, finite horizon, single risky asset.

## 1. Goal

Formalise the **backward direction** of the discrete-time FTAP and package the
**biconditional**

> a finite-Ω, finite-horizon, single-asset market has **no arbitrage** **iff**
> it admits an **equivalent martingale measure (EMM)**.

The forward direction (EMM ⇒ no-arbitrage) already exists abstractly in the
repo; the genuinely-open, headline content is the backward direction
(no-arbitrage ⇒ ∃ EMM) and the assembled biconditional. This is the
**Harrison–Pliska** theorem — the finite-Ω case of Dalang–Morton–Willinger —
which appears to be unformalised in Lean (Echenim's Isabelle line is
replication-based, not the NA⟺EMM separating-hyperplane characterisation).

## 2. Scope — locked decisions

- **Rung 2 of the FTAP ladder.** Finite Ω (the reachable crown). NOT the
  general-Ω DMW (Rung 3/4), which is gated on L⁰-closedness-under-NA and a
  measurable-selection theorem absent from the Mathlib pin.
- **Scalar** — one risky asset, discounted price `S : ℕ → Ω → ℝ`. Pairs verbatim
  with the existing scalar forward direction.
- **Finite horizon** `T : ℕ`. The EMM property is stated up to `T` only (S need
  not be a Q-martingale past the horizon).
- **Statement form:** `NoArbitrage ↔ ∃ Q, IsEMM Q`.

### Out of scope (named follow-ons, recorded in `coverage.md`)
- **d-asset multi-period** — mechanical generalisation (vector `S`, vector
  martingale transform, separation in `EuclideanSpace ℝ (Fin d)` per period).
- **General-Ω DMW (the crown)** — Rung 3/4; needs L⁰-closedness + measurable
  selection. Separate, longer, partly upstream-grade campaign.

## 3. What already exists (reuse, do not rebuild)

Discrete-martingale spine (`MathFin/Foundations/`, all green):
- `MartingaleTransform.lean` — `martingaleTransform (A M : ℕ → Ω → ℝ) (n) (ω) :=
  ∑ k ∈ Finset.range n, A (k+1) ω * (M (k+1) ω - M k ω)` (the discrete
  stochastic integral / gains process) + `martingaleTransform_isMartingale`.
- `DoobDecomposition.lean`, `OptionalSamplingInequality.lean`,
  `L2MartingaleConvergence.lean` — not directly needed here but confirm the
  martingale toolkit is mature.

Existing FTAP scaffolding (`MathFin/Foundations/`):
- `FTAP.lean : emm_implies_no_arbitrage` — forward direction, abstract,
  multi-period, **all-time** `Martingale S 𝓕 Q`. Left untouched (the all-time
  cousin); our finite-horizon forward is proved fresh against the one-step EMM.
- `FTAPTwoState.lean` — `HasEMM_two_state`, `HasArbitrage_two_state`,
  `emm_of_signs` (backward, two-state single-period).
- `FTAPMultiState.lean` — `HasEMM_multi_state`, `HasArbitrage_multi_state`,
  `noArbitrage_of_emm_multi` (forward, finite-state single-period). The file
  explicitly flags the **backward direction as "not formalised — Phase 42c,
  needs Hahn–Banach separation."** We complete that here (§7).

## 4. Market model + statement (`MathFin/Foundations/FTAPDiscrete.lean`, new)

```lean
variable {Ω} [Fintype Ω] [Nonempty Ω] {mΩ : MeasurableSpace Ω}
  [MeasurableSingletonClass Ω]
  (𝓕 : Filtration ℕ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
  (hP : ∀ ω, 0 < P {ω})                    -- full support ⇒ "equivalent" is meaningful
  (S : ℕ → Ω → ℝ) (hS : Adapted 𝓕 S) (T : ℕ)

/-- No predictable strategy turns zero initial wealth into a sure non-loss
with a positive chance of gain. `≤ᵐ[P]` / `=ᵐ[P]` matches the repo idiom and,
on full-support finite Ω, equals the pointwise statement. -/
def NoArbitrage : Prop :=
  ∀ φ : ℕ → Ω → ℝ, StronglyAdapted 𝓕 (fun n => φ (n+1)) →
    0 ≤ᵐ[P] martingaleTransform φ S T → martingaleTransform φ S T =ᵐ[P] 0

/-- Equivalent martingale measure for the finite horizon. The martingale
property is one-step up to `T` (NOT Mathlib's all-time `Martingale`), the
honest finite-horizon object. -/
structure IsEMM (Q : Measure Ω) : Prop where
  prob  : IsProbabilityMeasure Q
  equiv : Q ≪ P ∧ P ≪ Q
  mart  : ∀ t, t < T → S t =ᵐ[Q] Q[S (t+1) | 𝓕 t]

theorem ftap_discrete : NoArbitrage 𝓕 P S T ↔ ∃ Q, IsEMM 𝓕 P S T Q
```

Notes:
- `Adapted 𝓕 S` = `∀ t, StronglyMeasurable[𝓕 t] (S t)`. Predictability of `φ`
  = `StronglyAdapted 𝓕 (fun n => φ (n+1))` (`φ (n+1)` is `𝓕 n`-measurable) —
  exactly the repo convention used by `martingaleTransform_isMartingale`.
- Integrability of `S t` under `Q` is free (Fintype ⇒ bounded), so the
  `condExp` in `mart` is the genuine conditional expectation.
- `T` indexes `Finset.range T` in the transform, using `S 0 … S T`; one-step EMM
  ranges `t = 0 … T-1`.

## 5. Proof route — B (global separation). APPROVED.

The single conceptual move: **no-arbitrage ⟺ the attainable-gains subspace
misses the positive orthant ⟺ a strictly-positive pricing functional (the EMM)
exists.** Worked entirely in the finite-dimensional `EuclideanSpace ℝ Ω`.

(Route A — per-atom backward induction gluing one-step densities — was the
considered alternative; rejected for finite Ω because it needs a
change-of-measure conditional-expectation (Bayes-under-`withDensity`) lemma
absent from the pin, plus product/tower bookkeeping. Route B is lower-risk and
all-Mathlib.)

### Backward direction (`exists_isEMM_of_noArbitrage`), step by step

1. **`gainsLinearMap`** — `φ ↦ martingaleTransform φ S T` is ℝ-linear in `φ`.
   Realise the attainable-gains set as a submodule
   `V : Submodule ℝ (EuclideanSpace ℝ Ω)`, `V = LinearMap.range gainsLinearMap`
   restricted to predictable `φ`. `V` is finite-dimensional ⇒ **closed**
   (`Submodule.closed_of_finiteDimensional`).
   - Care point: the domain "predictable strategies" is itself a submodule of
     `(ℕ → Ω → ℝ)`; `V` is the image of that submodule. Equivalent concrete
     description: `V = span { 𝟙_A · (S (t+1) - S t) : t < T, A ∈ 𝓕 t-measurable }`
     — used directly in step 4.

2. **`disjoint_V_stdSimplex`** — `NoArbitrage ⇒ V ∩ stdSimplex ℝ Ω = ∅`. The
   simplex consists of non-negative, non-zero vectors; any such vector in `V`
   is a gains vector `≥ 0`, `≠ 0`, i.e. an arbitrage — contradiction.
   (`stdSimplex` is `convex_stdSimplex` and `isCompact_stdSimplex`, nonempty
   since `[Nonempty Ω]`.)

3. **`exists_separating_functional`** — `geometric_hahn_banach_compact_closed`
   on the compact convex simplex and the closed convex `V` yields
   `f : EuclideanSpace ℝ Ω →L[ℝ] ℝ` and reals `u < v` with `f < u` on the
   simplex and `f > v` on `V`. Since `V` is a subspace, `f` bounded below on `V`
   ⇒ **`f ≡ 0` on `V`** (else `f (λ b) = λ f b → -∞`); hence `v < 0` and
   `f < u ≤ v < 0` on the simplex. Define `q ω := - f (EuclideanSpace.single ω 1)`;
   each `single ω 1 ∈ stdSimplex` (a vertex) ⇒ **`q ω > 0`** for all `ω`.

4. **`isEMM_of_separating`** — normalise: `Z := ∑ ω, q ω > 0`,
   `Q := (PMF.ofFintype (fun ω => q ω / Z) _).toMeasure`. Then:
   - `IsProbabilityMeasure Q` (`PMF.toMeasure.isProbabilityMeasure`); `Q {ω} =
     q ω / Z > 0` ⇒ `Q ≪ P ∧ P ≪ Q` (both full support on finite Ω).
   - **Martingale property.** `f ≡ 0` on `V` and `f x = ∑ ω, x ω * f (single ω 1)`
     (basis expansion) give, for every `g ∈ V`, `∑ ω, q ω * g ω = 0`, i.e.
     `∫ g dQ = 0` (`PMF.integral_eq_sum`). Apply with the indicator strategy
     `φ = fun s => if s = t+1 then 𝟙_A else 0` (`A` `𝓕 t`-measurable, so `φ`
     predictable), whose gains are `𝟙_A · (S (t+1) - S t) ∈ V`. Thus
     `∫_A (S (t+1) - S t) dQ = 0`, i.e. `∫_A S (t+1) dQ = ∫_A S t dQ` for all
     `A ∈ 𝓕 t`. With `S t` `𝓕 t`-measurable (adapted) and everything
     `Q`-integrable, `ae_eq_condExp_of_forall_setIntegral_eq` gives
     `S t =ᵐ[Q] Q[S (t+1) | 𝓕 t]`.

### Forward direction (`noArbitrage_of_isEMM`)

Fresh, self-contained, consuming the one-step EMM (no dependency on
`FTAP.emm_implies_no_arbitrage`). For predictable `φ`, the gains
`G := martingaleTransform φ S` satisfy
`Q[G (t+1) - G t | 𝓕 t] = φ (t+1) · Q[S (t+1) - S t | 𝓕 t] = 0`
(pull out the `𝓕 t`-measurable `φ (t+1)`; one-step EMM). Telescoping ⇒
`∫ G T dQ = ∫ G 0 dQ = 0`. If `G T ≥ᵐ[P] 0` then (`P ≪ Q`) `G T ≥ᵐ[Q] 0`, and a
non-negative `Q`-integrable function with zero integral is `0` `Q`-a.e., hence
(`Q ≪ P`) `0` `P`-a.e. So `NoArbitrage`.

### Assembly
`ftap_discrete := ⟨fun hNA => exists_isEMM_of_noArbitrage …,
                   fun ⟨Q, hQ⟩ => noArbitrage_of_isEMM hQ⟩`.

## 6. Mathlib pieces consumed (names confirmed against the pin)

Backward direction (separation):
- `geometric_hahn_banach_compact_closed` (`Analysis/LocallyConvex/Separation.lean`)
- `stdSimplex`, `convex_stdSimplex`, `isCompact_stdSimplex`
  (`Analysis/Convex/StdSimplex.lean`)
- `Submodule.closed_of_finiteDimensional` (`Analysis/Normed/Module/FiniteDimension.lean`)
- `ae_eq_condExp_of_forall_setIntegral_eq`
  (`MeasureTheory/Function/ConditionalExpectation/Basic.lean:251`)
- `PMF.toMeasure`, `PMF.toMeasure_apply_singleton`, `PMF.integral_eq_sum`
  (`Probability/ProbabilityMassFunction/*`)

Forward direction (telescoping):
- `condExp_mul_of_stronglyMeasurable_left`
  (`MeasureTheory/Function/ConditionalExpectation/PullOut.lean:245`) — pull the
  `𝓕 t`-measurable `φ (t+1)` out of the conditional expectation.
- `integral_condExp`, `setIntegral_condExp`
  (`…/ConditionalExpectation/Basic.lean:229`).
- `integral_eq_zero_iff_of_nonneg_ae` (already consumed by
  `FTAP.emm_implies_no_arbitrage`).

Available if atom-level reasoning is needed (fallback for the forward
pull-out): `measurableAtom`, `measurableSet_measurableAtom`,
`MeasurableSet.measurableAtom_of_countable`
(`MeasureTheory/MeasurableSpace/Constructions.lean`,
`…/CountablyGenerated.lean:253`) — not expected in Route B.

## 7. Rung-1 companion (`FTAPMultiState.lean`, extend)

Add the backward direction the file already flags as missing:
`hasEMM_multi_of_not_hasArbitrage : ¬ HasArbitrage_multi_state z →
HasEMM_multi_state z` for `z : Fin M → Fin N → ℝ`, via the same separation
(`geometric_hahn_banach_compact_closed` in `EuclideanSpace ℝ (Fin N)`,
separating the gains cone from the simplex). This is the single-period shadow of
Route B and completes "Phase 42c", upgrading the multi-state result to a
biconditional `noArbitrage ↔ ∃ EMM`. Cheap; deliver alongside.

## 8. Files

- **new** `MathFin/Foundations/FTAPDiscrete.lean` — `NoArbitrage`, `IsEMM`,
  `gainsLinearMap`, the four backward steps, `noArbitrage_of_isEMM`,
  `ftap_discrete`. Module header per repo rule (`module` + `public import` +
  `@[expose] public section` + `namespace MathFin`).
- **edit** `MathFin/Foundations/FTAPMultiState.lean` — add §7 backward +
  biconditional; update the file docstring (drop the "Phase 42c not formalised"
  caveat).
- **edit** `MathFin.lean` umbrella — add `import MathFin.Foundations.FTAPDiscrete`
  (re-sync the single-file bind mount / restart daemon after editing per the
  inode caveat in CLAUDE.md).
- **edit** `MathFin/AxiomAudit.lean` — pin the new headline constants
  (`ftap_discrete`, the multi-state backward) axioms-clean.

## 9. Corpus + wiring

- `benchmarks/mathematical_finance.json`:
  - `mf-ftap-discrete-complete` — the multi-period biconditional (headline),
    `domain: mathematical_finance`, `formalization_status: full`, snippet
    imports `MathFin.Foundations.FTAPDiscrete` and re-states `ftap_discrete`.
  - `mf-ftap-single-period-complete` — the multi-state biconditional, `full`.
- `metadata.formalization_scope` on each: explicit finite-Ω / scalar / finite-T
  boundary + the named open follow-ons (§2).
- Regenerate `python3 -m tools.verify.axiom_audit_gen --write`
  (`MathFin/AxiomAuditGen.lean`); refresh `verification_ledger.json`
  (`ledger status` / `ledger verify`).
- Update `docs/coverage.md` (new full entries + scope wording) and
  `docs/bridges.md` if a bridge row fits.
- Tests: `tests/test_router.py`, `tests/test_ledger.py`, `tests/test_values.py`
  must stay green (Lean-only routing, ledger rows, no forbidden text, declared
  status, exhaustive-audit freshness).

## 10. Risks

- **Low overall** — no Mathlib gaps; every load-bearing lemma confirmed present.
- **TVS plumbing.** Working in `EuclideanSpace ℝ Ω`: realising the predictable
  strategies and `V` as submodules, the basis expansion
  `f x = ∑ ω, x ω * f (single ω 1)`, and `f`-vanishes-on-subspace. Bounded,
  finite-dimensional, but the fiddliest part.
- **NA ↔ a.e. vs pointwise.** On full-support finite `P` these coincide; keep
  the `ᵐ[P]` form and discharge equivalences via `hP`.
- **Indicator-strategy bookkeeping.** The test strategy `φ = if s = t+1 then 𝟙_A
  else 0` must be shown predictable and its gains identified with
  `𝟙_A (S (t+1) - S t)`; mechanical.
- **No daemon on v4.31** (lean-interact 0.11.4 caps rc1, per memory) — iterate
  via the ledger `--exec` warm path / `lake build`, not the REPL daemon.

## 11. Acceptance criteria

1. `lake build` green; `FTAPDiscrete.lean` and the extended `FTAPMultiState.lean`
   compile, no `sorry`/`admit`/forbidden tactics.
2. `ftap_discrete` and the multi-state backward are **axioms-clean**
   (`AxiomAudit` `#guard_msgs`-pinned; `AxiomAuditGen` regenerated).
3. New corpus entries verify; `python3 -m tools.verify.ledger status` all fresh.
4. `pytest tests/` green (`test_router`, `test_ledger`, `test_values`).
5. `coverage_report` reflects the new `full` entries; scope wording honest.
6. Values review (8 lenses) appended if the corpus cadence gate requires it.
