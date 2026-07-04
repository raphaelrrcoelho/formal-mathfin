# Idiomatic Lean / Mathlib review — 2026-07-04 (whole corpus)

A craft-level review of the entire Lean library (227 files / ~45k lines) for
**idiomatic Lean 4 / Mathlib code quality and best practice** — distinct from
the 8-lens *values* review (`docs/values-review.md`, which judges mathematical
honesty/inspiration) and narrower: this pass asks only "is the *code* written
the way a Mathlib maintainer would write it?" It is closest to the values
lenses *Mathlib/Degenne coherence* and *idiomatic register*.

**Method.** Eleven read-only reviewers fanned out over disjoint slices
(Foundations ×6 on Opus; BlackScholes ×2 + Binomial/FixedIncome/Portfolio ×3 on
Sonnet), each with a rubric calibrated to this repo's *high* ceiling
(`Foundations/ItoIntegralL2.lean` as the gold standard) and told that
manufacturing findings is the primary failure mode. Every finding below was
**re-verified by hand against the source** — and, where it names a Mathlib
lemma, against the actual Mathlib tree (`.lake/packages/mathlib`); a few were
compile-checked against the REPL daemon. Agent over-claims were rejected (see
*Non-findings*).

---

## Headline verdict

**The library is in excellent idiomatic shape.** Mechanically it is essentially
spotless — corpus-wide there are **zero** `by exact`, zero `push_neg`/deprecated
tactics, zero `?`-suggestion tactics, zero `sorry`/`admit`/`native_decide`,
consistent copyright headers, and near-universal rich docstrings. Six of the
eleven slices came back with *no* MED-or-higher finding.

There is **no HIGH-severity correctness or maintainability defect** and **no
mechanical slop.** What the read *did* surface is a modest, almost entirely
**LOW-severity** backlog with two real shapes:

1. **DRY / coherence consolidations** (the MED tier) — ~8 spots where a
   *purpose-built Mathlib lemma* or an *existing repo lemma* should be *consumed*
   instead of re-proved, several of them duplicated across 3–4 files. This is the
   library's own anti-wrapper / coherence-first doctrine applied to itself.
2. **A cosmetic dead-`open` sweep** (~50 files with a vestigial `open`).

Both are low-risk. The main *cost* is not difficulty but the **verification
ledger**: any edit to a `MathFin/` file re-stales the entries that import it, so
a broad sweep re-verifies a large slice for little mathematical gain. Recommended
action order (below) is sequenced with that in mind.

---

## MED tier — DRY / coherence consolidations (8)

All verified; all low-risk; all "consume the idiomatic lemma instead of
re-proving it." Ranked by value.

| # | Site(s) | Issue | Fix | Verified |
|---|---------|-------|-----|----------|
| I1 | `FixedIncome/Immunization.lean:75`, `ConvexityImmunization.lean:68`, `DurationSensitivity.lean:87`, `ConvexitySensitivity.lean:72` | `HasDerivAt.sum` yields a Pi-typed sum, so each file adds a `funext`+`Finset.sum_apply` eta-workaround (with an apologetic comment) to get back a function-of-sum — **×4 verbatim** | replace with **`HasDerivAt.fun_sum`** (whose conclusion is already `HasDerivAt (fun x => ∑ …) (∑ …) x`), deleting the `h_fn_eq` block in all four | ✓ Mathlib `Deriv/Add.lean:218`; agent daemon-compiled |
| I2 | `Foundations/LpContinuousMartingaleConvergence.lean:212` | `private lemma ofReal_norm_eq_enorm` re-proves a Mathlib lemma — under the *exact name of Mathlib's own `@[deprecated]` alias* | delete it; use **`ofReal_norm`** at lines 245/248 | ✓ Mathlib `Normed/Group/Basic.lean:396`, alias at :398 |
| I3 | `Foundations/ItoIntegralL2.lean:179`, `ItoIntegralBrownian.lean:259`, `WienerIntegralL2.lean:435` | the generic fact `‖g‖² = ∫ (g z)² ∂ν` is proved **×3 verbatim**; the Brownian copy's docstring even claims to be "the single home for this generic L² fact" (false) | keep the earliest-in-DAG copy, delete the other two, re-point consumers; fix the docstring | ✓ read all three |
| I4 | `Foundations/ItoIntegralProcessLocalMartingale.lean:72`, `…LocalMartingaleGeneral.lean:91`, `…LocalMartingaleInfinite.lean:38` | `private isCadlag_of_continuous` (Continuous ⟹ IsCadlag) defined **×3 verbatim**; the latter two docstrings literally say "re-derived because the [0,T] copy is `private`" | drop `private` on one base copy and consume it (or upstream `Continuous.isCadlag` to Degenne — confirmed absent there) | ✓ read all three |
| I5 | `Binomial/MertonAmericanCallTree.lean:76` | `binomial_martingale_identity` is a verbatim re-proof (`unfold; field_simp; ring`) of `crrUpProb_mul_up_add` — same statement, from `Model.lean:226`, which this file **already imports** | `:= crrUpProb_mul_up_add u d r h` | ✓ read both; import at line 9 |
| I6 | `BlackScholes/PDE.lean:140` (also `:293`, `StrikeGreeks.lean:85`) | `hasDerivAt_bsd2_S` hand-rolls "subtract a constant" (`hasDerivAt_const` + `.sub` + `funext` + a `- 0` massage), **×3** — while the same file uses `.add_const`/`.const_add` at six other sites | `(hasDerivAt_bsd1_S …).sub_const (σ * Real.sqrt τ)` | ✓ read; `HasDerivAt.sub_const` is standard |
| I7 | `BlackScholes/Digital.lean:59` and `:142` | the indicator-transfer block `h_indic_eq` is proved **twice verbatim**, differing only in the payoff `f` | factor one `private` lemma parameterised by `f`, instantiate at both sites | ✓ read both |
| I8 | `BlackScholes/BreedenLitzenberger.lean:182` | `by_contra; not_le; linarith [mul_neg_of_pos_of_neg …]` to get `0 ≤ pdf` from `0 ≤ e^{-rT}·pdf` and `0 < e^{-rT}` | `(mul_nonneg_iff_of_pos_left h_exp_pos).mp h_d2_nn` | ✓ Mathlib `Order/Ring/Unbundled/Basic.lean:442` |

**MED-minor (fold in when touching the file):** `Immunization.lean:64` re-derives
the ZCB `r`-derivative from scratch though its docstring claims to "recover the
ZCB result" — but never imports `ZCB.lean` (import it, use `hasDerivAt_zcb_r`);
`ConvexitySensitivity.lean:109` `convert … <;> try rfl; ring` for a plain
`-(-x)=x` → `rw [neg_neg] at h; exact h`; `NewtonConvergence.lean:138/169`
duplicates two `HasDerivAt` `have`-blocks across `rcases` branches → hoist.

---

## LOW tier — grouped

### C1 — Vestigial / dead `open`s (the dominant nit, ~50 files)
Verified counts: **6** files with vestigial `open scoped BigOperators` (`∑`/`∏`
are global at this pin — 82 files use them *without* it), **25** with dead
`open scoped NNReal ENNReal` (the `ℝ≥0`/`ℝ≥0∞` notation never appears), **~25**
with a likely-dead `open Real` (everything `Real.`-qualified), plus scattered
`open Finset` / `open MeasureTheory intervalIntegral` / `open … Set`.
This is genuine dead code, but it is **one cleanup sweep, not 50 fixes**, and it
**cannot be a blind `sed`** — removing an `open` that turns out to be load-bearing
breaks the build, so each file needs a daemon check. Because the sweep re-stales
a large ledger slice for zero mathematical content, treat it as **opt-in
cosmetic** or fold each file's opens in when it is edited for another reason.
(Representative sites: `PDE.lean:41`, `KMVMerton.lean:48`, `FTAPDiscrete.lean:47`,
`ConvexDuality.lean:45`, six `Binomial/*` `open Real`, `SDEUniqueness.lean:40`.)

### C2 — Missing / stale docstrings (~10 sites)
Exported declarations lacking a `/-- -/` in otherwise fully-documented files:
`ItoIntegralL2.timeMeasure_Ioc:218`, `ItoIntegralBrownian.measurable_clampM:72`,
`WienerIntegralL2` StepIndex helpers, `StandardNormal.Phi_eq_integral:56` (listed
under "Main results"), `MertonJumpDiffusion` `mertonSpot_pos`/`mertonVol_pos`,
`RiskMeasures/WorstCaseRisk` `le_worstCase`/`worstCase_le`, `Binomial/Model`
`binomialPrice_zero`/`_succ`, `CRRConvergence` `crrUp_pos`/`crrDown_pos`. Plus one
**stale** stamp: `ExpMin.lean:26` docstring says "(Mathlib v4.30 API)" on a v4.31
pin — drop version stamps, they drift silently. And fix I3's false "single home."

### C3 — Collapsible tactic idioms (all LOW)
`BrownianMartingale.lean:82` & `:135` `have := X; exact this` → term-mode `have h : T := X`;
`ItoIntegralProcessContinuousModification.lean:309` `simp only […]; exact hLp` → `simpa only […] using hLp`;
`CouponBonds.lean:83` `convert …; funext; exact h_eq` → `HasDerivAt.congr_of_eventuallyEq` (**the idiom `patterns.md` itself documents**);
`BachelierGreeks.lean:46` (+3) `convert (hasDerivAt_id _).sub_const _ <;> rfl` → `hasDerivAt_id'` directly;
`Spectral.lean:87` `rw [show ∑ t*φ = t*∑φ from (mul_sum).symm]` → `rw [← Finset.mul_sum]` (used correctly 10 lines below);
`MarkowitzNAsset.lean:112` `rw [show univ = {0,1} from rfl]` → `Fin.sum_univ_two`;
`DigitalGreeks.lean` repeated 4-line `have` preamble ×5 → shared helper.

### C4 — Definitional restatements with no consumers (candidate trims)
`RiskParityFOC.isRiskParity_iff_cross_product` (billed "characterisation", proof is
definitional, **no code consumers** — only a prose mention) and
`MarkowitzLagrangian.variance_objective_eq_self_dot` (`unfold; rfl`, no consumers):
either delete, or relabel from "characterisation"/"identity" to "definitional
restatement." Also `PDEFromIto.lean:117` closes an `Iff` that is `Iff.rfl`-after-`unfold`
with `constructor; intro; linarith`; `YieldCurve` `bootstrap_solve_first`/`_second`
re-prove specializations of `bootstrap_solve` above them (conf low — may be
deliberate pedagogical concreteness).

### C5 — Naming (each carries a churn caveat)
`isLundbergAdjustmentCoefficient` (`Actuarial/Mortality.lean:124`) is a lowerCamelCase
`Is`-prefixed `Prop` → Mathlib wants **PascalCase** `IsLundbergAdjustmentCoefficient`;
`variance_itoIntegralCLM_T` carries a `variance_` prefix but states `∫ I² = ‖φ‖²` (no `Var`);
`itoIntegralProcessGen_*` breaks the sibling `itoProcessCLM_*` convention;
`exchangeOption_numeraire_price` is camelCase in an otherwise snake_case file.
**Note:** several of these names are benchmark-exported and `AxiomAudit`-pinned, so a
rename carries ledger + audit churn a maintainer may reasonably decline for a cosmetic gain.

### C6 — Borderline micro-wrappers (judgment)
`ItoLemma.gbm_log_volatility` (`σ·S·(1/S)=σ`) and `NoArbitrageDerivations.max_sub_max_neg`
(renames one Mathlib lemma, used once) — each is one line and *disclosed* as a named
concept marker; keep-or-inline is a judgment call, not a defect.

---

## Non-findings (explicitly rejected, so this report doesn't over-claim)

- **Bare `simp` (69 occurrences).** Two agents flagged terminal bare `simp` as
  "violating the repo's zero-bare-simp discipline." **There is no such rule** —
  `test_values.py` forbids `sorry`/`admit`/`native_decide`/`polyrith`/`?`-tactics/
  `hammer`/`loogle`, *not* `simp`; terminal `simp` closing a goal is idiomatic
  Mathlib. Rejected as a defect. (Switching a *load-bearing* `simp` to
  `simp only […]` for robustness is a fine optional hardening, not an obligation.)
- **Redundant blanket `import Mathlib` (111 files).** Each is technically covered
  transitively by a `MathFin` import, but blanket `import Mathlib` is the deliberate
  house convention (167/227 files) and dropping them re-stales a large ledger slice
  for zero value. Not swept — same call as the `patterns.md` discount-factor non-sweep.
- **`foo_pos` / `foo_def` one-liners** (`zcb_pos := Real.exp_pos _`, `Phi_def := rfl`, …):
  legitimate named facts about *domain* definitions, not renamed passthroughs. Not wrappers.
- **Audit/example leaves** (`AxiomAudit`, `AxiomAuditGen`, `Blueprint`, `Examples`)
  lacking `@[expose] public section`: intentional (they export nothing).

## Housekeeping (not code)

- **Stray host-side `.lake/packages/mathlib` exists.** `CLAUDE.md` says it "should
  not exist" (the olean store lives in the Docker volume). A build/LSP artifact worth
  clearing. (It did let the review verify findings against real Mathlib source.)
- **REPL daemon** was hit concurrently by review agents (one reported it briefly
  "unresponsive"); the container is still up but a restart before the next authoring
  session is prudent — and a reminder that "one Lean process locally" applies to
  agent fan-outs too.

## What is genuinely good (verified, not adjusted)

`Foundations/ItoIntegralL2.lean`, `ItoIsometryAdapted.lean`, `ItoIntegralL2Dense.lean`,
the whole `ItoFormula*` tower, `FeynmanKacHeatEquation.lean` (1.3k lines, exemplary),
`DoobLpMaximalInequality.lean`, the `Gaussian*`/`Poisson*` leaves, `CRRCharFun.lean`,
`PathReflection.lean`, the FOC files (`SharpeFOCDerivation`, `RiskParityFOC`) — read
in full, hold the gold-standard bar: rich accurate docstrings, clean
`calc`/`filter_upwards`/`refine … ?_`, correct `nlinarith [certificates]` /
`grind` usage, Mathlib-consistent naming, and disclosed (`_`-prefixed) unused
hypotheses. The disciplined-library signal is strong.

---

## Recommended action order

1. **I1–I8** (the MED consolidations) — highest value/risk ratio; each is a small,
   local, verified edit that *removes* code and improves coherence. I1, I3, I4 also
   kill 3–4× duplication. Do these first; they touch few files, so ledger churn is small.
2. **C2 docstrings + I3's false docstring + ExpMin stale stamp** — trivial, zero-risk.
3. **C3/C4 collapsible idioms + definitional-restatement trims** — file-local, low-risk.
4. **C1 dead-`open` sweep** — genuine but cosmetic and ledger-costly; do it opt-in as
   one batched, daemon-checked commit, or amortise it file-by-file when each file is
   next edited. **Not urgent.**
5. **C5 naming** — only if the benchmark/audit churn is acceptable; otherwise leave.

No fixes were applied in this pass (report-first). Every fix above is specified
precisely enough to apply directly. After any batch, regenerate `AxiomAuditGen`
and run `ledger status`/`verify` per `CLAUDE.md`.
