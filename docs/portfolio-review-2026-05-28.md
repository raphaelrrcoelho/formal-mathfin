# Portfolio review — 2026-05-28

A contract-aligned audit of the whole library against the six standing
values:

1. **Inspired math quality**
2. **Mathlib / BrownianMotion(Degenne) coherence**
3. **Zero slop**
4. **Architectural ingenuity**
5. **First principles**
6. **Superior genius concept clarity**

Snapshot: 148 Lean files, 22,975 LOC; cold `lake build` green (8,650/8,650);
zero `sorry`/`admit`/`TODO`/`FIXME` anywhere in `MathFin/`. The last
contract-aligned review was 2026-05-26 ("library fundamentally sound +
honest, bounded slop fixed in 6 commits"); this review re-runs the same
lens against the state two days later, post-CLM landing.

The library is in good shape on every axis it claims, but **one
structural deviation has widened**, three medium-grain hygiene items
warrant tightening, and **two opportunities to strengthen ingenuity**
present clean unlocks. Findings below in priority order.

## Findings — deviations

### F1. The Foundations → pricing bridge gap has *grown*, not closed
**Verdict: load-bearing structural deviation; track as the project's
single biggest architectural debt.**

The 2026-05-22 memory flagged "4,664 LOC of `Foundations/` BM/Wiener
machinery sits unused by pricing modules". As of today:

* `Foundations/` BM + Itô + Wiener + martingale tier: **9,460 LOC** (up
  ~2× since the flag, including the new CLM + process scaffold + squaring
  identity landed in the last 24h).
* Pricing modules (`Binomial/`, `BlackScholes/`, `Performance/`,
  `RiskMeasures/`) that import any of `Foundations.{ItoIntegralL2,
  ItoIsometryAdapted, WienerIntegralL2, BrownianMartingale}`:
  **0 files**.

The pricing layer reaches into `Foundations/` for *Gaussian / lognormal*
moment lemmas (`GaussianMoments`, `LognormalMoments`,
`LognormalCOV`), for the **`bs_identity`** root closed-form, and for
geometric BM as a *posited dynamics* (via `BSCallHypFromBrownian`,
`PricingFromBrownian`) — but it never crosses into the Itô-isometry / CLM
machinery as a *derivation* of those dynamics. The CLM shipped today
unblocks the path; *consuming* it from `BlackScholes/PDEFromIto.lean` is
still on the resume plan, not in code.

This is **not slop** — the architecture doc is explicit that
"Foundations machinery becomes load-bearing only when downstream modules
can consume it", and the bridges are documented in `docs/bridges.md`. It
*is* the highest-leverage piece of unfinished structural work.

Recommended next move: pick *one* pricing identity (the BS-PDE drift
balance is the cleanest candidate — `BlackScholes/PDEFromIto.lean`
already exists as the home) and refactor it to consume `itoIntegralCLM_T`
+ the Itô-squaring identity rather than positing the GBM dynamics. One
genuine consumer is worth more than a dozen unused theorems.

### F2. Two parallel Itô-integral tracks coexist; one is now strictly weaker
**Verdict: minor bounded slop; mark the weaker track as legacy.**

Two simple-process Itô-integral constructions sit side by side in
`Foundations/`:

| File | LOC | Origin | Status after the CLM landed |
|---|---|---|---|
| `ItoIntegralL2.lean` + `ItoIntegralCLM.lean` | 1,206 | Degenne-anchored, full L² extension via `extendOfNorm` | **Canonical** |
| `ItoIntegralSimple.lean` | 103 | Nagy 2026-derived, simple-process only | **Strictly subsumed** by `ItoIntegralL2.itoSimple` + algebra |

`ItoIntegralSimple.lean` is honest about its scope (the docstring notes
"the L² extension via Cauchy completeness is deferred — see
`Foundations/WienerIntegralL2.lean` for our existing parallel work via a
different construction path"). With the CLM now landed, the *L²
extension* path is no longer "via Cauchy completeness elsewhere" — it is
`ItoIntegralCLM_T`, in the same file family. The Nagy file is now a
historical attribution + Lean exercise (`itoIntegralSimple_linear`,
`itoIntegralSimple_isometry_constant_integrand`, `itoIntegralSimple_scale`)
whose three theorems all live inside `ItoIntegralL2.itoAssembly`'s span.

Recommendation: add a one-line note to the top of `ItoIntegralSimple.lean`
("**Legacy — use `ItoIntegralL2.itoSimple` / `ItoIntegralCLM_T` for new
work**; this file is retained for attribution to Nagy 2026 §4 and for the
discrete-Itô track in `DiscreteIto.lean`"). Do *not* delete — the
attribution is honest and the file is small.

### F3. `BlackScholes.GarmanNormalForm` is imported but not in the umbrella
**Verdict: minor index gap.**

`MathFin.BlackScholes.GarmanNormalForm` is imported by three downstream
modules (`ExchangeOption`, `Futures.Black76`, `FixedIncome.KMVMerton`)
and the umbrella file `MathFin.lean` has explicit `import` lines for
every other authored file *except* this one. Lake's `globs :=
.andSubmodules` picks it up regardless, but the umbrella's role is
"single grep target for the human reader" and the omission is jarring.

Recommendation: add the import line. One-line fix.

### F4. 130 of 148 files (~88%) `import Mathlib` (the whole library)
**Verdict: bounded slop; cosmetic but cumulative.**

`import Mathlib` pulls in every Mathlib module and noticeably inflates
elaboration time per file even with `lake exe cache get` warm. The
analogous pattern in upstream Degenne / blueprint-quality Mathlib work
is to import the minimal subset (`Mathlib.MeasureTheory.Function.LpSpace`,
`Mathlib.Probability.…`, etc.).

This was acceptable when the library was 30 files; at 148 it is a
visible drag on incremental builds and on the daemon's cold-start time
(the daemon takes ~5 min cold even with the new `.lake/` volume because
each file re-elaborates its full Mathlib import). The contract item
"Mathlib / Degenne coherence" includes *coherent imports*, not just
*coherent results*.

Recommendation: opportunistic — when touching a file for substantive
work, narrow its `import Mathlib` to the actually-needed modules. Do
*not* sweep this in a single commit (risk of correctness regressions on
implicit-instance availability). Track as a slow-tail cleanup.

## Findings — opportunities to strengthen

### O1. The discrete-Itô-squaring identity can lift to the L² Itô lemma in one file
**Leverage: high.**

The discrete pathwise identity `X_N² − X_0² = 2 ∑ X_k·ΔX_k + ∑ (ΔX_k)²`
(landed today) plus the existing `BrownianQuadraticVariation.qv_equals_t`
plus the new `itoIntegralCLM_T` are the three pieces of the continuous
L² Itô formula

  `B_T² = 2 · itoIntegralCLM_T (B-process indicator [0,T]) + T`   in `Lp 2 μ`.

The path is mechanical: build the step-process `V_n` (left-endpoint
sampling of `B` at the dyadic partition), show `V_n → B-as-Lp` in
`L²(trim_T)`, use CLM continuity to push the convergence into `Lp 2 μ`,
combine with the QV limit, and out pops the formula. ~400 LOC,
self-contained against existing infrastructure.

This is the natural Phase B "to completion" in a follow-up session.

### O2. The natural-filtration adaptedness lemma `adaptedAt_of_measurable_natural` is the *only* current bridge from Degenne measurability to `ItoIsometryAdapted.AdaptedAt`
**Leverage: medium; turn the load-bearing fact into an `@[fun_prop]` lemma.**

`ItoIntegralL2.adaptedAt_of_measurable_natural` does the Doob-Dynkin
factorisation that lets the upstream `SimpleProcess`-based Itô machinery
talk to our home-grown `ItoIsometryAdapted.AdaptedAt`-stated isometry
core (`rect_increment_pairing` and friends). It is invoked manually in
every isometry-consuming proof in `ItoIntegralL2.lean`
(`memLp_itoSimple`, `itoSimple_sq_integral`, `simpleProcessL2_norm_sq`).

Tagging it `@[fun_prop]` (or even just bundling the
`AdaptedAt_of_measurable_value` shortcut as a definition) would let
future proofs in `ItoIntegralProcess.lean`, in any continuous-time Itô
work, and in the Phase B L²-Itô formula write `by fun_prop` instead of
the four-line `Measurable.exists_eq_measurable_comp` cascade. The
load-bearing fact deserves a single name, not a copy-pasted invocation.

### O3. `ItoIntegralCLM.lean` has three private lemmas flagged `unusedSectionVars` (`hB`)
**Leverage: low; cosmetic, but the linter pings every cold build.**

Three private lemmas
(`eLpNorm_uncurry_trim_T_eq_trim`,
`setIntegral_eq_zero_of_orthogonal_pred`,
`setIntegral_eq_setIntegral_inter_supp`) don't use the section-level
`[hB : IsPreBrownian B μ]` instance, and the linter says so on every
cold build. The `omit hB in private lemma …` syntax doesn't compose
cleanly (parser error encountered during authoring); the
`set_option linter.unusedSectionVars false in private lemma …` form
similarly didn't work because the linter sits before `private`.

Recommendation: lift the three private lemmas *out* of the
`[IsPreBrownian B μ]` variable scope — they are pure measure-theoretic
facts that don't need it — by splitting the file into two `section`
blocks (the measure-theoretic preamble *before* `variable [hB …]` and
the Itô-specific tail *after*). Pure cleanup; no proof changes.

## What's not on the deviation list (and why)

* **Axiom-cleanness.** All 36 audited theorems pin
  `[propext, Classical.choice, Quot.sound]`. The CLM + the four new pins
  (including `simpleAssembly_T_denseRange`, `itoIntegralCLM_T_norm`,
  `discrete_squaring_identity`) maintain the invariant. This is on track.
* **`sorry` / `admit`.** None anywhere in `MathFin/`. (One `sorry` literal
  appears inside a *docstring* in `AxiomAudit.lean`, explaining what the
  audit prevents — that is not a proof obligation.)
* **`TODO` / `FIXME` / `XXX`.** None.
* **Docstrings.** Every file in `Foundations/` opens with a `/-! … -/`
  module docstring naming results + giving an intuition; pricing modules
  are equally documented. The library reads top-to-bottom without
  needing the blueprint.
* **The CLM landing.** The seven phases delivered today are all
  axiom-clean, no slop, with substantive content in each phase (Phase 5's
  π-λ induction, Phase 6's orthogonal-complement / `iocSP_T` / inner-
  product-as-set-integral). The companion blueprint entry was added.

## Summary

| Item | Severity | Action | **Status after follow-up sweep** |
|---|---|---|---|
| F1. Foundations→pricing bridge gap | **structural** | one pricing-side consumer in the next session | **partial** — `BlackScholes/PDEFromIto.lean` docstring now names the chain (`itoIntegralCLM_T`, `itoSquared_L2_tendsto_div2` ✓, then `C²`-Itô + GBM-SDE = multi-session). Full refactor deferred. |
| F2. Two Itô-simple tracks | minor slop | one-line "legacy" header on `ItoIntegralSimple.lean` | **done** (`414a034`) |
| F3. Garman missing from umbrella | minor index | add the import line | **done** (`ae9f1fc`) |
| F4. `import Mathlib` everywhere | cumulative cosmetic | tighten opportunistically | **partial** — narrowed `Foundations/ItoFormulaSquaredL2.lean` (one file, opportunistic-as-you-go per the review). |
| O1. Discrete-squaring → L²-Itô | high leverage | next phase, ~400 LOC | **done** (`99d11fb`) — actual landing was 141 LOC because the proof reduces to one algebraic step + `tendsto_qv`. `Foundations/ItoFormulaSquaredL2.lean` proves `∑ B·ΔB → ½(B_T² − B_0² − T)` in L²(μ). |
| O2. `adaptedAt_of_measurable_natural` → `@[fun_prop]` | medium | one attribute | **closed-as-deferred** — `ItoIsometryAdapted.AdaptedAt` isn't a registered `fun_prop` property; the attribute is rejected by the elaborator. Closing O2 properly requires registering `AdaptedAt` upstream (single-line attribute on the definition itself), a deeper change than the review estimated. Tracked. |
| O3. `ItoIntegralCLM.lean` linter hints | low cosmetic | split the section | **done** (`2b37b44`) — `omit hB in` on the three private lemmas (placed BEFORE the docstring to satisfy the parser; the section split was unnecessary). |

Commits in the sweep:
* `414a034` — Itô-process scaffold + discrete squaring identity.
* `ae9f1fc` — Portfolio review + F2 / F3 cheap fixes.
* `2b37b44` — Slop sweep: O3 + 8 unused-var fixes + 1 deprecated alias.
* `99d11fb` — Itô's lemma for `f(x)=x²` continuous L² form (O1 done).
* `68c2ebf` — F1 status note in `PDEFromIto.lean` + F4 partial.

The contract is intact. The single architectural debt (F1) is the same
one the project has carried since the foundations layer began landing —
it is real, it is named, and shipping the CLM + L² Itô squaring formula
makes the canonical closing path concrete. The next session's deliverable
is the `C²` Itô extension (general `f`, not just `x²`) plus GBM-as-SDE-
solution, which then makes `bsItoDrift` (the algebraic target in
`PDEFromIto.lean`) a *derived* coefficient rather than a posited one.
