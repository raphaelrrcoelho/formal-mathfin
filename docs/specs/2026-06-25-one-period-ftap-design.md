# Design: one-period general-Ω FTAP (scalar, NA ⟺ ∃ EMM)

- **Date:** 2026-06-25
- **Status:** approved design, pre-implementation
- **Author:** Raphael Coelho
- **Topic:** Fundamental Theorem of Asset Pricing, one trading period, **arbitrary** probability space, single risky asset. ("Rung 3" of the FTAP ladder.)

## 1. Goal

Formalise the **one-period, general-Ω** FTAP (Föllmer–Schied, *Stochastic
Finance*, Thm 1.55; the one-period Dalang–Morton–Willinger): a market with a
single scalar discounted excess return `Y` on an arbitrary probability space
`(Ω, 𝓕, P)` has **no arbitrage** iff it admits an **equivalent martingale
measure** — `Q ~ P` with `Y` integrable and `E_Q[Y] = 0`.

This is the step from finite Ω (Rung 2, done) to **genuine measure theory**:
`Y ∈ L⁰` (not bounded, integrability not free), so the proof needs a
bounded-density reduction, a `withDensity` EMM construction, and a.e. reasoning.

## 2. Scope — locked decisions

- **Rung 3 of the FTAP ladder.** One period, **general Ω**. NOT the multi-period
  general-Ω DMW (Rung 4 — that glues one-period *conditional* markets by backward
  induction and needs a measurable selection theorem absent from the pin).
- **Scalar** — one risky asset, `Y : Ω → ℝ`. Parallels the Rung-2 scalar choice.
- **Elementary route** (Föllmer–Schied 1.55), NOT Kreps–Yan: one period means the
  trading position is a scalar `θ ∈ ℝ`, so the only "separation" is the scalar
  sign argument — no L⁰-closedness lemma, no Kreps–Yan separating-measure
  theorem. Confirmed reachable with the pin (recon 2026-06-25).
- **No integrability hypothesis on `Y`.** The theorem holds for `Y ∈ L⁰`; the
  bounded-density reduction (Move 1) supplies integrability internally. This is
  the honest FS-1.55 strength; we do not assume `Y ∈ L¹`.

### Out of scope (named follow-ons)
- **d-asset one-period** — adds finite-dim Hahn–Banach separation of the
  achievable-means set in ℝ^d + a concentrating-measure argument + a redundancy
  reduction (induction on d). The "full" FS 1.55; mechanical-but-larger.
- **General-Ω multi-period DMW** (the crown) — Rung 4; gated on measurable
  selection.

## 3. Coherence with the FTAP family

The repo now has a deliberate FTAP hierarchy; this slots in cleanly:

| result | Ω | periods | direction(s) |
|---|---|---|---|
| `FTAP.emm_implies_no_arbitrage` | any | multi | forward (abstract) |
| `FTAPTwoState` / `FTAPMultiState` | finite | one | both (finite-dim) |
| `FTAPDiscrete.ftap_discrete` (Rung 2) | finite | multi | both |
| **`FTAPOnePeriod` (this, Rung 3)** | **any** | **one** | **both** |
| general-Ω multi-period DMW (Rung 4) | any | multi | — (open) |

Rung 3 is the **general-Ω measure-theoretic foundation**: Rung 4 will glue
one-period *conditional* versions of exactly this result.

## 4. Statement (`MathFin/Foundations/FTAPOnePeriod.lean`, new)

```lean
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  (Y : Ω → ℝ)   -- discounted excess return S₁ − S₀ (scalar; one period, 𝓕₀ trivial)

/-- No scalar position `θ` turns zero wealth into a sure non-loss with a chance
of gain: any `θ` whose discounted gain `θ·Y` is `≥ 0` a.e. has `θ·Y = 0` a.e. -/
def NoArbitrage : Prop :=
  ∀ θ : ℝ, 0 ≤ᵐ[P] (fun ω => θ * Y ω) → (fun ω => θ * Y ω) =ᵐ[P] 0

/-- Equivalent martingale measure: `Q ~ P`, `Y` integrable, `E_Q[Y] = 0`. -/
structure IsEMM (Q : Measure Ω) : Prop where
  prob : IsProbabilityMeasure Q
  absP : Q ≪ P
  Pabs : P ≪ Q
  int  : Integrable Y Q
  fair : ∫ ω, Y ω ∂Q = 0

theorem ftap_one_period (hY : Measurable Y) :
    NoArbitrage P Y ↔ ∃ Q, IsEMM P Y Q
```

The construction (Move 3) actually delivers a **bounded** density (`dQ/dP ∈
L^∞`) — the strong FS form. We keep `IsEMM` minimal — equivalence,
integrability, and fairness (the facts the forward direction consumes) plus
`IsProbabilityMeasure`; bounded density can be an extra exposed lemma if a
consumer needs it (YAGNI for now).

## 5. Forward direction (`EMM ⟹ NA`)

Mirror of Rung 2's forward, now with genuine integrability. Given `Q ~ P`,
`Integrable Y Q`, `E_Q[Y] = 0`, and a `θ` with `θ·Y ≥ 0` a.e.[P]:
`θ·Y ≥ 0` a.e.[Q] (`Q ≪ P`, `AbsolutelyContinuous.ae_le`); `∫ θ·Y dQ = θ·E_Q[Y]
= 0`; a non-negative `Q`-integrable function with zero integral is `0` a.e.[Q]
(`integral_eq_zero_iff_of_nonneg_ae`); back to a.e.[P] (`P ≪ Q`,
`AbsolutelyContinuous.ae_eq`). So `θ·Y = 0` a.e.[P].

**Coherence note (for the values panel / cleanup):** this argument is the scalar
shadow of `FTAP.emm_implies_no_arbitrage` and of Rung 2's `noArbitrage_of_isEMM`.
The genuinely shared kernel is *"`Q ≪≫ P`, `0 ≤ᵐ[P] X`, `E_Q[X] = 0`, `Integrable
X Q` ⟹ `X =ᵐ[P] 0`"*. If the panel agrees it is load-bearing in ≥2 places, extract
it as a named helper (e.g. `Foundations/EMM`-level lemma) and have both forwards
consume it. Decide after the panel verdict; do not pre-emptively refactor
committed Rung-2 code without that signal.

## 6. Backward direction (`NA ⟹ EMM`) — the new general-Ω content, three moves

### Move 1 — bounded-density reduction to L¹
`Y` need not be integrable. Let `g₀ ω := (1 + |Y ω|)⁻¹` (measurable, valued in
`(0,1]`), `c := ∫ g₀ dP ∈ (0,1]`, `g := g₀ / c`, and
`P̃ := P.withDensity (fun ω => ENNReal.ofReal (g ω))`.
- `P̃` is a probability measure (`∫ g dP = 1`) and `P̃ ~ P` (`g > 0`, bounded).
- `Y ∈ L¹(P̃)`: `∫ |Y| dP̃ = ∫ g·|Y| dP = c⁻¹ ∫ |Y|/(1+|Y|) dP ≤ c⁻¹ < ∞`.
- `NoArbitrage P Y ↔ NoArbitrage P̃ Y` (a.e.[P] = a.e.[P̃]); and an EMM for
  `(P̃, Y)` is an EMM for `(P, Y)` (equivalence is transitive; `E_Q[Y]=0`
  unchanged). So **WLOG `Y ∈ L¹` and `P = P̃`** for the rest.

### Move 2 — scalar no-arbitrage dichotomy
Under `NoArbitrage` (and `Y ∈ L¹`): **either** `Y = 0` a.e.[P] (take `Q = P`),
**or** `0 < P{ω | Y ω > 0}` **and** `0 < P{ω | Y ω < 0}`. (If, say, `P{Y<0}=0`
then `Y ≥ 0` a.e.; arbitrage unless `P{Y>0}=0` too — so `θ = ±1` forces the
dichotomy.)

### Move 3 — two-region balancing density
In the non-degenerate case set `a := ∫ Y⁺ dP > 0`, `b := ∫ Y⁻ dP > 0` (finite,
`Y ∈ L¹`; positive by Move 2). Choose `λ, μ > 0` with `λ·a = μ·b` (risk-neutral
balance) and `λ·P{Y ≥ 0} + μ·P{Y < 0} = 1` (normalisation) — explicitly
`μ = (a / (a·P{Y<0} + b·P{Y≥0}))`, `λ = (b/a)·μ` (both `> 0`). Set
`Z := fun ω => if 0 ≤ Y ω then λ else μ` (bounded in `[min,max]`, `> 0`,
measurable) and `Q := P.withDensity (fun ω => ENNReal.ofReal (Z ω))`. Then:
- `IsProbabilityMeasure Q` (`∫ Z dP = 1`); `Q ~ P` (`Z > 0`, bounded);
- `Integrable Y Q` (`Z` bounded, `Y ∈ L¹(P)` — `integrable_withDensity_iff_integrable_smul'`);
- `E_Q[Y] = ∫ Z·Y dP = λ·a − μ·b = 0` (change of measure; `Y⁺/Y⁻` split).

The EMM is `Q` (composed back through Move 1's `P̃ ~ P`). The construction
*re-weights the up-moves and down-moves until `Y` is fair* — the elementary,
constructive heart of the one-period FTAP.

## 7. Mathlib pieces (names confirmed against the pin)

- `MeasureTheory.withDensity`, `withDensity_absolutelyContinuous` (`Q ≪ P`).
- `integral_withDensity_eq_integral_toReal_smul`
  (`…/Integral/Bochner/ContinuousLinearMap.lean`) — `E_Q[X] = ∫ Z·X dP`.
- `integrable_withDensity_iff_integrable_smul'` (`Y ∈ L¹(Q)` from `Z·Y ∈ L¹(P)`).
- `integral_eq_zero_iff_of_nonneg_ae`, `AbsolutelyContinuous.ae_le` / `.ae_eq`,
  `AbsolutelyContinuous.trans` (forward + equivalence plumbing).
- **Derived (small):** `P ≪ Q` when the density `Z > 0` a.e. — not a directly
  named lemma; derive from `withDensity_apply` + `lintegral_eq_zero_iff`
  (`Q s = ∫⁻_s ofReal Z = 0` with `Z > 0` ⟹ `P s = 0`).

No separation kernel for scalar (the balancing density replaces Hahn–Banach);
no new infrastructure.

## 8. Files

- **new** `MathFin/Foundations/FTAPOnePeriod.lean` — `NoArbitrage`, `IsEMM`, the
  bounded-density reduction lemma, the dichotomy, the balancing-density
  construction, forward, backward, `ftap_one_period`. Module header per repo
  rule (`module` + `public import Mathlib` + `@[expose] public section` +
  `namespace MathFin`).
- **edit** `MathFin.lean` umbrella — add the import (re-sync single-file mount /
  restart daemon after editing, per the inode caveat).
- **edit** `MathFin/AxiomAudit.lean` — pin `ftap_one_period` axioms-clean;
  regenerate `AxiomAuditGen.lean`.
- *(conditional)* a shared forward-core lemma file, only if the panel endorses §5.

## 9. Corpus + wiring

- `benchmarks/mathematical_finance.json`: `mf-ftap-one-period-general` (full),
  snippet imports `FTAPOnePeriod` + re-states `ftap_one_period`. `formalization_scope`:
  one period / scalar / **arbitrary Ω** / no integrability assumed; named
  follow-ons (d-asset, general-Ω multi-period).
- Regenerate `axiom_audit_gen --write`; `ledger verify --exec`; pytest;
  `coverage.md` Live-status bump; a `bridges.md` row if one fits.

## 10. Scope honesty (recorded in entry + coverage.md)

One trading period, **one scalar asset**, **arbitrary** `(Ω, P)`, EMM with
bounded density. PROMINENTLY: this is the **one-period** FTAP — the multi-period
general-Ω Dalang–Morton–Willinger theorem (the crown) is NOT proved here and
remains open (gated on measurable selection). Do not let "DMW" / "FTAP" naming
imply the multi-period general case.

## 11. Risks

- **Move 1 (bounded-density reduction)** is the most delicate: the `withDensity`
  normalisation (`c > 0`, `∫ g dP = 1`), transferring `NoArbitrage` across `~P`,
  and composing the final EMM back through `P̃`. Medium.
- **`P ≪ Q` from `Z > 0`** — the one derived measure lemma (§7). Small.
- **Change-of-measure bookkeeping** (`ofReal`/`toReal`, `Y⁺/Y⁻` split as
  `∫ Z·Y = λa − μb`). Mechanical but fiddly.
- Overall medium — more delicate than Rung 2's finite/PMF arithmetic, but every
  ingredient is confirmed in the pin; no gating.

## 12. Values self-review (the eight lenses, applied to this design)

- **Inspired math / first principles:** the EMM is *constructed* from
  no-arbitrage (dichotomy → balancing density), never assumed; the theorem is the
  honest one-period FTAP with no integrability cheat. ✓
- **Mathlib coherence / zero slop:** consumes `withDensity` + change-of-measure +
  `integral_eq_zero_iff_of_nonneg_ae`; no reproving, no over-machinery (scalar ⟹
  no Hahn–Banach). The one self-derived lemma (`P ≪ Q` from `Z>0`) is a genuine
  pin gap, not a wrapper. ✓
- **Architectural ingenuity:** the bounded-density reduction is a clean,
  reusable device; the forward direction flags a possible shared kernel with the
  family (§5) — to confirm via the panel, not force.
- **Idiomatic register / concept clarity:** statement in `=ᵐ[P]` / `Integrable` /
  `withDensity` idiom; scope stated honestly and prominently (§10).
- **Beautiful math:** the construction *re-weights up vs down moves until `Y` is
  fair* — the elementary, visualisable core of the FTAP; the right proof for one
  scalar period (separation would be over-machinery here).

## 13. Acceptance criteria

1. `lake build` green; `FTAPOnePeriod.lean` compiles, no `sorry`/forbidden tactics.
2. `ftap_one_period` axioms-clean (AxiomAudit + regenerated AxiomAuditGen).
3. Corpus entry verifies; `ledger status` all fresh; pytest green.
4. `coverage_report` reflects the new `full` entry; scope wording honest.
5. Values review (8 lenses) — folded into the session-close panel.
