# One-period general-Ω FTAP (scalar) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans. Steps use checkbox (`- [ ]`) syntax.

**Goal:** `ftap_one_period : NoArbitrage P Y ↔ ∃ Q, IsEMM P Y Q` — for a single scalar discounted excess return `Y` on an arbitrary probability space `(Ω, P)`, no arbitrage ⟺ ∃ equivalent martingale measure with `E_Q[Y]=0`.

**Architecture:** Elementary Föllmer–Schied 1.55. Forward = a.e. + change-of-measure. Backward, built incrementally: first the **integrable** case (scalar dichotomy → two-region balancing density `Z = λ·𝟙_{Y≥0} + μ·𝟙_{Y<0}`), then drop the integrability hypothesis via a **bounded-density reduction** `P̃ = P.withDensity (c/(1+|Y|))`. No Hahn–Banach (scalar), no Kreps–Yan.

**Tech Stack:** Lean 4 (v4.31.0), Mathlib (`withDensity` + change-of-measure + integration). New file imports `Mathlib` only (no MathFin deps), so `lean-check` works directly against the daemon without umbrella wiring.

## Global Constraints

- Module header: `module` / `public import Mathlib` / `/-! … -/` docstring / `@[expose] public section` / `namespace MathFin`.
- No `sorry`/`admit`/`native_decide`/`polyrith`/`?`-tactics/`hammer`/`loogle`/`leansearch` in `MathFin/` (comments exempt).
- Axioms-clean (AxiomAudit `#guard_msgs`); regenerate `AxiomAuditGen` after benchmark edits.
- Benchmark snippet imports the module (no extra `import Mathlib`); `formalization_status: full`.
- Git: specific adds only; no `Co-Authored-By`/Claude trailer.
- Build = test: per-file `./scripts/lean-check.sh <file>` (warm daemon ~8s); green ⇒ `{"success": true, "sorry_count": 0}`, no warnings. Final `lake build` gate via daemon restart.
- Honest scope (docstrings + corpus): one period, **one scalar asset**, arbitrary Ω, no integrability assumed; general-Ω **multi-period** DMW + d-asset are named open follow-ons.

---

## File Structure

- **Create** `MathFin/Foundations/FTAPOnePeriod.lean` — defs, forward, backward (integrable case → general case), biconditional. One file, self-contained.
- **Modify** `MathFin.lean`, `MathFin/AxiomAudit.lean`, `benchmarks/mathematical_finance.json`, generated `AxiomAuditGen.lean` + `verification_ledger.json`, `docs/coverage.md`.

---

### Task 1: Model defs + scaffold

**Files:** Create `MathFin/Foundations/FTAPOnePeriod.lean`

**Produces:**
```lean
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)

def NoArbitrage : Prop :=
  ∀ θ : ℝ, 0 ≤ᵐ[P] (fun ω => θ * Y ω) → (fun ω => θ * Y ω) =ᵐ[P] 0

structure IsEMM (Q : Measure Ω) : Prop where
  prob : IsProbabilityMeasure Q
  absP : Q ≪ P
  Pabs : P ≪ Q
  int  : Integrable Y Q
  fair : ∫ ω, Y ω ∂Q = 0
```

- [ ] **Step 1:** Write the header, `open MeasureTheory`, the `variable` block, and the two defs above. Module docstring states the theorem + honest scope.
- [ ] **Step 2:** `./scripts/lean-check.sh MathFin/Foundations/FTAPOnePeriod.lean` → `success: true, sorry_count: 0`.
- [ ] **Step 3:** Commit `feat(foundations): one-period FTAP model — NoArbitrage, IsEMM`.

---

### Task 2: Forward direction (`EMM ⟹ NA`)

**Files:** Modify `FTAPOnePeriod.lean`

**Produces:** `theorem noArbitrage_of_isEMM {Q : Measure Ω} (hQ : IsEMM P Y Q) : NoArbitrage P Y`

- [ ] **Step 1:** State it. Strategy: `intro θ hpos`. `θ·Y ≥ 0` a.e.[P] ⟹ a.e.[Q] (`hQ.absP.ae_le hpos`). `∫ θ·Y ∂Q = θ * ∫ Y ∂Q = θ * 0 = 0` (`integral_mul_left` / `integral_const_mul` + `hQ.fair`; needs `Integrable Y Q = hQ.int`). Then `θ·Y =ᵐ[Q] 0` (`integral_eq_zero_iff_of_nonneg_ae` with `0 ≤ᵐ[Q] θ·Y` and `Integrable (θ·Y) Q = hQ.int.const_mul θ`). Transport to a.e.[P] via `hQ.Pabs.ae_eq`.
- [ ] **Step 2:** `lean-check` → green.
- [ ] **Step 3:** Commit `feat(foundations): one-period FTAP forward — EMM ⇒ NA`.

---

### Task 3: Balancing-density EMM (the integrable, non-degenerate core)

**Files:** Modify `FTAPOnePeriod.lean`

**Produces:**
```lean
theorem exists_isEMM_of_pos_tails (hY : Measurable Y) (hYint : Integrable Y P)
    (ha : 0 < ∫ ω, max (Y ω) 0 ∂P) (hb : 0 < ∫ ω, max (- Y ω) 0 ∂P) :
    ∃ Q, IsEMM P Y Q
```

- [ ] **Step 1:** State it. Let `a := ∫ max Y 0 ∂P` (=`E[Y⁺]`), `b := ∫ max (-Y) 0 ∂P` (=`E[Y⁻]`), both `> 0` (hyps), finite (`hYint`, `Integrable.max_zero`). Set `pp := P {ω | 0 ≤ Y ω}`, `pn := P {ω | Y ω < 0}` (`pp + pn = 1`). Pick `μ := a / (a*pn.toReal + b*pp.toReal)`, `λ := (b/a)*μ` — both `> 0`. Density `Z := fun ω => if 0 ≤ Y ω then λ else μ` (measurable: `hY` + `measurableSet_le`; bounded; `> 0`).
- [ ] **Step 2:** `Q := P.withDensity (fun ω => ENNReal.ofReal (Z ω))`. Prove `∫ Z ∂P = 1` (split `{Y≥0}`/`{Y<0}`, `setIntegral_const`, `λ*pp + μ*pn = 1` by the choice of λ,μ) ⟹ `IsProbabilityMeasure Q` (`isProbabilityMeasure_withDensity` / from `withDensity` of a density integrating to 1). `Q ≪ P` (`withDensity_absolutelyContinuous`); `P ≪ Q` (small lemma: `Z > 0` a.e. ⟹ reverse AC, via `withDensity_apply` + `lintegral_eq_zero_iff`).
- [ ] **Step 3:** `Integrable Y Q` (`integrable_withDensity_iff_integrable_smul'` — `Z·Y ∈ L¹(P)` since `Z` bounded + `hYint`). `E_Q[Y] = ∫ (Z·Y) ∂P` (`integral_withDensity_eq_integral_toReal_smul`) `= λ·∫_{Y≥0} Y + μ·∫_{Y<0} Y = λ·a − μ·b = 0` (split + `λa = μb`).
- [ ] **Step 4:** `lean-check` → green. (Expect this to be the most iteration — the `withDensity`/`setIntegral` split bookkeeping.)
- [ ] **Step 5:** Commit `feat(foundations): one-period FTAP — balancing-density EMM (integrable core)`.

---

### Task 4: Scalar dichotomy + integrable backward

**Files:** Modify `FTAPOnePeriod.lean`

**Produces:** `theorem exists_isEMM_of_noArbitrage_integrable (hY : Measurable Y) (hYint : Integrable Y P) (hNA : NoArbitrage P Y) : ∃ Q, IsEMM P Y Q`

- [ ] **Step 1:** Dichotomy: under `hNA`, either `Y =ᵐ[P] 0`, or `0 < ∫ max Y 0` and `0 < ∫ max (-Y) 0`. Proof: if `∫ max Y 0 = 0` then `max Y 0 =ᵐ 0` (`integral_eq_zero_iff_of_nonneg_ae`, `max ≥ 0`) so `Y ≤ᵐ 0`; symmetric for `∫ max (-Y) 0 = 0` ⟹ `Y ≥ᵐ 0`. If `Y ≥ᵐ 0` with `∫ max Y 0 > 0` (i.e. not `Y ≤ᵐ 0`), then `θ=1` is an arbitrage (`0 ≤ᵐ Y`, not `=ᵐ 0`) — contradicts `hNA`. So `hNA` forces `(∫max Y 0 = 0 ∧ ∫max(-Y)0 = 0)` (⟹ `Y=ᵐ0`) or both `> 0`.
- [ ] **Step 2:** Degenerate `Y =ᵐ[P] 0`: `Q := P` is the EMM (`Integrable Y P = hYint`; `∫ Y ∂P = 0` from `Y =ᵐ 0`; `P ≪ P`).
- [ ] **Step 3:** Non-degenerate: `exists_isEMM_of_pos_tails hY hYint ha hb`.
- [ ] **Step 4:** `lean-check` → green. Commit `feat(foundations): one-period FTAP — scalar dichotomy + integrable backward`.

---

### Task 5: Bounded-density reduction + general backward

**Files:** Modify `FTAPOnePeriod.lean`

**Produces:** `theorem exists_isEMM_of_noArbitrage (hY : Measurable Y) (hNA : NoArbitrage P Y) : ∃ Q, IsEMM P Y Q`

- [ ] **Step 1:** `g₀ := fun ω => (1 + |Y ω|)⁻¹` (measurable, `∈ (0,1]`); `c := ∫ g₀ ∂P ∈ (0,1]`; `P̃ := P.withDensity (fun ω => ENNReal.ofReal (g₀ ω / c))`. Prove `P̃` is a probability measure (`∫ g₀/c = 1`), `P̃ ~ P` (`g₀/c > 0` bounded). `Y ∈ L¹(P̃)`: `∫ |Y| ∂P̃ = c⁻¹ ∫ |Y|·g₀ ∂P ≤ c⁻¹ < ∞` (`|Y|/(1+|Y|) ≤ 1`).
- [ ] **Step 2:** `NoArbitrage P̃ Y` from `NoArbitrage P Y` (a.e.[P] = a.e.[P̃] since `P̃ ~ P`: `hP̃P.ae_le`/`.ae_eq` both ways).
- [ ] **Step 3:** `obtain ⟨Q, hQ⟩ := exists_isEMM_of_noArbitrage_integrable hY hYint̃ hNÃ` (EMM for `(P̃, Y)`). Lift: `Q ~ P̃ ~ P` (`AbsolutelyContinuous.trans` both directions); `E_Q[Y] = 0` and `Integrable Y Q` unchanged. So `IsEMM P Y Q`.
- [ ] **Step 4:** `lean-check` → green. Commit `feat(foundations): one-period FTAP backward — NA ⇒ ∃ EMM (general Y, no integrability)`.

---

### Task 6: Biconditional

**Files:** Modify `FTAPOnePeriod.lean`

**Produces:** `theorem ftap_one_period (hY : Measurable Y) : NoArbitrage P Y ↔ ∃ Q, IsEMM P Y Q`

- [ ] **Step 1:** `⟨fun hNA => exists_isEMM_of_noArbitrage P Y hY hNA, fun ⟨_, hQ⟩ => noArbitrage_of_isEMM P Y hQ⟩`. Module docstring final scope note.
- [ ] **Step 2:** Add temporary `#print axioms MathFin.ftap_one_period`; confirm `[propext, Classical.choice, Quot.sound]`; remove the line.
- [ ] **Step 3:** `lean-check` → green. Commit `feat(foundations): assemble ftap_one_period (one-period general-Ω FTAP)`.

---

### Task 7: Wiring

**Files:** `MathFin.lean`, `MathFin/AxiomAudit.lean`, `benchmarks/mathematical_finance.json`, generated files, `docs/coverage.md`

- [ ] **Step 1:** Add `import MathFin.Foundations.FTAPOnePeriod` to `MathFin.lean` (re-sync the single-file mount / restart daemon per the inode caveat).
- [ ] **Step 2:** AxiomAudit pin for `MathFin.ftap_one_period` (`#guard_msgs (whitespace := lax) in #print axioms …`).
- [ ] **Step 3:** Corpus entry `mf-ftap-one-period-general` (`full`): import `FTAPOnePeriod`, re-state `ftap_one_period`; `formalization_scope` = one period / scalar / arbitrary Ω / no integrability assumed + named open follow-ons.
- [ ] **Step 4:** `python3 -m tools.verify.axiom_audit_gen --write`.
- [ ] **Step 5:** Full build via daemon restart (gen-N); confirm READY (green). `ledger verify` the new entry; `ledger status` all fresh.
- [ ] **Step 6:** `pytest tests/ -q` green; update `docs/coverage.md` Live-status (corpus → 288, full → 253).
- [ ] **Step 7:** Commit `feat(corpus): wire one-period general-Ω FTAP — full entry, audit + ledger green`.

---

## Self-Review

**Spec coverage:** §4 statement → T1,T6; §5 forward → T2; §6 backward Move 3 → T3, Move 2 → T4, Move 1 → T5; §7 Mathlib pieces → cited in consuming tasks; §8 files / §9 corpus → T1–T7; §10 scope honesty → T1/T6 docstrings + T3 corpus. ✓ (The integrable-case checkpoint T3+T4 delivers a complete theorem even if T5's reduction proves hard — incremental safety.)

**Placeholder scan:** statements exact; proof bodies are strategy + confirmed Mathlib lemma names (Lean-honest — tactics developed against the daemon). No "TBD"/"handle edge cases". ✓

**Type consistency:** `NoArbitrage P Y`, `IsEMM P Y Q` (fields `prob/absP/Pabs/int/fair`), `exists_isEMM_of_pos_tails` → `…_integrable` → `…_of_noArbitrage` → `ftap_one_period` chain consistent; `a := ∫ max Y 0`, `b := ∫ max (-Y) 0` used consistently in T3/T4. ✓
