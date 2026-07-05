# Adapted-σ Quadratic Variation (SP1) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the quadratic variation of an adapted-coefficient Itô process, `⟨X⟩ = ∫₀ᵀ σ_s² ds` for **bounded adapted continuous σ**, as a `full` benchmark theorem — the keystone (SP1) of the adapted-coefficient Itô formula.

**Architecture:** A *freezing lemma* replaces each stochastic-integral increment `ΔMₖ = ∫_{tₖ}^{tₖ₊₁} σ dB` by the frozen `σ_{tₖ}·ΔBₖ` (error → 0 in L² via the Itô isometry + σ path-continuity). This reduces the adapted-σ diffusion QV to the **existing** weighted-QV-of-B (`tendsto_weighted_qv_process`, weight `σ²`); the drift² and cross terms die by the **existing** `ItoProcessQV` mechanism (bounds use only the drift Lipschitz constant, not constant σ). Assemble into the headline `tendsto_qv_ito_process_adapted`.

**Tech Stack:** Lean 4 (module system), Mathlib (pinned), Degenne `BrownianMotion`, the MathFin Itô tower (`MathFin/Foundations/`). Verification via the warm `lean-repl` daemon (`./scripts/lean-check.sh`) and the host-side ledger/pytest gates.

> **⚠️ EXECUTION NOTE (2026-07-05).** De-risking Task 1 revealed it is **not** a fiddly single step: the tower represents Itô integrands as `Lp` classes (`trimMeasure_T`) with **no** raw-process realization and **no** sub-interval increment API (see the spec's "Correction" §). So **Task 1 below is really the prerequisite milestone SP0** — (i) `processToLp_of_bdd_adapted_cont` (realize a bounded adapted continuous σ as `φ`), (ii) the CLM sub-interval increment identity — and must land before Tasks 2–5. Meanwhile **Track α** (the simple-process Girsanov path, spec §"Route decision update") is being executed **first** as the faster route to the Girsanov deliverable, since it needs none of SP0. This plan resumes once SP0 is green.

## Lean-proof adaptation of the TDD cycle

This is theorem proving, not app code. Each task's "test" is the Lean compiler:
1. **Write the failing "test"** = state the theorem/lemma with `:= by sorry` (exact signature).
2. **Run to verify it fails** = `./scripts/lean-check.sh <file>` → `success: true, sorry_count ≥ 1` (statement *elaborates*; proof incomplete). A red elaboration (unknown identifier / type error) means the statement itself is wrong — fix before proceeding.
3. **Write the proof** = develop the body **interactively against the daemon**, following the strategy given. Exact statements are pinned here; hard proof bodies are discovered against the daemon and **cannot be pre-written** — the plan gives the strategy + the exact lemmas to consume, not a pre-verified body.
4. **Run to verify it passes** = `./scripts/lean-check.sh <file>` → `sorry_count: 0`.
5. **Commit.**

## Global Constraints

- **Module-system rule:** every `MathFin/` file starts with `module` + `public import`s and puts `@[expose] public section` immediately after the module docstring (else declarations are module-private; enforced by `test_router`).
- **One Lean process locally:** the `lean-repl` daemon is the slot occupant; never run `lake build` / a second env-loading command while it is up (10 GB box OOMs). Final `lake build` runs with the daemon **down**.
- **No forbidden text in `MathFin/` sources:** no `sorry`/`admit`/`native_decide`/`polyrith`/`?`-suggestion tactics/`hammer`/`loogle`/`leansearch` (comments exempt). Committed proofs are `sorry`-free.
- **Axioms-clean:** every headliner theorem's `#print axioms` = `propext, Classical.choice, Quot.sound` only.
- **Ledger:** after any `MathFin/`/benchmark edit, re-verify stale entries via the **warm daemon (no `--exec`)**; corpus-scale `--exec` OOMs the box.
- **Gates:** `pytest tests/test_router.py tests/test_ledger.py tests/test_values.py` = 19/19; `AxiomAuditGen.lean` byte-fresh (`python3 -m tools.verify.axiom_audit_gen --write`) after any benchmark edit.
- **Git:** specific adds only (never `git add -A`/`.`); commit messages carry **no** Claude attribution / Co-Authored-By trailer.
- **Branch:** work on `adapted-ito-formula` (already created; the spec is committed there as `1d9749d`).

## Files

| file | responsibility |
|---|---|
| `MathFin/Foundations/AdaptedStochasticIntegralFreezing.lean` | B1a (per-cell increment identity) + B1 (freezing lemma + weighted defect) |
| `MathFin/Foundations/AdaptedQuadraticVariation.lean` | B2 (diffusion QV → headline `tendsto_qv_ito_process_adapted` + weighted form) |
| `benchmarks/stochastic_calculus.json` | new `full` entry `sc-adapted-qv` re-exporting the headline |
| `MathFin/AxiomAudit.lean` | pin the headline theorem's axioms |
| `MathFin/AxiomAuditGen.lean` | regenerated (byte-fresh) after the benchmark edit |
| `docs/coverage.md`, `docs/bridges.md`, `docs/roadmap.md` | delivery + a Foundations bridge row |

## Notation (used throughout)

Uniform partition of `[0,T]`: `tₖ = unifPart T n k`. `M_t = (∫σ dB)_t` is the `itoProcessCLM` process (`ItoProcessPredictable`); `A_t = ∫₀ᵗ b ds`; `ΔYₖ = Y_{tₖ₊₁} − Y_{tₖ}`. `timeMeasure = ItoIntegralL2.timeMeasure` (Lebesgue on `Ioc 0 T`). Reused, with exact signatures:

- `WeightedQuadraticVariation.tendsto_weighted_qv_process (hB) (hBmeas) {w} (hw_adapt : ∀ s, AdaptedAt B s (w s)) (hw_cont) (hC0 : 0 ≤ C) (hw_bdd : ∀ s ω, |w s ω| ≤ C) (T) : Tendsto (fun n => ∫ ω, (∑ k ∈ range n, w tₖ ω * (B tₖ₊₁ ω − B tₖ ω)^2 − ∫ s in Ioc 0 T, w s ω ∂timeMeasure)^2 ∂μ) atTop (𝓝 0)`.
- `ItoProcessQV.tendsto_qv_ito_process (hB) (hBmeas) (T) {X A X₀ σ Ca} (hCa) (hX : ∀ t ω, X t ω = X₀ ω + A t ω + σ * B t ω) (hA_meas) (hA_lip : ∀ s ≤ t, ∀ ω, |A t ω − A s ω| ≤ Ca*((t:ℝ)−s)) : Tendsto (fun n => ∫ ω, (∑ k, (ΔXₖ)^2 − σ^2*T)^2 ∂μ) atTop (𝓝 0)` — its internals (`ItoProcessQV.qv_bound`, and the private drift²/cross bounds) are the drift-drop pieces to reuse/generalize.
- `ItoIntegralCovariation.covariation_itoIntegralCLM_T (hB) (T) (hBmeas) (φ ψ) : 𝔼_μ[(itoIntegralCLM_T φ)·(itoIntegralCLM_T ψ)] = ∫ φ·ψ d(trim)` — the isometry powering B1's L²-error identity (read the exact `variance_itoIntegralCLM_T` too).
- `itoProcessCLM` / the `φ ● B` process API (`ItoProcessPredictable`) — supplies `M` and its per-cell increments (B1a).

---

### Task 1: B1a — the per-cell increment identity

**Files:**
- Create: `MathFin/Foundations/AdaptedStochasticIntegralFreezing.lean`

**Interfaces:**
- Consumes: `itoProcessCLM` / `φ ● B` and its `[0,t]`-restriction API (`ItoProcessPredictable`); the trim measure `trimMeasure_T`.
- Produces: `itoProcess_increment_eq_subInterval` — the process increment `ΔMₖ = M tₖ₊₁ − M tₖ` equals the sub-interval Itô integral of `σ·𝟙_{(tₖ,tₖ₊₁]}` (as an a.e. identity of `Ω → ℝ` functions). This is the one place the *process* meets *sub-interval* integrals; the fiddliest plumbing (trim/restrict bookkeeping).

- [ ] **Step 1: Scaffold the file** — module header, `@[expose] public section`, `namespace MathFin`, opens matching `ItoProcessPredictable` (`MeasureTheory ProbabilityTheory`, `open scoped NNReal ENNReal`), `variable {Ω mΩ μ B} (hB : IsPreBrownianReal B μ)`, `include hB`. `lean-check` → green (empty body).

- [ ] **Step 2: State `itoProcess_increment_eq_subInterval` with `sorry`.** Read the exact `itoProcessCLM` signature first (`grep -n "def itoProcessCLM\|itoProcessCLM_T" MathFin/Foundations/ItoProcessPredictable.lean` and `ItoIntegralCLM.lean`) and pin the argument order. Statement shape: for bounded adapted continuous `σ` and `s ≤ t ≤ T`, `(itoProcessCLM … t …) − (itoProcessCLM … s …) =ᵐ[μ] itoIntegralCLM over (s,t]` of `σ`. `lean-check` → `sorry_count 1`, `success true` (elaborates).

- [ ] **Step 3: Prove it against the daemon.** Strategy: the CLM is linear and additive over `[0,s] ⊕ (s,t]`; the increment is the integral of `σ` restricted to `(s,t]`. Consume the CLM's additivity/restriction lemmas in `ItoProcessPredictable`/`ItoIntegralCLM`. If no clean restriction lemma exists, this task grows a helper `itoIntegralCLM_restrict_Ioc` (add it here). Develop interactively.

- [ ] **Step 4: `lean-check`** → `sorry_count 0`.

- [ ] **Step 5: Commit.**
```bash
git add MathFin/Foundations/AdaptedStochasticIntegralFreezing.lean
git commit -m "feat(foundations): itoProcessCLM per-cell increment = sub-interval Itô integral (B1a)"
```

---

### Task 2: B1 — the freezing lemma + weighted defect

**Files:**
- Modify: `MathFin/Foundations/AdaptedStochasticIntegralFreezing.lean`

**Interfaces:**
- Consumes: Task 1 `itoProcess_increment_eq_subInterval`; `ItoIntegralCovariation.covariation_itoIntegralCLM_T`/`variance_itoIntegralCLM_T` (isometry); σ path-continuity + boundedness.
- Produces:
  - `sum_freeze_error_tendsto_zero` — `∑ₖ 𝔼[(ΔMₖ − σ_{tₖ}·ΔBₖ)²] → 0`.
  - `weighted_freeze_defect_tendsto_zero` — for bounded adapted continuous `w`, `∫ ω, |∑ₖ w_{tₖ} ((ΔMₖ)² − σ_{tₖ}²(ΔBₖ)²)| ∂μ → 0` (L¹).

- [ ] **Step 1: State `sum_freeze_error_tendsto_zero` with `sorry`.** `lean-check` → `sorry_count 1`.

- [ ] **Step 2: Prove it.** Strategy: `ΔMₖ − σ_{tₖ}ΔBₖ = itoIntegral over (tₖ,tₖ₊₁] of (σ − σ_{tₖ})` (Task 1 + linearity). By the isometry, `𝔼[(·)²] = ∫_{(tₖ,tₖ₊₁]} 𝔼[(σ_s − σ_{tₖ})²] ds`. Sum over `k`: `= ∫_{(0,T]} 𝔼[(σ_s − σ_{s̄(n)})²] ds` where `s̄(n)` is the partition-left-endpoint of `s`. Bounded (`≤ (2Cσ)²`) + path-continuous σ ⟹ integrand → 0 pointwise ⟹ (DCT) → 0. Consume `MeasureTheory.tendsto_integral_of_dominated_convergence`.

- [ ] **Step 3: `lean-check`** → `sorry_count 0`. **Commit** (`feat(foundations): freezing lemma — ΔM ≈ σ·ΔB in L² (B1)`).

- [ ] **Step 4: State `weighted_freeze_defect_tendsto_zero` with `sorry`.** `lean-check` → `sorry_count 1`.

- [ ] **Step 5: Prove it.** Strategy: `(ΔMₖ)² − σ_{tₖ}²(ΔBₖ)² = (ΔMₖ − σ_{tₖ}ΔBₖ)(ΔMₖ + σ_{tₖ}ΔBₖ)`. `∑ₖ |w_{tₖ}|·|·|·|·| ≤ C · (∑(ΔMₖ − σ_{tₖ}ΔBₖ)²)^½ · (∑(ΔMₖ + σ_{tₖ}ΔBₖ)²)^½` (Cauchy–Schwarz over `k`, then over ω). First factor → 0 (Step 2); second factor L²-bounded (isometry: `𝔼[∑(ΔMₖ)²] = 𝔼[∑ ∫σ² ] ≤ Cσ²T`; `𝔼[∑(ΔBₖ)²] = T`). Product → 0 in L¹.

- [ ] **Step 6: `lean-check`** → `sorry_count 0`. **Commit** (`feat(foundations): weighted freezing defect → 0 in L¹ (B1)`).

---

### Task 3: B2-diffusion — the adapted-σ weighted diffusion QV

**Files:**
- Create: `MathFin/Foundations/AdaptedQuadraticVariation.lean`

**Interfaces:**
- Consumes: Task 2 `weighted_freeze_defect_tendsto_zero`; `WeightedQuadraticVariation.tendsto_weighted_qv_process` (weight `wσ²`).
- Produces: `tendsto_weighted_diffusion_qv` — for bounded adapted continuous `w`, `∑ₖ w_{tₖ}(ΔMₖ)² → ∫₀ᵀ w_s σ_s² ds` in L¹ (or L², matching the assembly's needs).

- [ ] **Step 1: Scaffold the file** (module header, `@[expose] public section`, opens, `import MathFin.Foundations.AdaptedStochasticIntegralFreezing` + `WeightedQuadraticVariation`). `lean-check` green.

- [ ] **Step 2: State `tendsto_weighted_diffusion_qv` with `sorry`.** `lean-check` → `sorry_count 1`.

- [ ] **Step 3: Prove it.** Strategy: split `∑w(ΔMₖ)² = ∑w σ_{tₖ}²(ΔBₖ)² + ∑w[(ΔMₖ)² − σ_{tₖ}²(ΔBₖ)²]`. Second sum → 0 (Task 2, `w` bounded absorbs into the defect). First sum: apply `tendsto_weighted_qv_process` with weight `w' := wσ²` (adapted: product of adapted; continuous: product of continuous; bounded: `≤ C·Cσ²`) → `∫ w σ² ds`. Note the mode: `tendsto_weighted_qv_process` gives L² convergence of the *centered square*; downgrade to the L¹ convergence of `∑w σ²(ΔB)² − ∫wσ²` if the assembly consumes L¹ (via `∫|·| ≤ (∫(·)²)^½`).

- [ ] **Step 4: `lean-check`** → `sorry_count 0`. **Commit** (`feat(foundations): adapted-σ weighted diffusion QV via freezing (B2)`).

---

### Task 4: B2-headline — `tendsto_qv_ito_process_adapted`

**Files:**
- Modify: `MathFin/Foundations/AdaptedQuadraticVariation.lean`

**Interfaces:**
- Consumes: Task 3 `tendsto_weighted_diffusion_qv`; `ItoProcessQV.qv_bound` drift²/cross bounds (generalize the private lemmas to the `M`-increment form — they use only `Ca`, `Cσ`, not constant σ); Task 1 for `M`'s increment L²-bound.
- Produces:
  - `tendsto_qv_ito_process_adapted` — the headline: for `X = X₀ + A + M` (`A` Lipschitz drift, `M = ∫σ dB`, σ bounded adapted continuous), `∫ ω, (∑ₖ(ΔXₖ)² − ∫₀ᵀ σ_s² ds)² ∂μ → 0` (`⟨X⟩ = ∫σ²ds`).
  - `tendsto_weighted_qv_ito_process` — the weighted form `∑ w_{tₖ}(ΔXₖ)² → ∫ w σ² ds` (the version SP2's Itô formula consumes, `w = f''(X)`).

- [ ] **Step 1: State both with `sorry`** (headline is the `w ≡ 1` case; state the weighted one and derive the headline, or vice-versa). `lean-check` → `sorry_count 2`.

- [ ] **Step 2: Prove the weighted form.** Strategy: `(ΔXₖ)² = (ΔAₖ)² + 2ΔAₖΔMₖ + (ΔMₖ)²`. `∑w(ΔAₖ)² → 0` (drift²: `|ΔAₖ| ≤ Ca·Δtₖ`, so `≤ C·Ca²·∑Δtₖ² = C·Ca²T²/n → 0`) and `∑w·2ΔAₖΔMₖ → 0` (cross: Cauchy–Schwarz, `∑(ΔAₖ)² → 0` × `∑(ΔMₖ)²` bounded) — reuse/generalize `ItoProcessQV.qv_bound`'s private bounds (they never used σ constant). `∑w(ΔMₖ)² → ∫wσ²ds` is Task 3.

- [ ] **Step 3: Derive the headline** as `w ≡ 1` (constant weight 1 is adapted/continuous/bounded; `∫ 1·σ² = ∫σ²`).

- [ ] **Step 4: `lean-check`** → `sorry_count 0`.

- [ ] **Step 5: Final `lake build` gate** (daemon **down**): `docker compose -f docker/docker-compose.yml down lean-repl` then `docker compose … run --rm verify … lake build` (or the canonical path). Expected: green. Then bring the daemon back up.

- [ ] **Step 6: Commit** (`feat(foundations): ⟨X⟩ = ∫σ²ds for adapted σ — the QV keystone (B2, SP1)`).

---

### Task 5: Benchmark entry + audit + ledger + docs

**Files:**
- Modify: `benchmarks/stochastic_calculus.json` (new entry `sc-adapted-qv`)
- Modify: `MathFin/AxiomAudit.lean`, `MathFin/AxiomAuditGen.lean` (regen)
- Modify: `docs/coverage.md`, `docs/bridges.md`, `docs/roadmap.md`
- Modify: `verification_ledger.json` (re-verify)

**Interfaces:**
- Consumes: Task 4 `tendsto_qv_ito_process_adapted`.
- Produces: a `full` benchmark theorem re-exporting the headline; a ledger row.

- [ ] **Step 1: Add the benchmark entry** `sc-adapted-qv` (domain `stochastic_calculus`, `metadata.formalization_status: "full"`, a `formalization_scope` describing the derivation). The `code.lean` snippet: `import MathFin.Foundations.AdaptedQuadraticVariation` (re-exports Mathlib; **no** `import Mathlib`), then a theorem re-exporting `MathFin.tendsto_qv_ito_process_adapted` with a docstring. Model on the existing `gir-change-of-measure-engine` entry.

- [ ] **Step 2: Verify the snippet** — `./scripts/bench-check.sh benchmarks/stochastic_calculus.json sc-adapted-qv` → `success true, sorry_count 0`.

- [ ] **Step 3: Extend `AxiomAudit.lean`** with a `#guard_msgs`-pinned `#print axioms MathFin.tendsto_qv_ito_process_adapted` (expect the standard 3). Regenerate the exhaustive audit: `python3 -m tools.verify.axiom_audit_gen --write`.

- [ ] **Step 4: Update docs** — `coverage_report` count reconciled (`python3 -m tools.verify.coverage_report`), a `bridges.md` row (constant-coeff → adapted-coeff QV), a `roadmap.md` phase-log line. Do **not** claim the Girsanov architecture row is wired (that is SP3).

- [ ] **Step 5: Gates + ledger.** `python3 -m pytest tests/test_router.py tests/test_ledger.py tests/test_values.py -q` → 19/19. `python3 -m tools.verify.ledger status`; re-verify stale via the warm daemon (no `--exec`), detached if large.

- [ ] **Step 6: Commit** (`feat(bench): adapted-σ quadratic variation as a full entry (SP1)`), specific adds only.

---

## Self-review

- **Spec coverage:** SP1 = spec bricks B1 (Task 2) + B1a (Task 1) + B2 (Tasks 3–4) + benchmark/audit/docs (Task 5). SP2 (B3–B6, the Itô-formula assembly) and SP3 (Girsanov) are **out of scope** here — separate plans, as the spec's §8 phasing requires. ✓
- **Placeholder scan:** proof bodies are intentionally *strategy + consumed-lemmas*, not pre-verified code — this is the domain adaptation stated up front (a research-level Lean proof cannot be pre-written), not a hidden TODO. Every *statement* and every *reused interface* is exact; every step has a concrete `lean-check`/command with expected output.
- **Type consistency:** producer/consumer names match across tasks — `itoProcess_increment_eq_subInterval` (T1) → `sum_freeze_error_tendsto_zero`/`weighted_freeze_defect_tendsto_zero` (T2) → `tendsto_weighted_diffusion_qv` (T3) → `tendsto_weighted_qv_ito_process`/`tendsto_qv_ito_process_adapted` (T4) → `sc-adapted-qv` (T5).
- **Known open API detail:** the exact `itoProcessCLM` increment/restriction signature (Task 1, Step 2) is pinned against `ItoProcessPredictable` at implementation time; if a clean restriction lemma is absent, Task 1 grows the helper `itoIntegralCLM_restrict_Ioc`. Flagged, not hidden.
