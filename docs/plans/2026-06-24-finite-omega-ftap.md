# Finite-Ω multi-period FTAP — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalise `NoArbitrage ↔ ∃ Q, IsEMM Q` for a finite-Ω, finite-horizon, single scalar-asset market (Harrison–Pliska / finite-Ω Dalang–Morton–Willinger), plus the single-period multi-state backward companion.

**Architecture:** One geometric move — no-arbitrage means the attainable-gains subspace `V ⊆ (Ω → ℝ)` misses the standard simplex, so `geometric_hahn_banach_compact_closed` yields a strictly-positive dual functional, which (normalised via `PMF`) is the EMM. The separation is factored into a reusable kernel lemma consumed by both the single-period companion and the multi-period theorem. The forward direction is fresh martingale-transform telescoping.

**Tech Stack:** Lean 4 (toolchain v4.31.0), Mathlib (pin `d6f23da`-era), Degenne BrownianMotion, the repo's `MathFin/Foundations/MartingaleTransform.lean`. Build/verify via Docker (`scripts/lean-check.sh`, full `lake build`); host-side `tools.verify` for ledger/coverage.

## Global Constraints

Copied verbatim from repo rules; every task implicitly includes these.

- **Module header** every new/edited `MathFin/**` file: `module` line, then `public import …`, then a `/-! … -/` docstring, then **`@[expose] public section`**, then `namespace MathFin`. Without `@[expose] public section` declarations are module-private (build stays green, importers break).
- **No forbidden text** in `MathFin/` sources (enforced by `tests/test_values.py`): no `sorry`, `admit`, `native_decide`, `polyrith`, `?`-suggestion tactics (`apply?`/`exact?`/`rw?`), `hammer`, `loogle`, `leansearch`/`leansearch%` (comments exempt).
- **Axioms-clean**: every headline constant pinned in `MathFin/AxiomAudit.lean` with `#guard_msgs`; build-enforced by `build.yml`.
- **Benchmark snippets** that `import MathFin.<Module>` do **not** also `import Mathlib` (the module re-exports it). Each theorem needs `metadata.formalization_status` ∈ {full, library_wrapper, reduced_core, placeholder}; these are `full`.
- After ANY benchmark edit: regenerate `python3 -m tools.verify.axiom_audit_gen --write` (`MathFin/AxiomAuditGen.lean`) and refresh the ledger.
- **Git:** specific `git add <path>` only (never `git add -A`/`.`); commit messages carry **no** `Co-Authored-By`/Claude trailer.
- **Build reality (v4.31):** the lean-interact REPL daemon is unavailable (lean-interact 0.11.4 caps at rc1). Per-file checks use `./scripts/lean-check.sh <file>` (falls back to `lake env lean` in a fresh `verify` container — slow, reliable). Snippet/ledger checks use `python3 -m tools.verify.ledger verify --exec`. One Lean process at a time.
- **Separation space:** work in `Ω → ℝ` (= `ι → ℝ`), the finite-dim normed Pi space, NOT `EuclideanSpace ℝ Ω`. `stdSimplex ℝ ι` is native to `ι → ℝ`; `martingaleTransform φ S T : Ω → ℝ` lands there directly. (Refines the spec's `EuclideanSpace` wording; identical mathematics.)

---

## File Structure

- **Create** `MathFin/Foundations/ConvexSeparation.lean` — the reusable separation kernel `exists_pos_dual_of_disjoint_stdSimplex`. One responsibility: turn "subspace misses the simplex" into "strictly-positive annihilating dual." No finance.
- **Create** `MathFin/Foundations/FTAPDiscrete.lean` — the multi-period model (`NoArbitrage`, `IsEMM`), the attainable-gains subspace, both directions, `ftap_discrete`.
- **Modify** `MathFin/Foundations/FTAPMultiState.lean` — add the single-period backward + biconditional (consumes the kernel); drop the "Phase 42c not formalised" caveat.
- **Modify** `MathFin.lean` — umbrella imports of the two new modules.
- **Modify** `MathFin/AxiomAudit.lean` — pin the new headline constants.
- **Modify** `benchmarks/mathematical_finance.json` — two new `full` entries.
- **Modify** `MathFin/AxiomAuditGen.lean` (generated), `verification_ledger.json` (generated), `docs/coverage.md`.

Dependency order: `ConvexSeparation` → {`FTAPMultiState` (edit), `FTAPDiscrete`} → umbrella/audit/corpus.

---

### Task 1: Separation kernel (`ConvexSeparation.lean`)

**Files:**
- Create: `MathFin/Foundations/ConvexSeparation.lean`

**Interfaces:**
- Produces:
  ```lean
  theorem MathFin.exists_pos_dual_of_disjoint_stdSimplex
      {ι : Type*} [Fintype ι] [Nonempty ι]
      (V : Submodule ℝ (ι → ℝ)) (hV : ∀ v ∈ V, v ∉ stdSimplex ℝ ι) :
      ∃ q : ι → ℝ, (∀ i, 0 < q i) ∧ ∀ v ∈ V, ∑ i, q i * v i = 0
  ```

- [ ] **Step 1: Create the file with header + statement (`sorry` body).**
  Header per Global Constraints. Imports:
  ```lean
  module
  public import Mathlib.Analysis.Convex.StdSimplex
  public import Mathlib.Analysis.LocallyConvex.Separation
  public import Mathlib.Analysis.Normed.Module.FiniteDimension
  ```
  State the theorem above with `:= by sorry`.

- [ ] **Step 2: Prove it.** Strategy (all lemmas confirmed in pin):
  1. `Δ := stdSimplex ℝ ι` is convex (`convex_stdSimplex`), compact (`isCompact_stdSimplex`), nonempty (vertex `Pi.single (Classical.arbitrary ι) 1`, via `ne_empty`/`stdSimplex` membership of a single basis vector).
  2. `(V : Set (ι → ℝ))` is convex (`Submodule.convex`) and closed (`V.closed_of_finiteDimensional`; `ι → ℝ` is `FiniteDimensional ℝ` via `Module.Finite.pi`).
  3. `Disjoint`: `hV` gives `↑V ∩ Δ = ∅`.
  4. `geometric_hahn_banach_compact_closed (convex Δ) (isCompact Δ) (convex V) (closed V) (disjoint)` ⇒ `f : (ι → ℝ) →L[ℝ] ℝ`, `u < v`, `∀ a ∈ Δ, f a < u`, `∀ b ∈ V, v < f b`.
  5. `f` vanishes on `V`: for `b ∈ V` and `c : ℝ`, `c • b ∈ V` so `v < f (c • b) = c * f b`; if `f b ≠ 0`, pick `c` making `c * f b ≤ v` (e.g. `c = (v - 1)/f b` with sign care) — contradiction. Hence `f b = 0`. So `v < 0` and `f a < u ≤ v < 0` on `Δ`.
  6. `q i := - f (Pi.single i 1)`. Each `Pi.single i 1 ∈ Δ` (nonneg, sums to 1) ⇒ `f (Pi.single i 1) < 0` ⇒ `q i > 0`.
  7. Dual annihilation: for `v ∈ V`, `f v = ∑ i, v i * f (Pi.single i 1)` (expand `v = ∑ i, v i • Pi.single i 1` via `Finset.univ_sum_single` / `Pi.basisFun`, then `map_sum`/`map_smul`), and `f v = 0`, so `∑ i, q i * v i = - f v = 0` (reconcile `v i * f(single i 1)` vs `q i * v i` by `q i = -f(single i 1)` and `mul_comm`).

- [ ] **Step 3: Build-check.**
  Run: `./scripts/lean-check.sh MathFin/Foundations/ConvexSeparation.lean`
  Expected: `{"success": true, … "sorry_count": 0}`, no errors.

- [ ] **Step 4: Commit.**
  ```bash
  git add MathFin/Foundations/ConvexSeparation.lean
  git commit -m "feat(foundations): separating-dual kernel for the finite FTAP"
  ```

---

### Task 2: Single-period multi-state backward (`FTAPMultiState.lean`)

**Files:**
- Modify: `MathFin/Foundations/FTAPMultiState.lean`

**Interfaces:**
- Consumes: `exists_pos_dual_of_disjoint_stdSimplex` (Task 1); existing `HasArbitrage_multi_state`, `HasEMM_multi_state`, `noArbitrage_of_emm_multi`.
- Produces:
  ```lean
  theorem MathFin.hasEMM_multi_of_not_hasArbitrage {N M : ℕ} [NeZero N]
      (z : Fin M → Fin N → ℝ) (h : ¬ HasArbitrage_multi_state z) : HasEMM_multi_state z
  theorem MathFin.hasEMM_multi_iff_not_hasArbitrage {N M : ℕ} [NeZero N]
      (z : Fin M → Fin N → ℝ) : HasEMM_multi_state z ↔ ¬ HasArbitrage_multi_state z
  ```

- [ ] **Step 1: Add the import.** Add `public import MathFin.Foundations.ConvexSeparation` to the import block. Re-read the existing `HasArbitrage_multi_state` / `HasEMM_multi_state` definitions in the file to match field names exactly before writing the proof.

- [ ] **Step 2: State both theorems with `sorry`** below the existing `noArbitrage_of_emm_multi`.

- [ ] **Step 3: Prove `hasEMM_multi_of_not_hasArbitrage`.** Strategy:
  - Gains subspace `V := Submodule.span ℝ (Set.range fun m => (z m : Fin N → ℝ))` — the asset payoff vectors. (Portfolio payoff `fun s => ∑ m, θ m * z m s` lies in `V`; `V` = their span.)
  - `¬ HasArbitrage ⇒ ∀ v ∈ V, v ∉ stdSimplex`: a `v ∈ V ∩ stdSimplex` is a payoff (write `v` via `Submodule.span` membership as a combination of `z m`, i.e. some `θ`), nonneg with `∑ = 1 ≠ 0` ⇒ an arbitrage `θ`. Contradiction. (`span_induction` or `mem_span_range_iff_exists_fun` to extract `θ`.)
  - `exists_pos_dual_of_disjoint_stdSimplex V (…) ⇒ q > 0` with `∀ v ∈ V, ∑ s, q s * v s = 0`; apply at `v = z m` (`Submodule.subset_span`) ⇒ `∑ s, q s * z m s = 0 ∀ m`.
  - Normalise `q` to a probability (`Q s := q s / ∑ s, q s`), still strictly positive, summing to 1, with `∑ s, Q s * z m s = 0`. Package as `HasEMM_multi_state` (match its exact fields).

- [ ] **Step 4: Prove `hasEMM_multi_iff_not_hasArbitrage`** := `⟨fun h => noArbitrage_of_emm_multi z h's-contrapositive, hasEMM_multi_of_not_hasArbitrage z⟩`. (Reuse existing forward `noArbitrage_of_emm_multi : HasEMM_multi_state z → ¬ HasArbitrage_multi_state z`.)

- [ ] **Step 5: Update the file docstring** — remove the "backward direction (not formalised — Phase 42c)" caveat; state the biconditional is complete.

- [ ] **Step 6: Build-check.**
  Run: `./scripts/lean-check.sh MathFin/Foundations/FTAPMultiState.lean`
  Expected: success, `sorry_count: 0`.

- [ ] **Step 7: Commit.**
  ```bash
  git add MathFin/Foundations/FTAPMultiState.lean
  git commit -m "feat(foundations): multi-state single-period FTAP backward — completes the biconditional"
  ```

---

### Task 3: Discrete model — defs + gains subspace (`FTAPDiscrete.lean`)

**Files:**
- Create: `MathFin/Foundations/FTAPDiscrete.lean`

**Interfaces:**
- Consumes: `martingaleTransform`, `StronglyAdapted` (from `MartingaleTransform.lean`); Mathlib `Adapted`, `Filtration`, `condExp`.
- Produces (section `variable`s + defs):
  ```lean
  variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {mΩ : MeasurableSpace Ω}
    [MeasurableSingletonClass Ω] (𝓕 : Filtration ℕ mΩ)
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : ∀ ω, 0 < P {ω})
    (S : ℕ → Ω → ℝ) (T : ℕ)

  def NoArbitrage : Prop :=
    ∀ φ : ℕ → Ω → ℝ, StronglyAdapted 𝓕 (fun n => φ (n+1)) →
      0 ≤ᵐ[P] martingaleTransform φ S T → martingaleTransform φ S T =ᵐ[P] 0

  structure IsEMM (Q : Measure Ω) : Prop where
    prob  : IsProbabilityMeasure Q
    absP  : Q ≪ P
    Pabs  : P ≪ Q
    mart  : ∀ t, t < T → S t =ᵐ[Q] Q[S (t+1) | 𝓕 t]

  def incrementIndicator (t : ℕ) (A : Set Ω) : Ω → ℝ :=
    fun ω => A.indicator (fun _ => (1:ℝ)) ω * (S (t+1) ω - S t ω)

  def gainsSubspace : Submodule ℝ (Ω → ℝ) :=
    Submodule.span ℝ { g | ∃ t, t < T ∧ ∃ A, MeasurableSet[𝓕 t] A ∧ g = incrementIndicator S t A }
  ```

- [ ] **Step 1: Create the file** with header, imports (`public import Mathlib`, `public import MathFin.Foundations.ConvexSeparation`, `public import MathFin.Foundations.MartingaleTransform`), `@[expose] public section`, `namespace MathFin`, `open MeasureTheory ProbabilityTheory`. Add the `variable` block and the four defs above. No `sorry` (defs only).

- [ ] **Step 2: Build-check.**
  Run: `./scripts/lean-check.sh MathFin/Foundations/FTAPDiscrete.lean`
  Expected: success, `sorry_count: 0` (defs compile).

- [ ] **Step 3: Commit.**
  ```bash
  git add MathFin/Foundations/FTAPDiscrete.lean
  git commit -m "feat(foundations): discrete FTAP model — NoArbitrage, IsEMM, gains subspace"
  ```

---

### Task 4: Backward direction (`FTAPDiscrete.lean`)

**Files:**
- Modify: `MathFin/Foundations/FTAPDiscrete.lean`

**Interfaces:**
- Consumes: Task 3 defs; `exists_pos_dual_of_disjoint_stdSimplex` (Task 1); `PMF.ofFintype`, `PMF.toMeasure`, `PMF.toMeasure_apply_singleton`, `PMF.integral_eq_sum`; `ae_eq_condExp_of_forall_setIntegral_eq`.
- Produces:
  ```lean
  theorem exists_isEMM_of_noArbitrage
      (hS : Adapted 𝓕 S) (hNA : NoArbitrage 𝓕 P S T) : ∃ Q, IsEMM 𝓕 P S T Q
  ```

- [ ] **Step 1: Helper `mem_gains_imp_predictable`** (with `sorry`, then prove):
  ```lean
  theorem mem_gains_imp_predictable {g : Ω → ℝ} (hg : g ∈ gainsSubspace S T) :
      ∃ φ, StronglyAdapted 𝓕 (fun n => φ (n+1)) ∧
           (fun ω => martingaleTransform φ S T ω) = g
  ```
  Proof by `Submodule.span_induction`: generator `incrementIndicator S t A` (with `A ∈ 𝓕 t`) is the gains of `φ = fun s => if s = t+1 then A.indicator (fun _ => 1) else 0` (predictable: `φ (n+1)` is `0` or `𝟙_A` with `A ∈ 𝓕 n`; `martingaleTransform … T = 𝟙_A (S (t+1) - S t)` since only the `s=t` term survives, needs `t < T`); closure under `+`/`smul`/`0` assembles `φ₁+φ₂`, `c•φ`, `0`. Uses linearity of `martingaleTransform` in its first argument (prove/inline `martingaleTransform_add`, `martingaleTransform_smul` if not already present).

- [ ] **Step 2: Disjointness `noArb_imp_disjoint`** (with `sorry`, then prove):
  ```lean
  theorem gains_disjoint_stdSimplex (hNA : NoArbitrage 𝓕 P S T) :
      ∀ v ∈ gainsSubspace S T, v ∉ stdSimplex ℝ Ω
  ```
  Proof: suppose `v ∈ gains ∩ stdSimplex`. `mem_gains_imp_predictable` ⇒ predictable `φ` with `martingaleTransform φ S T = v`. `v ∈ stdSimplex` ⇒ `0 ≤ v` (so `0 ≤ᵐ[P]`) and `∑ v = 1` ⇒ `v ≠ 0` ⇒ `martingaleTransform φ S T ≠ᵐ[P] 0` (full support `hP`: some `ω` has `v ω > 0`, `P{ω} > 0`). Contradicts `hNA φ … (0 ≤ᵐ) ⇒ (=ᵐ 0)`.

- [ ] **Step 3: Main backward theorem** (with `sorry`, then prove). Strategy:
  - `obtain ⟨q, hq_pos, hq_dual⟩ := exists_pos_dual_of_disjoint_stdSimplex (gainsSubspace S T) (gains_disjoint_stdSimplex hNA)`.
  - `Z := ∑ ω, q ω` (`> 0`); `Q := (PMF.ofFintype (fun ω => ⟨q ω / Z, _⟩) _).toMeasure` (masses `q ω / Z`, nonneg, sum 1). `IsProbabilityMeasure Q` from `PMF.toMeasure`.
  - `Q {ω} = q ω / Z > 0` (`PMF.toMeasure_apply_singleton`) ⇒ `Q ≪ P` and `P ≪ Q` (both: a null set has all singletons null ⇒ empty, on finite Ω with strictly-positive masses; use `hP` for `P ≪ Q`).
  - Martingale: fix `t < T`, `A ∈ 𝓕 t`. `incrementIndicator S t A ∈ gainsSubspace` (`Submodule.subset_span`), so `hq_dual` gives `∑ ω, q ω * incrementIndicator S t A ω = 0`, i.e. `∑ ω, q ω * 𝟙_A ω * (S (t+1) - S t) ω = 0`. Divide by `Z` and rewrite as `∫ ω, 𝟙_A ω * (S (t+1) - S t) ω ∂Q = 0` (`PMF.integral_eq_sum`), i.e. `∫ A, (S (t+1) - S t) ∂Q = 0`, i.e. `∫ A, S (t+1) ∂Q = ∫ A, S t ∂Q`. Then `ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le t)` (with `S t` `𝓕 t`-measurable from `hS`, integrability free on Fintype) ⇒ `S t =ᵐ[Q] Q[S (t+1) | 𝓕 t]`.
  - Assemble `⟨Q, ⟨prob, absP, Pabs, mart⟩⟩`.

- [ ] **Step 4: Build-check.**
  Run: `./scripts/lean-check.sh MathFin/Foundations/FTAPDiscrete.lean`
  Expected: success, `sorry_count: 0`.

- [ ] **Step 5: Commit.**
  ```bash
  git add MathFin/Foundations/FTAPDiscrete.lean
  git commit -m "feat(foundations): discrete FTAP backward — NA ⇒ ∃ EMM via separation"
  ```

---

### Task 5: Forward direction (`FTAPDiscrete.lean`)

**Files:**
- Modify: `MathFin/Foundations/FTAPDiscrete.lean`

**Interfaces:**
- Consumes: Task 3 defs; `condExp_mul_of_stronglyMeasurable_left`, `integral_condExp`, `integral_eq_zero_iff_of_nonneg_ae`.
- Produces:
  ```lean
  theorem noArbitrage_of_isEMM (hS : Adapted 𝓕 S)
      {Q : Measure Ω} (hQ : IsEMM 𝓕 P S T Q) : NoArbitrage 𝓕 P S T
  ```

- [ ] **Step 1: State with `sorry`.**

- [ ] **Step 2: Prove.** Strategy (intro `φ`, `hφ` predictable, `hpos : 0 ≤ᵐ[P] G T` where `G := martingaleTransform φ S`):
  - One-step: for `t < T`, `Q[G (t+1) - G t | 𝓕 t] = Q[φ (t+1) * (S (t+1) - S t) | 𝓕 t] = φ (t+1) * Q[(S (t+1) - S t) | 𝓕 t] = 0` — pull out `𝓕 t`-measurable `φ (t+1)` (`condExp_mul_of_stronglyMeasurable_left`, finite measure), and `Q[S (t+1) - S t | 𝓕 t] = Q[S (t+1)|𝓕 t] - S t = 0` from `hQ.mart` (with `S t` `𝓕 t`-measurable: `condExp` of an adapted term is itself).
  - Telescoping ⇒ `∫ G T ∂Q = ∫ G 0 ∂Q = 0` (`G 0 = 0`; integrate the conditional increments via `integral_condExp`).
  - `hpos` and `P ≪ Q` (`hQ.Pabs`) ⇒ `0 ≤ᵐ[Q] G T`; with `∫ G T ∂Q = 0`, `integral_eq_zero_iff_of_nonneg_ae` ⇒ `G T =ᵐ[Q] 0`; then `Q ≪ P`… wait need `=ᵐ[P]`: use `hQ.absP`? `G T =ᵐ[Q] 0` and `P ≪ Q` ⇒ `G T =ᵐ[P] 0`. Conclude `NoArbitrage`.

- [ ] **Step 3: Build-check.**
  Run: `./scripts/lean-check.sh MathFin/Foundations/FTAPDiscrete.lean`
  Expected: success, `sorry_count: 0`.

- [ ] **Step 4: Commit.**
  ```bash
  git add MathFin/Foundations/FTAPDiscrete.lean
  git commit -m "feat(foundations): discrete FTAP forward — EMM ⇒ NA via transform telescoping"
  ```

---

### Task 6: The biconditional (`FTAPDiscrete.lean`)

**Files:**
- Modify: `MathFin/Foundations/FTAPDiscrete.lean`

**Interfaces:**
- Produces:
  ```lean
  theorem ftap_discrete (hS : Adapted 𝓕 S) :
      NoArbitrage 𝓕 P S T ↔ ∃ Q, IsEMM 𝓕 P S T Q
  ```

- [ ] **Step 1: Prove** := `⟨exists_isEMM_of_noArbitrage … hS, fun ⟨Q, hQ⟩ => noArbitrage_of_isEMM … hS hQ⟩`. Update the module docstring to state the theorem + honest scope (finite Ω, scalar, finite T; general-Ω / d-asset are out of scope).

- [ ] **Step 2: Build-check.**
  Run: `./scripts/lean-check.sh MathFin/Foundations/FTAPDiscrete.lean`
  Expected: success, `sorry_count: 0`.

- [ ] **Step 3: `#print axioms` sanity** (inside the file, temporary): add `#print axioms ftap_discrete` and confirm only `propext/Classical.choice/Quot.sound`; remove the line before commit.

- [ ] **Step 4: Commit.**
  ```bash
  git add MathFin/Foundations/FTAPDiscrete.lean
  git commit -m "feat(foundations): assemble ftap_discrete biconditional (finite-Ω Harrison–Pliska)"
  ```

---

### Task 7: Wiring — umbrella, AxiomAudit, corpus, ledger, coverage

**Files:**
- Modify: `MathFin.lean`, `MathFin/AxiomAudit.lean`, `benchmarks/mathematical_finance.json`, `MathFin/AxiomAuditGen.lean` (generated), `verification_ledger.json` (generated), `docs/coverage.md`.

- [ ] **Step 1: Umbrella imports.** Add to `MathFin.lean`:
  ```
  import MathFin.Foundations.ConvexSeparation
  import MathFin.Foundations.FTAPDiscrete
  ```
  (`FTAPMultiState` already imported.) **Re-sync the single-file bind mount** after editing (`docker exec -i docker-lean-repl-1 sh -c 'cat > /app/MathFin.lean' < MathFin.lean`) or restart the service — single-FILE mounts pin the inode.

- [ ] **Step 2: AxiomAudit pins.** Add to `MathFin/AxiomAudit.lean` the `#guard_msgs`-wrapped `#print axioms` for `MathFin.ftap_discrete`, `MathFin.hasEMM_multi_iff_not_hasArbitrage`, `MathFin.exists_pos_dual_of_disjoint_stdSimplex` (match the file's existing pin idiom).

- [ ] **Step 3: Corpus entries.** Add to `benchmarks/mathematical_finance.json`:
  - `mf-ftap-discrete-complete` — `domain: mathematical_finance`, `formalization_status: full`, snippet `import MathFin.Foundations.FTAPDiscrete` + re-state `ftap_discrete` (5–25 lines, no `import Mathlib`). `metadata.formalization_scope`: finite Ω / scalar / finite-T; named open follow-ons.
  - `mf-ftap-single-period-complete` — re-state `hasEMM_multi_iff_not_hasArbitrage`, `full`.

- [ ] **Step 4: Regenerate generated artifacts.**
  ```bash
  python3 -m tools.verify.axiom_audit_gen --write
  ```

- [ ] **Step 5: Full build gate.**
  Run (daemon down, one Lean process): a full `lake build` via the verify container, e.g.
  `docker compose -f docker/docker-compose.yml run --rm --entrypoint sh verify -c 'lake build'`
  Expected: completes green (no errors, no `sorry`).

- [ ] **Step 6: Ledger + coverage + tests.**
  ```bash
  python3 -m tools.verify.ledger status            # expect all fresh after verify
  python3 -m tools.verify.ledger verify --exec     # re-verify the two new (and any restaled) entries
  python3 -m tools.verify.coverage_report          # confirm +2 full
  docker compose -f docker/docker-compose.yml run --rm --entrypoint python3 verify -m pytest tests/ -q
  ```
  Update `docs/coverage.md` (two new `full`, scope wording).

- [ ] **Step 7: Commit.**
  ```bash
  git add MathFin.lean MathFin/AxiomAudit.lean MathFin/AxiomAuditGen.lean \
          benchmarks/mathematical_finance.json verification_ledger.json docs/coverage.md
  git commit -m "feat(corpus): wire finite-Ω FTAP — 2 full entries, audit + ledger green"
  ```

---

## Self-Review

**Spec coverage:**
- §4 statement (`NoArbitrage`, `IsEMM`, `ftap_discrete`) → Tasks 3, 6. ✓
- §5 backward (gains subspace, disjointness, separation, PMF, condExp) → Tasks 1, 4. ✓
- §5 forward (telescoping) → Task 5. ✓
- §7 single-period companion → Task 2. ✓
- §8 files (FTAPDiscrete, FTAPMultiState, umbrella, AxiomAudit) → Tasks 3–7. ✓
- §9 corpus/ledger/coverage/tests → Task 7. ✓
- §6 Mathlib lemmas → referenced in the consuming tasks. ✓
- ConvexSeparation kernel (implied by §5 but not a named spec file) → Task 1 (a clean factor; both consumers use it). ✓

**Placeholder scan:** Proof bodies are strategy + exact lemma names (honest for Lean — tactic bodies are elaborator-developed), statements are exact. No "TBD"/"handle edge cases"/"similar to". ✓

**Type consistency:** `martingaleTransform φ S T : Ω → ℝ` used consistently; `gainsSubspace S T : Submodule ℝ (Ω → ℝ)` matches the kernel's `V : Submodule ℝ (ι → ℝ)` at `ι = Ω`; `IsEMM` field names (`prob/absP/Pabs/mart`) referenced consistently in Tasks 4–6; `exists_pos_dual_of_disjoint_stdSimplex` signature identical at definition (Task 1) and uses (Tasks 2, 4). ✓
