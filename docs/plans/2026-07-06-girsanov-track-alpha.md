# Girsanov Track-α: simple → continuous bounded-adapted-θ (SP3-α) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: superpowers:executing-plans. Multi-session; land each brick green before the next. Supersedes the on-disk Track-β plan (`2026-07-05-adapted-ito-formula-sp1.md`) as the path to closing `gir-thm-9.1.8`; that plan (general adapted Itô formula) stays as backlog for SDEs/Feynman–Kac.

**Goal:** Close `gir-thm-9.1.8` (`reduced_core → full`) for **general bounded adapted θ**: under `Q = P.withDensity(Doléans exp)`, `B^θ_t = X_t + ∫₀ᵗ θ_s ds` is a Q-Brownian motion — via the **characteristic-function route** (NOT Lévy, which Mathlib lacks; NOT the adapted Itô formula, which the tower lacks), reusing the constant-θ apparatus in `GirsanovConstantTheta.lean`.

**Architecture (the spine).** For a partition `0 = s₀ ≤ … ≤ s_m = T` and **𝓕-adapted bounded** multipliers `d : Fin m → Ω → ℝ` (`dᵢ` is `𝓕_{sᵢ}`-measurable), define the running **simple Doléans exponential**
`E^d_t = exp( Σᵢ dᵢ·(X_{sᵢ₊₁∧t} − X_{sᵢ∧t}) − ½ Σᵢ dᵢ²·(sᵢ₊₁∧t − sᵢ∧t) )`.
The linchpin algebraic identity (verified by hand):
`E^{−c}_t · exp(a·B^θ_t − ½a²t) = E^{a−c}_t`  (per-cell exponent `(a−cᵢ)ΔXᵢ − ½(a−cᵢ)²Δsᵢ`),
i.e. `Z·D` is *another* simple Doléans exponential — **exactly** the trick powering the constant-θ file (`Z = Wald(−θ)`, `Z·D = Wald(a−θ)`). So once **`E^d` is a P-martingale**, the entire constant-θ chain (`expBtheta_isQMartingale → condExp_expBtheta → condExp_Btheta_increment → Btheta_increment_mgf → Btheta_increments_joint_mgf → Btheta_linComb_map_eq_gaussianReal → Btheta_increments_indepFun → Btheta_isQBrownianMotion`) lifts to simple θ by replacing `Wald(α)` with `E^d`.

**Tech Stack:** Lean 4 (module system), Mathlib v4.31.0 pin, Degenne `BrownianMotion`, the MathFin tower. Verify via the warm `lean-repl` daemon (`./scripts/lean-check.sh`); final `lake build` daemon-down.

## Global Constraints
- Module-system rule: `module` + `public import`s, `@[expose] public section` after the docstring.
- One Lean process locally (daemon is the slot; `lake build` only daemon-down; 10 GB box).
- No forbidden text in `MathFin/` (sorry/admit/native_decide/polyrith/?-tactics/hammer/loogle/leansearch — comments exempt). Committed proofs sorry-free.
- Axioms-clean headliners (`propext, Classical.choice, Quot.sound`).
- Ledger re-verify via warm daemon (no `--exec`); gates `pytest test_router/test_ledger/test_values` 19/19; `AxiomAuditGen.lean` byte-fresh after any benchmark edit.
- Git: specific adds only; **no** Claude attribution / Co-Authored-By trailer.
- Branch: `girsanov-track-alpha` (create off `main`).

## Brick sequence (one coherent green milestone per session)

### Brick α1 — conditional single-cell Wald with a **random adapted multiplier** ✅ DONE (2026-07-06)
`MathFin/Foundations/SimpleDoleansExponential.lean` (new). The one genuinely new estimate.
**Status: LANDED green + axioms-clean** (`condExp_exp_adapted_mul_increment`, commit `55242cf`). The
freezing went through the joint-law factorization of `(c, 𝟙_A)` against the independent increment
(`indep_of_indep_of_le_right` + `indepFun_iff_map_prod_eq_prod_map_map`) then `integral_prod`. Reusable
private helper `condExp_exp_adapted_freeze_setIntegral` (general in `Δ, v`).
**Statement.** For `c : Ω → ℝ` with `StronglyMeasurable[𝓕 r] c`, `∀ ω, |c ω| ≤ K`, and `r ≤ t`:
`P[fun ω ↦ exp(c ω · (X t ω − X r ω)) | 𝓕 r] =ᵐ[P] fun ω ↦ exp(½·(c ω)²·(t − r))`
(equivalently the normalized `exp(cΔ − ½c²(t−r))` has `condExp = 1`).
**Proof.** `ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le r)`: RHS is `𝓕_r`-measurable (✓, `c` is); LHS integrable (bounded `c` + increment Gaussian-MGF, AM–GM domination as in `condExp_Btheta_increment`); for `A ∈ 𝓕_r`, `∫_A exp(cΔ) = ∫_A exp(½c²(t−r))`. The set-integral equality is the **freezing**: `Δ = X_t − X_r ⊥ 𝓕_r` (`hX.indep`), so the joint law of `Y := (A.indicator 1, c) ⊔`… factorizes — `P.map (fun ω ↦ (c ω, Δ ω)) = (P.map c).prod (P.map Δ)` (`IndepFun.map_prod_eq_prod` / `indepFun_iff_measure_inter_preimage_eq_mul`), then `integral_prod` (Fubini) freezes `c` and the inner `∫ exp(c·z) dN(0,t−r) = exp(½c²(t−r))` is `integral_exp_mul_gaussianReal_zero`. Alternative if Fubini plumbing fights back: approximate `c` by `𝓕_r`-simple functions, apply the constant-multiplier `condExp_func_increment` (via `exp(aⱼ·)`) cellwise, pass to the L¹ limit.
**Deliverable.** `condExp_exp_adapted_mul_increment` green (0 sorries). Foundations infra — no benchmark entry yet.

### Brick α2 — `E^d` is a P-martingale
Same file (`SimpleDoleansExponential.lean`). **CORE DONE (2026-07-06, commit `082e677`).**
- ✅ `condExp_expCell_eq_one` — normalized freezing corollary `E[exp(cΔ − ½c²(t−r))|𝓕_r] = 1`.
- ✅ `cellExp a b c t = exp(c(X_{b∧t} − X_{a∧t}) − ½c²(b∧t − a∧t))` + region lemmas (`_of_le_left`,
  `_of_mem`, `_of_ge_right`) + `integrable_cellIncrement`.
- ✅ **`cellExp_isMartingale`** — the single-cell random-multiplier Wald martingale, via a
  4-region conditional-expectation argument (tower `𝓕_s ⊆ 𝓕_a` when `s ≤ a ≤ t`; pull-out of the
  `𝓕_s`-measurable `cellExp_s` when `a ≤ s`). axioms-clean.

**α2b — the N-cell product assembly. ✅ DONE (2026-07-06, commits `92da5ef`+`<α2>`).**
- ✅ `mul_cellExp_isMartingale` — M (martingale, frozen after `p`) × `cellExp p q c` is a martingale.
  Cross-cell integrability used only **pairwise** `hX.indep` (`M_p` is `𝓕_p`-measurable, so
  `IndepFun.integrable_mul` after dominating the cell by two Gaussian MGFs) — no mutual independence
  needed. 3-case conditional expectation (pull out `M_p` when `p ≤ s`; tower through `𝓕_p` when
  `s ≤ p ≤ t`; M-martingale when `t ≤ p`).
- ✅ `simpleDoleansExp` (recursive product) + `simpleDoleansExp_frozen` (frozen after `s N`) +
  **`simpleDoleansExp_isMartingale`** (induction on N via `mul_cellExp_isMartingale`). The density
  process `E^d`. axioms-clean, `lake build` green.

**α2 is COMPLETE.** α3 can now consume `E^{−c}` / `E^{a−c}` (= `simpleDoleansExp s (−c)` / `s (a−c)`)
as martingales.

### Brick α3 — simple-θ Girsanov: `B^θ` is Q-Brownian (mirror the constant-θ file)
`MathFin/Foundations/GirsanovSimpleTheta.lean` (new). Feed `E^{−c}` and `E^{a−c}` (both α2 martingales) into `changeOfMeasure_setIntegral_eq`; re-run the constant-θ chain verbatim (charFun independence via `indepFun_iff_charFun_prod`). Deliverable: `Btheta_simple_isQBrownianMotion` + **new `full` benchmark entry** `gir-simple-adapted` (strict generalization of `gir-const-theta-qbm`).

### Brick α4 — continuous bounded adapted θ (the hard analytic brick; may be several sessions)
Approximate continuous bounded adapted `θ` by simple `θ⁽ⁿ⁾` in `L²(dt×dP)`; `E^{−c⁽ⁿ⁾}_T → Z_T` in `L¹(P)` (bounded θ ⟹ uniform `L²` control); the charFun identity for `B^θ` increments under `Q⁽ⁿ⁾` passes to the limit. Needs the stochastic-integral density `∫θdB` as the `L²` limit of `Σ c⁽ⁿ⁾ᵢΔXᵢ` (the tower's `itoIntegralCLM_T`, with the σ-realization half of SP0 — the sub-interval increment API is **not** needed). Deliverable: `Btheta_isQBrownianMotion_adapted`.

### Brick α5 — flip `gir-thm-9.1.8` → full + wire
Restate `gir-thm-9.1.8` with the honest Doléans density (reconcile sign `θ ↔ −θ`), re-export `Btheta_isQBrownianMotion_adapted`; `metadata.formalization_status: "full"`. Regenerate `AxiomAuditGen.lean`, extend `AxiomAudit.lean`, ledger re-verify, gates 19/19. Update `docs/coverage.md`, `docs/bridges.md`, `docs/mathematical-architecture.md` (Girsanov row ◐→✅ bounded case), `docs/roadmap.md`.

## Verification (each brick)
`./scripts/lean-check.sh <file>` → `sorry_count 0`; final `lake build` daemon-down before relying on oleans; `#print axioms` clean on headliners; ledger fresh; pytest 19/19.

## Risks
- **α1 Fubini plumbing** (joint-law factorization + integrability side-conditions) — the simple-function-approximation fallback is the escape hatch.
- **α4 is genuinely hard** (the stochastic-integral density + `L²`→charFun limit); α3 (simple θ) is already an honest `full` deliverable strictly beyond constant-θ, so the program ships value even if α4 slips.
- **Ledger blast radius:** editing Foundations re-stales `stochastic_calculus`/`mathematical_finance`; re-verify warm-daemon, detached.
