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
`MathFin/Foundations/GirsanovSimpleTheta.lean` (new). **FOUNDATION DONE (2026-07-06, commit `38f2bdc`).**
- ✅ `cellExp_zero`, `simpleDoleansExp_zero` (density `= 1` at `t = 0`), `simpleDoleansExp_pos`.
- ✅ `simpleDoleansExp_integral_eq_one` — unit `P`-mean from the α2 martingale (`E[Z_T] = E[Z_0] = 1`).
- ✅ `simpleGirsanovMeasure_isProbabilityMeasure` — `Q = P.withDensity Z_T` is a probability measure
  (via `isEquivProbMeasure_withDensity`, mirroring `girsanovMeasure_isProbabilityMeasure`).

### Brick α3-abstraction — the reusable exponential characterization ✅ DONE (2026-07-06)
`MathFin/Foundations/ExpMartingaleQBrownian.lean` (new). The ~10-theorem constant-θ charFun chain
was **not** re-derived for simple θ; instead it was **abstracted once, process-agnostically**. The
route decision (the plan's "Consider abstracting …" made concrete): factor steps 3–14 of the
constant-θ file into a single module keyed only on `(Q, 𝓕, Y, T)` + the hypothesis bundle.
- ✅ `IsExpQMartingale Q 𝓕 Y T` (structure): `Y` adapted, `Y 0 =ᵐ[Q] 0`, and for every `a`
  `exp(a·Y − ½a²·)` is a `Q`-martingale on `[0,T]` (as the set-integral identity over `𝓕_s`-sets).
- ✅ `map_eq_gaussianReal_of_expMartingale` (marginal law `N(0,t)`), `increment_map_eq_gaussianReal_of_expMartingale`
  (increment law `N(0,t−s)`), `increments_indepFun_of_expMartingale` (disjoint increments `Q`-independent,
  via `indepFun_iff_charFun_prod`), and the packaging `isQBrownianMotion_of_expMartingale` (the triple).
  The ten intermediate MGF/condExp/joint-MGF/linComb lemmas are `private`. Green, axioms-clean.

**Const-θ refactored onto the abstraction ✅ DONE (2026-07-06).** `GirsanovConstantTheta.lean` keeps
only the two process-specific results — `expBtheta_isQMartingale` (the exponential martingale, from
the Bayes engine + two Wald exponentials) and `girsanovMeasure_isProbabilityMeasure` — plus a new
`isExpQMartingale_Btheta` packaging `B^θ_u = X_u + θ u`; its four public deliverables
(`Btheta_map_eq_gaussianReal`, `Btheta_increment_map_eq_gaussianReal`, `Btheta_increments_indepFun`,
`Btheta_isQBrownianMotion`) are now **one-line instances** of the abstraction. ~450 lines of
duplicated chain deleted; both corpus benchmarks (`gir-const-theta-marginal`, `gir-const-theta-qbm`)
re-verified green; AxiomAuditGen byte-fresh (proof-heads unchanged); gates 19/19; `lake build` 8848
green. This validates the abstraction against a known-good instance before simple-θ is built on it.

**α3 P-side spine ✅ DONE (2026-07-06).** In `GirsanovSimpleTheta.lean`:
- ✅ `simpleDrift s c N t = Σ_i c_i·(s_{i+1}∧t − s_i∧t)` (so `B^θ_t = X_t + simpleDrift_t`) +
  `stronglyMeasurable_simpleDrift` (`𝓕`-adaptedness: per cell, either `s_i ≤ u` so `c_i` is
  `𝓕_u`-measurable, or `u ≤ s_i` so the clamped interval is `0`).
- ✅ `simpleDoleansExp_eq_exp_sum` — log-form `E^d_t = exp(Σ_i [d_i·ΔX_i − ½d_i²·Δτ_i])`, so the
  spine is one exponent identity (`Real.exp_add` + `Finset.sum_range_succ`).
- ✅ **`simple_spine`** — the tilted-density identity `E^{−c}_t · exp(a·B^θ_t − ½a²t) =
  exp(a·X_0)·E^{a−c}_t` (per-cell `(−c_i)ΔX_i − ½c_i²Δτ_i` and `a·ΔX_i + a·c_i·Δτ_i − ½a²Δτ_i`
  combine to `(a−c_i)ΔX_i − ½(a−c_i)²Δτ_i`). Telescoping via `Finset.sum_range_sub` under the cover
  `s_0 = 0`, `t ≤ T ≤ s_N`; the algebra closes by `linear_combination`. The genuinely intricate
  brick, now verified.
- ✅ **`simple_spine_ae`** — the a.e. form `E^{−c}·exp(a·B^θ − ½a²·) =ᵐ[P] E^{a−c}` (since
  `X_0 = 0` a.e.), the exact analogue of `Wald(−θ)·Wald(a) = Wald(a−θ)` in the constant-θ file.

**α3 Q-SIDE ✅ COMPLETE (2026-07-06).** `Btheta_simple_isQBrownianMotion` — `B^θ` is a `Q`-Brownian
motion for simple (piecewise-constant adapted) θ, strictly beyond constant θ, on the existing tower
with **no** adapted-integrand Itô formula. The two pieces that were genuinely harder than the
constant-θ analogues, both solved:
- **`integrable_expBthetaSimple_mul_density`** (the mixed-time `hmix`, `D_u·Z_T ∈ L¹`) — NOT the feared
  N-fold induction, but a clean **L² Hölder** (`MemLp.mul`, `L²·L² ⊆ L¹`): `D_u ∈ L²` by the Gaussian
  MGF of `X_u` with the drift bounded (`simpleDrift_abs_le`, `|drift_u| ≤ K·u`), and `Z_T ∈ L²`
  because `Z_T² = E^{−2c}_T · exp(∑ c_i²Δτ_i)` with `∑ c_i²Δτ_i ≤ K²T` — an integrable density times a
  bounded factor.
- **the full `Z·D` martingale, sidestepped** — instead of proving `Z·D` a martingale on all of `ℝ≥0`
  (which diverges beyond `s_N`), the engine's helper `∫_A D_u dQ = ∫_A Z_u D_u dP` was **inlined** and
  the final step done with `simple_spine_ae` (`Z·D =ᵐ E^{a−c}` on `[0,T]`) + the `E^{a−c}` martingale's
  `setIntegral_eq` — so only the `[0,T]` spine is needed, never the beyond-`s_N` behaviour.

`isExpQMartingale_BthetaSimple` packages the three `IsExpQMartingale` fields; `Btheta_simple_isQBrownianMotion`
is one application of `isQBrownianMotion_of_expMartingale` (the abstraction's payoff — no charFun chain).
Deliverable **shipped**: `full` benchmark `gir-simple-adapted`, AxiomAuditGen guard, axioms-clean.
**Brick α3 is DONE.** Only α4 (continuous adapted θ) and α5 (flip `gir-thm-9.1.8`) remain.

### Brick α4 — continuous bounded adapted θ (the hard analytic brick; multi-session, infrastructure-gated)
**Reconnaissance done (2026-07-06):** α4 is *buildable* but gated on ONE genuinely-missing (unwritten, not
`sorry`'d) infrastructure lemma. Everything else is present and sorry-free.

**Already built + reusable (verified):**
- `ItoIntegralCLM.itoIntegralCLM_T` (`ItoIntegralCLM.lean:718`) — the `∫₀ᵀ θ dB` machine, a CLM isometry
  `Lp ℝ 2 (trimMeasure_T μ T) →L[ℝ] Lp ℝ 2 μ`, with `itoIntegralCLM_T_norm` (Itô isometry `:725`).
  Domain = L² *predictable* integrand classes over the trim product measure.
- `ItoIntegralCLM.simpleAssembly_T_denseRange` (`:649`) — simple step processes are dense in the integrand
  L²; `itoAssembly_T` / `itoIntegralRiemannBridge.itoSimple_stepφ` give the finite-sum `∑ cᵢ(B_{tᵢ₊₁}−B_{tᵢ})`.
- CLM-continuity ⟹ `∫θⁿdB → ∫θdB` in L² for free; worked template `itoIntegralCLM_T_of_bdd_cont` (Riemann-Itô
  sums for a bounded *continuous* integrand `φ∘B`).
- `Btheta_simple_isQBrownianMotion` (the α3 target to pass to the limit) + the `IsExpQMartingale` abstraction.

**The two pieces that must be WRITTEN (the α4 work):**
1. **`processToLp_of_bdd_adapted_cont`** — the **σ-realization** (half (i) of SP0): realize a bounded adapted
   *continuous* raw `σ : ℝ≥0 → Ω → ℝ` as an integrand class `φ ∈ Lp 2 (trimMeasure_T)` (predictable-measurability
   as an a.e. limit of simple processes + L² membership + `.toLp`). **This is the load-bearing gap** — no
   shortcut lemma in Degenne (`isStronglyPredictable` is only for `SimpleProcess`; `predictableConvexStep` /
   `predictablePartLim` are the tools but connecting a continuous adapted process to them is the substantial
   work). Design doc (`docs/specs/2026-07-05-adapted-ito-formula-design.md:101`) rates it "substantial." The
   sub-interval increment API (half (ii)) is **not** needed for α4.
2. **L²-exponent → L¹-density**: turn `∫θⁿdB − ½∫(θⁿ)²ds → ∫θdB − ½∫θ²ds` in L² into `E^{−c⁽ⁿ⁾}_T → Z_T` in
   L¹(P) (uniform-integrability control from bounded θ), then pass the α3 charFun/increment identity to the limit.
Deliverable: `Btheta_isQBrownianMotion_adapted`. **Status: NOT started — its own focused effort; α3 (simple) is
already an honest `full` deliverable strictly beyond constant θ, so the program ships value regardless.**

### Brick α5 — flip `gir-thm-9.1.8` → full + wire
**Gated on α4** (the `full` flip re-exports `Btheta_isQBrownianMotion_adapted`, which α4 must first build).
The honest flip cannot happen before α4: `gir-thm-9.1.8` / `sc-thm-9.1.8` are `reduced_core` **structure
specs** for the *general continuous adapted* case, and narrowing them to the simple case (already shipped as
`gir-simple-adapted`, `full`) would change the claim — not honest.

**Interim wiring DONE (2026-07-06, docs-only, ledger-neutral):** `gir-thm-9.1.8` and `sc-thm-9.1.8`
`formalization_scope` prose now cross-references the real `gir-simple-adapted` derivation and names the exact
remaining gap (the σ-realization `processToLp_of_bdd_adapted_cont`); `docs/roadmap.md`, `docs/coverage.md`,
`docs/bridges.md`, `docs/mathematical-architecture.md` record the frontier (simple-adapted `full`;
continuous-adapted infrastructure-gated).

**When α4 lands:** restate `gir-thm-9.1.8` with the honest Doléans density (reconcile sign `θ ↔ −θ`), re-export
`Btheta_isQBrownianMotion_adapted`, `metadata.formalization_status: "full"`; regenerate `AxiomAuditGen.lean`,
extend `AxiomAudit.lean`, ledger re-verify, gates 19/19; Girsanov row ◐→✅ (bounded case).

## Verification (each brick)
`./scripts/lean-check.sh <file>` → `sorry_count 0`; final `lake build` daemon-down before relying on oleans; `#print axioms` clean on headliners; ledger fresh; pytest 19/19.

## Risks
- **α1 Fubini plumbing** (joint-law factorization + integrability side-conditions) — the simple-function-approximation fallback is the escape hatch.
- **α4 is genuinely hard** (the stochastic-integral density + `L²`→charFun limit); α3 (simple θ) is already an honest `full` deliverable strictly beyond constant-θ, so the program ships value even if α4 slips.
- **Ledger blast radius:** editing Foundations re-stales `stochastic_calculus`/`mathematical_finance`; re-verify warm-daemon, detached.
