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

**The two pieces of the α4 work:**
1. **σ-realization ✅ DONE (2026-07-06)** — `MathFin/Foundations/AdaptedProcessToLp.lean`:
   `isStronglyPredictable_of_bdd_adapted_cont` + `memLp_uncurry_of_bdd_adapted_cont` + **`processToLp`**
   (+ `processToLp_coeFn`). Realizes a bounded, adapted, every-`ω`-continuous `σ : ℝ≥0 → Ω → ℝ` as an integrand
   class in `Lp 2 (trimMeasure_T T)` (the domain of `itoIntegralCLM_T`). **The feared "load-bearing gap" was NOT
   substantial:** the deep recon (superseding the earlier "predictability as an a.e. limit of simple processes"
   scare) found Degenne's `StronglyAdapted.isStronglyPredictable_of_leftContinuous` (every-`ω` continuity gives
   the left-continuity it wants) and the tower's own `DriftProcessPredictable.driftSimpleProcessLp` recipe. My
   lemma is that recipe with the concrete drift replaced by a general hypothesized `σ` — a ~30-line assembly
   (`isStronglyPredictable_of_leftContinuous` → `.aestronglyMeasurable` → `MemLp.of_bound` on the finite
   `trimMeasure_T` → `.toLp`), green + axioms-clean on the first pass. (For an *only-a.e.*-continuous `σ` one
   would route through the `limUnder` pattern of `ItoProcessPredictable`; not needed — bounded adapted continuous
   θ is every-`ω`-continuous.)
2. **L²-exponent → L¹-density** (remaining; a genuine multi-lemma build, fully scoped by two deep recons).

**★ Key enabler (verified 2026-07-06):** the two Brownian notions reconcile for free —
`IsPreBrownianReal.isFilteredPreBrownian hBmeas : IsFilteredPreBrownian B (natFiltration hBmeas) μ`
(`.lake/.../Gaussian/BrownianMotion.lean:289`; `natFiltration hBmeas = Filtration.natural B …`, `ItoIntegralL2.lean:64`).
So `IsPreBrownianReal B μ` gives BOTH the Itô integral (natFiltration) AND the α3 machinery
(IsFilteredPreBrownian) on the same `B` — the continuous theorem can take `IsPreBrownianReal B μ` + `hBmeas` and use both halves.

**Architecture:** prove `IsExpQMartingale Q 𝓕 (fun t ω ↦ B t ω + ∫₀ᵗθds) T` by LIMIT of the simple case and apply
`isQBrownianMotion_of_expMartingale` ONCE (reuse the abstraction; pass only the exp-martingale field, not the
charFun/independence chain). Q = `μ.withDensity(Z_T)`, `Z_T = exp(−∫θdB − ½∫θ²ds)` (pointwise-positive `exp` form
required by `isEquivProbMeasure_withDensity`, `EquivMeasure.lean:33`).

**PRESENT (no gap), with file:line:** CLM convergence `(itoIntegralCLM_T …).continuous.tendsto` (idiom already at
`ItoIntegralRiemannBridge.lean:288`) + `simpleAssembly_T_denseRange` (`ItoIntegralCLM.lean:649`); Lp→a.e.-subseq
`tendstoInMeasure_of_tendsto_Lp` (`ConvergenceInMeasure.lean:474`) + `TendstoInMeasure.exists_seq_tendsto_ae` (`:277`);
Vitali ENDPOINT `tendsto_Lp_finite_of_tendstoInMeasure` (`UniformIntegrable.lean:566`); L¹→integral
`tendsto_integral_of_L1'` (`Bochner/Basic.lean:390`); withDensity transport `setIntegral_withDensity_eq_setIntegral_toReal_smul`
(used `GirsanovSimpleTheta.lean:406`); unit-mean `simpleDoleansExp_integral_eq_one`; prob-measure
`isEquivProbMeasure_withDensity`; law injectivity `Measure.ext_of_complexMGF_eq` (`ComplexMGF.lean:319`, reused in
ExpMartingaleQBrownian); Lévy fallback `ProbabilityMeasure.tendsto_iff_tendsto_charFun` (`LevyConvergence.lean:214`).

**MUST BUILD (the α4 work, in order):**
- (a) **`unifIntegrable_one_of_sq_integral_le`** — THE linchpin, the ONE genuine Mathlib absence (no "bounded in Lᵖ,
  p>1 ⟹ UnifIntegrable"): from `MemLp (fⁿ) 2` + `sup_n ∫(fⁿ)² ≤ M` conclude `UnifIntegrable fⁿ 1 μ`, via
  `unifIntegrable_of` (`UniformIntegrable.lean:653`) + a Chebyshev truncation (`C·1_{‖f‖≥C}‖f‖ ≤ ‖f‖²`). General,
  reusable, ~60-line ENNReal proof. Unlocks the Vitali endpoint. The uniform L² bound `∫(Z⁽ⁿ⁾)² ≤ exp(K²T)` reuses the
  `Z² = E^{−2c}·exp(∑c²Δτ)` identity already in `integrable_expBthetaSimple_mul_density`.
- (a) **`unifIntegrable_one_of_sq_integral_le`** ✅ DONE (`UnifIntegrableL2.lean`, commit `6e301c8`).
- (b) **`itoIntegralCLM_T_of_bdd_adapted_cont`** ✅ DONE (2026-07-08, `ItoIntegralRiemannBridgeAdapted.lean`).
  The `∫θdB` CLM for a GENERAL bounded adapted continuous θ: the uniform-partition Riemann–Itô sums
  `∑ θ(tₖ)·ΔBₖ` converge in `L²(μ)` to `itoIntegralCLM_T (processToLp θ)`. Mirrors the φ∘B template
  (`itoIntegralCLM_T_of_bdd_cont`) line-for-line — new defs `riemannσ`/`stepσ` + lemmas
  `memLp_riemannσ`/`itoSimple_stepσ`/`itoIntegralCLM_T_stepσ`/`uncurry_stepσ`, reusing `cell_collapse`
  (partition-only, `omit hB`), `processToLp` as the target, and the same DCT L²-convergence.
  ★KEY simplification: **no `AdaptedAt`↔`natFiltration` bridge needed** — `memLp_riemannσ` proves the
  Riemann sum `L²` by plain **domination** (`‖θ·Δ‖ ≤ ‖C·Δ‖`, `MemLp.mono` on `hΔ.const_mul C`) instead of
  `memLp_adapted_mul_increment` (which wants `AdaptedAt`), so the hypotheses match `processToLp` exactly
  (`natFiltration`-strongly-measurable + continuous + bounded). Green, axioms-clean, no benchmark (Foundations infra).
  **drift Riemann-convergence ✅ DONE (2026-07-09, `DriftRiemannConvergence.lean`).** The deterministic
  half of the continuous Doléans exponent: `tendsto_riemannSum_setIntegral` (bounded-continuous `g`:
  `∑ g(tₖ)·(t_{k+1}−tₖ) → ∫ s in (0,T], g s ∂timeMeasure`) + the `θ²` specialization
  `tendsto_driftSq_riemannSum` (`∑ θ(tₖ)²·Δτ → ∫₀ᵀ θ²ds`, per path). Same `cell_collapse` + DCT as brick b,
  now on the finite time measure `timeMeasure.restrict (0,T]`. Green, no benchmark (Foundations infra).
- (c) **the exp-martingale limit assembly** — build `IsExpQMartingale Q 𝓕 (fun u ω ↦ B_u + ∫₀ᵘθds) T` by
  passing the simple-θ identity to the limit (`isExpQMartingale_BthetaSimple` for the `unifPart`-partition
  approximants `c⁽ⁿ⁾ = θ(tₖ)`), then apply `isQBrownianMotion_of_expMartingale` ONCE. The martingale field,
  transported to P, is `∫_A exp(a·Yⁿ−½)·Zⁿ_T dμ → ∫_A exp(a·Y−½)·Z_T dμ` — set-integral `L¹`-convergence.
  - **`L²→L¹` set-integral endpoint ✅ DONE (2026-07-09, `UnifIntegrableL2.lean`):**
    `tendsto_setIntegral_of_tendstoInMeasure_of_sq_bound` — on a finite measure, `fⁿ∈L²` + `sup ∫(fⁿ)²≤M` +
    `fⁿ→g` in measure ⟹ `∫_A fⁿ → ∫_A g` (linchpin ⟹ UnifIntegrable ⟹ Vitali `tendsto_Lp_finite…` ⟹
    `tendsto_setIntegral_of_L1`). This is the density-limit endpoint (`Zⁿ→Z` in measure, `∫(Zⁿ)²≤exp(K²T)`).
  - **STILL TODO (the irreversible core, own focused session):** (i) define the continuous density
    `Z_T = exp(−∫θdB − ½∫θ²ds)` via an Itô-CLM representative + the drift integral, and `Y_u = B_u + ∫₀ᵘθds`;
    (ii) `Zⁿ_T → Z_T` and `exp(a·Yⁿ−½)·Zⁿ_T → exp(a·Y−½)·Z_T` **in measure** (stochastic part L² brick b ⟹
    in-measure; drift part everywhere via the drift lemma; `exp`/product continuity). The **clamped horizon-`u`
    drift** `simpleDriftⁿ_u → ∫₀ᵘθds` (needed since the martingale identity is at intermediate `s'≤t'≤T`) is
    ✅ DONE (`tendsto_riemannSum_setIntegral_clamp`, 2026-07-09, `DriftRiemannConvergence.lean`).
    ★★**NEWLY-IDENTIFIED INFRA GAP:** Mathlib has NO `TendstoInMeasure` algebra (no `add`/`mul`/continuous-comp;
    only `tendstoInMeasure_of_tendsto_Lp` :474 and `_of_tendsto_ae` :223). So (ii) must build a **minimal
    in-measure toolkit** — either the direct closure lemmas, or (cleaner) route the *set-integral* limit through
    the **a.e.-subsequence principle**: to prove `∫_A hⁿ → ∫_A h` (a real sequence), show every subsequence has a
    further one along which `Wⁿ→W` a.e. (`TendstoInMeasure.exists_seq_tendsto_ae` on the L²-conv stochastic part),
    where the products/`exp` compose trivially a.e., then a.e.+uniform-L² ⟹ `∫_A→` (a.e. ⟹ in-measure on finite
    μ, feed `tendsto_setIntegral_of_tendstoInMeasure_of_sq_bound`), and lift via `tendsto_of_subseq_tendsto`.
    This subsequence route keeps the composition at the a.e. level (where `Continuous.comp`/`+`/`·` are free) and
    reuses the landed L¹ endpoint — no bespoke in-measure algebra. It IS its own ~2–3-lemma sub-effort. (iii) the continuous spine
    identity at the representative level (CLM linearity `∫(a−θ)dB = a·B − ∫θdB`); (iv) integrability; (v) assemble
    `isExpQMartingale_Btheta_adapted` + apply the abstraction. Deliverable: `Btheta_isQBrownianMotion_adapted`.
Deliverable: `Btheta_isQBrownianMotion_adapted`.
**Status: brick (a) + (b) + drift-convergence + `L²→L¹` endpoint all landed green. The remaining (c) core (i)–(v)
is the irreversible assembly — its own focused session, now fully mapped so it executes without re-recon. NOT to be
rushed as a tail-of-session partial.**

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
