# Continuous Itô integral (CLM extension) — progress + remaining density gap

> **CLOSED 2026-06-13 (Summit B / B2).** The infinite-horizon (`ℝ≥0`,
> σ-finite) Itô integral CLM is now **built**: `itoIntegralL2` /
> `itoIntegralL2_norm` in `MathFin/Foundations/ItoIntegralL2Dense.lean`
> (corpus entry `sc-ito-infinite-horizon-isometry`). The density step below
> was obtained **without** the upstream elementary-set π-system: the
> finite-horizon `predictableRect` π-system is T-independent and reused
> verbatim, and the σ-finite exhaustion reduces each finite frame
> `Ioc 0 (n+1) ×ˢ univ` to the finite `trimMeasure_T (n+1)` (via
> `trimMeasure_T_eq_restrict`), where the finite-horizon
> `setIntegral_eq_zero_of_orthogonal_pred` applies; the `{0}×univ` complement
> is `timeMeasure`-null. The rest of this document is kept as the historical
> design record.

> **Note (2026-05-30): the finite-horizon `[0,T]` Itô integral CLM is DONE.**
> `itoIntegralCLM_T` in `Foundations/ItoIntegralCLM.lean` is built, axioms-clean,
> AxiomAudit-pinned, with `∫₀ᵀ B dB = ½(B_T²−B₀²−T)` (`ItoIntegralBrownian.lean`)
> as its first consumer. This document tracks only the *separate* infinite-horizon
> variant — the `L2Predictable timeMeasure μ` integral over all of `ℝ≥0` — whose
> density step remains open.

**Status (2026-05-27): CLM steps 1–3 BUILT on `main`; only density + `extendOfNorm` remain.**
The L²-completion was resumed (this supersedes the earlier "deferred" status). All of the
following are on `main` in `MathFin/Foundations/ItoIntegralL2.lean`, full build green
(8646 jobs), AxiomAudit-clean, sorry-free:

- **ν time-measure** (`timeMeasure` = Lebesgue on `ℝ≥0`): `SigmaFinite`, `timeMeasure_Ioc`,
  `timeMeasure_Ioc_inter`, `timeMeasure_singleton`.
- **Embedding** `simpleProcessL2 : SimpleProcess → Lp ℝ 2 ((timeMeasure.prod μ).trim …)`
  (= Degenne's `L2Predictable timeMeasure μ`, kept unfolded for the `Lp` norm instance):
  `rectTerm` / `memLp_rectTerm` (finite-time-support L² bound), `uncurry_ae_eq_sum_rectTerm`
  (the `{⊥}`-fibre is null), `memLp_uncurry_trim` (`eLpNorm_trim`), `simpleProcessL2`.
- **Itô isometry** `simpleProcessL2_norm_sq`: `‖simpleProcessL2 V‖²` = the SAME predictable-
  rectangle double sum as `itoSimpleLp` (Fubini, `integral_prod_mul`, `integral_rectTerm_mul`).
- **Linear maps + isometry bound**: `itoAssembly : SimpleProcess →ₗ[ℝ] Lp ℝ 2 μ`,
  `simpleAssembly : SimpleProcess →ₗ[ℝ] Lp ℝ 2 (trim)`, and
  `assembly_isometry : ‖itoAssembly V‖ = ‖simpleAssembly V‖`.

**Remaining: `DenseRange simpleAssembly`, then `itoAssembly.extendOfNorm simpleAssembly`.**
The density is the genuine remaining work, harder than the Wiener analogue
(`stepAssembly_denseRange`) for two reasons:

1. **The orthogonal-complement route needs a *finite* measure.** Wiener's `compl` step uses
   `∫_{sᶜ} g = ∫_univ g − ∫_s g`, valid because `volume.restrict (Ioc 0 T)` is finite. Our
   `timeMeasure` is horizon-free hence **infinite** (σ-finite). `Lp.ae_eq_zero_of_forall_-`
   `setIntegral_eq_zero` only needs `∫_s g = 0` on **finite-measure** sets (no σ-finite
   hypothesis — good), but the π-system induction proving that must avoid `∫_univ`; it needs a
   σ-finite **exhaustion** of the predictable σ-algebra by finite-measure predictable sets
   (e.g. `Iic n ×ˢ univ`), not the finite-measure shortcut.
2. **Elementary-predictable-set π-system is a Degenne gap.** `induction_on_inter` over
   `generateFrom_eq_predictable` needs `IsPiSystem {↑S | S : ElementaryPredictableSet 𝓕}`.
   Degenne supplies `generateFrom_eq_predictable` but **not** the π-system property. The
   intersection of two elementary predictable sets IS elementary (rectangles:
   `(Ioc p × A) ∩ (Ioc q × B) = Ioc(max p.1 q.1)(min p.2 q.2) × (A∩B)`; `{⊥}×_ ∩ Ioc _ = ∅`),
   so it holds — but constructing the intersected `ElementaryPredictableSet` (with its
   disjointness field) is ~40–60 lines and **belongs upstream in brownian-motion** (like the
   `StochasticInterval` #440 contribution), then consumed here.

   > **Re-verified 2026-05-31 against the current pin (`fa590b1`, = upstream `main` tip).**
   > The gap **stands**: the package now ships `ElementaryPredictableSet` (structure, with its
   > disjointness field), `ElementaryPredictableSet.generateFrom_eq_predictable`,
   > `measurableSet_predictable`, and `indicator`/`coe_indicator` — but **no `IsPiSystem`
   > lemma** for `{↑S | S : ElementaryPredictableSet 𝓕}` (the actual prerequisite for
   > `induction_on_inter`). So the ~40–60-line π-system lemma is still the missing piece, and
   > remains a clean, well-scoped **upstream contribution** to `brownian-motion` (it would
   > unblock the package's own WIP integral *and* this infinite-horizon CLM at once). The
   > finite-horizon `[0,T]` CLM does not need it (it uses our own `predictableRect` π-system).

The orthogonality base case is in hand: `⟪simpleProcessL2 (SimpleProcess.indicator S 1), g⟫`
`= ∫_{S.toSet} g d(trim)` via `coe_indicator` (`uncurry ⇑(indicator S e) = (S:Set).indicator …`)
+ `L2.inner_def` + `integral_indicator`; and `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`
needs no σ-finiteness. So the resume path is: (a) upstream the elementary-set π-system, (b)
finite-measure predictable exhaustion, (c) `induction_on_inter`, (d) `extendOfNorm`.

This note also preserves the verified `ν` midpoint below. The CLM only fully pays off as the
base of a continuous-time Itô-*calculus* layer (Itô's lemma, SDEs) — a separate program.

## Verified midpoint — the time measure `ν` (Lebesgue on `ℝ≥0`)

This compiled green (was on `main` as commit `1373bc5`, then reverted in `87ed773` as
unused scaffolding). It is the `ν` for `L2Predictable ν μ`; the interval overlap in the
isometry **is** Lebesgue length (from `E[(Bₜ−Bₛ)²]=t−s`), so `ν` must be Lebesgue, and
`ℝ≥0` has no canonical `volume` — hence the `comap`.

```lean
/-- The coercion `ℝ≥0 → ℝ` as a measurable embedding (it is a closed embedding). -/
lemma measurableEmbedding_nnrealCoe : MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
  NNReal.isClosedEmbedding_coe.measurableEmbedding

/-- Lebesgue measure on the time axis `ℝ≥0` — the comap of `volume` along `ℝ≥0 ↪ ℝ`. -/
noncomputable def timeMeasure : Measure ℝ≥0 := Measure.comap ((↑) : ℝ≥0 → ℝ) volume

lemma timeMeasure_Ioc (a b : ℝ≥0) :
    timeMeasure (Set.Ioc a b) = ENNReal.ofReal ((b : ℝ) - a) := by
  have himg : ((↑) : ℝ≥0 → ℝ) '' Set.Ioc a b = Set.Ioc (a : ℝ) b := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioc]
    constructor
    · rintro ⟨y, ⟨hay, hyb⟩, rfl⟩
      exact ⟨by exact_mod_cast hay, by exact_mod_cast hyb⟩
    · rintro ⟨hax, hxb⟩
      have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt a.coe_nonneg hax)
      exact ⟨⟨x, hx0⟩, ⟨by exact_mod_cast hax, by exact_mod_cast hxb⟩, rfl⟩
  rw [timeMeasure, measurableEmbedding_nnrealCoe.comap_apply, himg, Real.volume_Ioc]

/-- The `vol((p]∩(q])` factor of the Itô-isometry double sum. -/
lemma timeMeasure_Ioc_inter (a b c d : ℝ≥0) :
    timeMeasure (Set.Ioc a b ∩ Set.Ioc c d)
      = ENNReal.ofReal (min (b : ℝ) d - max (a : ℝ) c) := by
  rw [Set.Ioc_inter_Ioc, timeMeasure_Ioc, NNReal.coe_min, NNReal.coe_max]
```

## Remaining plan (mirrors `WienerIntegralL2.lean`, integrand space adapted)

Domain `L2Predictable ν μ = Lp ℝ 2 ((ν.prod μ).trim 𝓕.predictable_le_prod)` (Degenne `L2M`),
with `ν = timeMeasure`, `μ` the probability measure, `𝓕 = natFiltration`.

1. **Embedding + Fubini norm** — `simpleProcessL2 : SimpleProcess → L2Predictable` and
   `‖simpleProcessL2 V‖² = ∫∫ (uncurry V)² d(ν⊗μ) = Σ_{p,q} E[V(p)V(q)]·ν((p]∩(q])` = the
   isometry's RHS. Uncurry `V.toFun` is a `Finsupp.sum` of interval-indicators + the `⊥`-value;
   the `{⊥}` slice is `ν`-null (`timeMeasure {⊥}=0`); then `integral_prod` (Fubini) +
   `timeMeasure_Ioc_inter`. `MemLp` in the trimmed measure comes from `SimpleProcess.isPredictable`
   (StronglyMeasurable[predictable]) + finite norm via `eLpNorm_trim` / `memLp_of_memLp_trim`.
   NB: `ν` is **infinite** (σ-finite) — a bounded SimpleProcess is L² only via its **compact
   time-support**, so `MemLp` must come from this finite norm, not boundedness.
2. **The two linear maps** — `itoAssembly : SimpleProcess →ₗ[ℝ] Lp ℝ 2 μ` (`V ↦ itoSimpleLp V`,
   linear via `SimpleProcess.integral_add_left`/`integral_smul_left` + `MemLp.toLp` linearity)
   and `simpleAssembly : SimpleProcess →ₗ[ℝ] L2Predictable ν μ`. The bound
   `‖itoAssembly V‖ = ‖simpleAssembly V‖` is step 1's norm = `itoSimpleLp_norm_sq`'s RHS.
3. **Density** (the crux) — `DenseRange simpleAssembly`: simple processes dense in `L2Predictable`
   via the orthogonal-complement route over the trimmed measure — `g ⊥ all elementary-predictable
   indicators ⇒ setIntegral = 0 ⇒` (`ElementaryPredictableSet.generateFrom_eq_predictable`,
   elementary sets are a π-system generating `𝓕.predictable`, `MeasurableSpace.induction_on_inter`)
   `⇒ g = 0 a.e.` (`Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`, needs the trimmed measure
   σ-finite). Mirrors `stepAssembly_denseRange`.
4. `itoIntegralL2 := itoAssembly.extendOfNorm simpleAssembly` + the isometry
   `‖itoIntegralL2 φ‖² = ∫₀ᵀ E[φ_t²] dt`.

## Don't-reinvent recon (Mathlib/Degenne)

- **Degenne has nothing on `L2Predictable` beyond the bare def** (blueprint's
  `simpleProcess_mem_L2Predictable`/`sq_norm_simpleProcess`/density lemmas are unformalized).
- **Mathlib primitives to assemble** (no end-to-end shortcut): `Lp.simpleFunc.dense` /
  `MemLp.induction_dense` (density), `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`,
  `integral_trim`/`eLpNorm_trim`/`memLp_of_memLp_trim` (trim), `integral_prod` (Fubini),
  `lpMeas`/`lpMeasToLpTrim` (predictable subspace). Degenne: `generateFrom_eq_predictable`,
  `SimpleProcess.isPredictable`, `SimpleProcess.integral_top`/`_add_left`/`_smul_left`.
- The genuine density gap with **no** high-level shortcut: *elementary*-predictable-set
  indicators (SimpleProcess) dense in the *predictable* σ-algebra's L² — `Lp.simpleFunc.dense`
  gives general-simple, leaving the π-system step. This is why the CLM is genuinely ~160 lines.

## 2026-06-10 — `SimpleProcess`/`L2Predictable` unification: verdict = already coherent, no action

The round-6 values review left "the `SimpleProcess`/`L2Predictable` unification" as a
deferred consolidation item. Scoped 2026-06-10 (as the warm-up to the Summit B / B1a
integral-as-process work) against the two embedding chains:

- **Infinite-horizon** (`ItoIntegralL2.lean`): `simpleProcessL2` (into
  `(timeMeasure.prod μ).trim`), `itoAssembly`, `simpleAssembly`, `assembly_isometry`.
- **Finite `[0,T]`** (`ItoIntegralCLM.lean`): `simpleProcessL2_T` (into `trimMeasure_T`),
  `itoAssembly_T`, `simpleAssembly_T`, `assembly_isometry_T`.

The `_T` layer **already consumes** the infinite-horizon layer at every substantive point:
`memLp_uncurry_trim_T = (memLp_uncurry_trim …).restrict` (CLM:281–282);
`itoAssembly_T = ItoIntegralL2.itoAssembly.comp (TBoundedSP …).subtype` (CLM:419–421);
`assembly_isometry_T` closes by `exact ItoIntegralL2.assembly_isometry` (CLM:431);
`simpleProcessL2_T_norm_eq` unfolds to `ItoIntegralL2.simpleProcessL2` (CLM:395). The only
standalone defs (`simpleProcessL2_T`, `simpleAssembly_T`) are genuine **distinct objects over
the T-restricted measure `trimMeasure_T`** — the entire reason the fixed-`T` CLM exists —
related to their infinite-horizon counterparts by the restrict/norm bridges already present.
They cannot be collapsed to one definition (different measures), and forcing it would add
coupling for cosmetic dedup.

**Verdict: no action.** The unification is already realized as *consumption*; the residual is
deliberate type-level distinctness. This closes the round-6 deferred item.
