# Continuous Itô integral (CLM extension) — deferred work + verified midpoint

**Status:** deliberately **deferred**. The L²-adapted Itô **isometry** (the substantive
analytic content) is delivered and on `main` in
`QuantFin/Foundations/ItoIntegralL2.lean` (`memLp_itoSimple`, `itoSimple_sq_integral`,
`itoSimpleLp_norm_sq`) and `QuantFin/Foundations/ItoIsometryAdapted.lean`
(`rect_increment_pairing` etc.). The continuous extension to a `ContinuousLinearMap`
`itoIntegralL2 : L2Predictable ν μ →L[ℝ] Lp ℝ 2 μ` is **not built**, because:

- Nothing in the library consumes a continuous Itô *integral* — pricing goes through
  static Gaussian methods (static-Girsanov/Esscher EMM, Black–Scholes, Margrabe; leaps
  1–3 bypass Itô entirely).
- It only pays off as the base of a full continuous-time Itô-*calculus* layer (Itô's
  lemma, SDE existence/uniqueness, continuous Girsanov) — a separate, upstream-Mathlib-scale
  program.
- It is ~160 lines of *standard* L²-completion packaging (large because Mathlib lacks the
  Itô integral, not because it is deep).

This note preserves the verified **midpoint** (the time-measure `ν`) and the full plan, so
the CLM is turnkey to resume if/when the Itô-calculus layer is pursued.

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
