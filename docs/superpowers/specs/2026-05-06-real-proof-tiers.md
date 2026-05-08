# Real-Proof Tiers For Stochastic-Process Formalization

**Author:** Raphael Coelho (with Claude Code assistance)
**Date:** 2026-05-06
**Status:** Spec — guides next stage of work after the inflation rollback

## Context

The benchmark suite covers 65 stochastic-process theorems drawn from Saporito-style course material. Under a strict faithfulness audit:

- 20 entries are delivery-claim ready (8 `full` real derivations / structural definitions, 12 `library_wrapper` direct Mathlib invocations).
- 45 entries are `reduced_core` — algebraic/analytic core checks, or Lean specifications where the textbook conclusion is encoded as a structure axiom rather than derived.
- 0 entries are `placeholder`.

A previous round of edits inflated the audit to `65/65 delivery-claim ready` by promoting 45 specification-based entries to `full`. Those promotions were rolled back: a structure with the textbook conclusion as a field, projected via `:= h.conclusion_field`, is type-checking but not deriving anything. The audit must reflect that.

The goal of this document is to classify the 45 remaining `reduced_core` entries by what it would actually take to convert them into real Lean derivations. We define three tiers:

- **Tier A** — real proofs achievable now with Mathlib `v4.18.0`.
- **Tier B** — needs a Mathlib-grade Brownian motion construction first.
- **Tier C** — needs the stochastic-integral layer on top of B (research-grade).

This is the basis for the next stage of work: pick Tier A targets, write real proofs, and contribute upstream where possible.

## Current Mathlib Landscape (Toolchain `v4.18.0`)

What Mathlib `v4.18.0` (pulled by `lean/lean-toolchain` + `lake update mathlib master`) gives us today:

**Solid foundations:**

- Measure theory, ENNReal, integrable functions, L^p spaces.
- Probability spaces, conditional expectation (`condExp`, `condExp_mul_of_stronglyMeasurable_left`, `condExp_indep_eq`, `condExp_condExp_of_le`, `condExp_add`, `condExp_smul`, …).
- Discrete-time martingales, submartingales, supermartingales (`Martingale`, `Submartingale`, `Supermartingale`).
- Filtrations and adapted processes (`Filtration`, `Adapted`).
- Stopping times (`IsStoppingTime`, `stoppedValue`, `hitting`).
- Discrete-time optional stopping, optional sampling.
- L^p submartingale convergence (`Submartingale.ae_tendsto_limitProcess`).
- Submartingale upcrossing inequality.
- Doob maximal inequality (`maximal_ineq`).
- Doob decomposition (`martingalePart`, `predictablePart`).
- Independence (`IndepFun`, `iIndepFun`, `Indep`, `iIndep`).
- 1D distributions: Gaussian (`gaussianReal`, `gaussianPDFReal`, `gaussianCDFReal`), exponential (`expMeasure`, `exponentialPDFReal`, `exponentialCDFReal`), gamma (`gammaMeasure`), Poisson (`poissonMeasure`).
- Strong law of large numbers (`StrongLaw.lean`).
- Borel-Cantelli (`Probability.Martingale.BorelCantelli`).

**Flagged TODOs:**

- Conditional Jensen's inequality. Files: `Mathlib/MeasureTheory/Function/ConditionalExpectation/Real.lean` (line ~`-- TODO: the following couple of lemmas should be generalized and proved using Jensen's inequality for the conditional expectation (not in mathlib yet)`), `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean` (line `-- TODO: Generalize via the conditional Jensen inequality`).

**NOT in Mathlib:**

- Brownian motion as a process object; Kolmogorov continuity theorem.
- Multivariate Gaussian (only 1D `gaussianReal`).
- Poisson convolution / sum of independent Poissons → Poisson.
- Stochastic integral / Itô isometry.
- Itô's formula.
- Lévy characterization of BM.
- Novikov's condition; Doléans–Dade exponential; Girsanov.
- SDE existence/uniqueness.
- Feynman–Kac.
- Black-Scholes PDE.
- Doob's L^p inequality (only the maximal-inequality version is present).
- Discrete martingale transform theorem.
- General-state Markov chains (only finite-state via Mathlib `Matrix`).

## Tier A — Real Proofs Achievable Now

Each entry below has a concrete proof path in Mathlib `v4.18.0`. Time estimates are for a focused contributor experienced with Lean / Mathlib; double them for first-time contributors.

### A.1 `ce-prop-2.1.11-jensen` — Conditional Jensen's inequality — **DONE 2026-05-07 (with explicit-subgradient hypothesis)**

**Textbook claim.** For convex `φ : ℝ → ℝ`, `X` integrable with `φ ∘ X` integrable, and σ-algebra `m`: `φ(E[X | m]) ≤ E[φ ∘ X | m]` almost surely.

**Approach used.** Mathlib `v4.18.0` has no general subgradient API for convex `ℝ → ℝ`, so the inequality is parametrized by an explicit subgradient `g : ℝ → ℝ` (with the supporting-line property as a hypothesis). Any convex `φ` on `ℝ` has such a `g` (its right derivative); the gap is shifted to the caller. Proof: pointwise `φ(Y) + g(Y)(X − Y) ≤ φ(X)` via the subgradient hyp; take `condExp` and use linearity, `condExp_sub`, `condExp_mul_of_stronglyMeasurable_left` (pull out `g(Y)` since `Y = E[X|m]` is `m`-measurable), `condExp_of_stronglyMeasurable` (self-condExp), and `condExp_mono`.

**Result.** Lean code in `benchmarks/conditional_expectation.json` entry `ce-prop-2.1.11-jensen`. Verifies in Docker. Promoted from `reduced_core` to `full`.

**Path.** Mathlib has every prerequisite:

- `ConvexOn ℝ Set.univ φ` and the supporting-line characterization (`ConvexOn.exists_affine_le`).
- `condExp_mono` (monotonicity of conditional expectation).
- `condExp_const`, `condExp_add`, `condExp_smul`, integrability lemmas.

The standard proof: write `φ` as the supremum of countably many affine functions `x ↦ a_n x + b_n` (Mathlib has this for lower semi-continuous convex `φ` via `ConvexOn`; for general convex on ℝ use the supporting-line representation on each rational point), apply `condExp_mono` and linearity to each `a_n X + b_n ≤ φ(X)`, take the sup. Mathlib's `ConvexOn.exists_affine_le` gives the affine minorants; `condExp_mono` propagates the inequality; ae-supremum closes it.

**Why this is high-leverage.** Mathlib explicitly flags this as a TODO. The proof would land upstream and unblock Doob's L^p inequality (which Mathlib's TODO comment says depends on conditional Jensen).

**Estimated effort.** 1–3 focused days for a Mathlib contributor.

### A.2 `mart-thm-2.4.6` — Doob's L^p inequality

**Textbook claim.** For `p > 1` and a non-negative submartingale `(M_n)`: `‖max_{k ≤ n} M_k‖_p ≤ (p / (p − 1)) · ‖M_n‖_p`.

**Status: feasible at v4.18.0; deferred for proof-engineering effort.**

**Audit (2026-05-07).** All ingredients exist at toolchain `v4.18.0`:

- Layer cake (verified location): `MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul` in `Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean` (NOT `Layercake.lean`), giving `∫⁻ ω, ofReal (f ω ^ p) ∂μ = ofReal p · ∫⁻ t in Ioi 0, μ {a | t ≤ f a} · ofReal (t^(p-1))`. Companion `_lt_mul` variant uses `t < f a`.
- Doob L¹ maximal: `MeasureTheory.maximal_ineq` in `Mathlib/Probability/Martingale/OptionalStopping.lean`. Exact signature: `(hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : NNReal} (n : ℕ) : ↑ε · μ {ω | ↑ε ≤ (Finset.range (n+1)).sup' _ (fun k => f k ω)} ≤ ofReal (∫ ω in {ω | ↑ε ≤ ...}, f n ω ∂μ)`. Note: `ε : NNReal`, set uses `≤`, requires `IsFiniteMeasure μ`.
- Hölder: `ENNReal.lintegral_mul_le_Lp_mul_Lq (μ : Measure α) {p q : ℝ} (hpq : p.HolderConjugate q) {f g : α → ENNReal} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : ∫⁻ (f*g) ∂μ ≤ (∫⁻ f^p ∂μ)^(1/p) * (∫⁻ g^q ∂μ)^(1/q)` in `Mathlib/MeasureTheory/Integral/MeanInequalities.lean`.
- L^p / rpow algebra: `MemLp.eLpNorm_eq_integral_rpow_norm`, `ENNReal.rpow_*` family.

**Proof outline.** ~150–300 lines (revised upward after API audit). Steps:

1. Define `Mstar M n ω := (Finset.range (n+1)).sup' Finset.nonempty_range_succ (fun k => M k ω)`. Prove measurability via `Finset.measurable_sup'`.
2. Connect `eLpNorm Mstar (ofReal p) μ` to `(∫⁻ ω, ofReal (Mstar ω ^ p) ∂μ)^(1/p)` via `MemLp.eLpNorm_eq_integral_rpow_norm` (or unfold `eLpNorm` for `0 < p < ∞`).
3. Apply `lintegral_rpow_eq_lintegral_meas_le_mul` to `Mstar`: `∫⁻ ω, ofReal (Mstar ω ^ p) = ofReal p · ∫⁻ t in Ioi 0, μ {ω | t ≤ Mstar ω} · ofReal (t^(p-1))`.
4. For each `t > 0`, apply `maximal_ineq` (with `ε = t.toNNReal`): `t.toNNReal · μ {t ≤ Mstar n ω} ≤ ofReal (∫ ω in {t ≤ Mstar n}, M n ω dμ)`. So `μ {t ≤ Mstar} ≤ ofReal(∫ ...) / t` (handling t > 0).
5. Plug into step 3: `∫⁻ ω, ofReal (Mstar^p) ≤ ofReal p · ∫⁻ t in Ioi 0, ofReal(t^(p-2)) · ofReal(∫_{t ≤ Mstar} M n dμ)`.
6. **Fubini swap** (the most delicate step): convert `∫⁻ t in Ioi 0, ofReal(t^(p-2)) · (∫_{t ≤ Mstar} M n dμ)` to `∫⁻ ω, M n ω · (∫⁻ t in Ioo 0 (Mstar ω), ofReal(t^(p-2)) dt)`. The inner integral evaluates to `Mstar^(p-1) / (p-1)`.
7. Apply Hölder `ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p, q` conjugate (`q = p/(p-1)`): `∫⁻ M n · Mstar^(p-1) ≤ (∫⁻ (M n)^p)^(1/p) · (∫⁻ Mstar^((p-1)q))^(1/q) = (∫⁻ (M n)^p)^(1/p) · (∫⁻ Mstar^p)^((p-1)/p)`.
8. Set `A := ∫⁻ Mstar^p`, `B := ∫⁻ (M n)^p`. From steps 3+5+6+7: `A ≤ (p/(p-1)) · B^(1/p) · A^((p-1)/p)`. So `A^(1/p) ≤ (p/(p-1)) · B^(1/p)`, giving `‖Mstar‖_p ≤ (p/(p-1)) · ‖M n‖_p`.
9. Case-split: if `A = 0`, conclude trivially. If `A = ∞`, the inequality is trivially true. Otherwise divide.

**Why deferred.** Each step is a multi-line Mathlib API call with ENNReal-vs-Real coercions, careful handling of `Set.Ioi 0` vs `Set.Ioo 0 t`, and rpow algebra. Step 6 (Fubini) is particularly delicate because `Set.indicator {t ≤ Mstar ω} t` needs to be measurable in `(t, ω)` jointly. Realistically 1–3 days of focused Lean engineering. Infrastructure is fully present, so this is the highest-leverage next target.

**Why this is high-leverage.** Also flagged as a Mathlib TODO. Lands upstream alongside A.1.

**Estimated effort.** 1–3 focused days.

### A.3 `mart-thm-2.2.9` — Discrete martingale transform — **DONE 2026-05-06**

**Textbook claim.** If `M` is a martingale w.r.t. `𝓕` and `A` is bounded predictable, then `(A · M)_n = ∑_{k=0}^{n-1} A_{k+1} (M_{k+1} − M_k)` is a martingale w.r.t. `𝓕`.

**Path used.** Direct calculation using `martingale_nat`, `condExp_add`, `condExp_mul_of_stronglyMeasurable_left` (predictability ⇒ `A_{k+1}` is `𝓕 k`-measurable so it pulls out), and the martingale property of `M`. Adaptedness of the partial-sum process is by `Finset.stronglyMeasurable_sum`; integrability of each summand is `Integrable.bdd_mul`. No new Mathlib infrastructure needed.

**Result.** Lean code lives in `benchmarks/martingales.json` entry `mart-thm-2.2.9`. Verifies in Docker. Promoted from `reduced_core` to `full`.

**Estimated effort.** 1–2 focused days (matched estimate).

### A.4 `pp-thm-3.3.8` — Sum of n iid Exp(λ) is Gamma(n, λ)

**Textbook claim.** For `X_1, ..., X_n` iid `Exp(λ)`, `∑ X_i ∼ Gamma(n, λ)`.

**Status: BLOCKED at v4.18.0 for the full distribution claim.**

**Audit (2026-05-07).** Three independent gaps in Mathlib `v4.18.0`:

1. **No measure convolution operator.** No `Measure.conv` / `Measure.convolution`. Mathlib has function convolution (`Mathlib/Analysis/Convolution.lean`) but not packaged measure convolution.
2. **No `mgf_expMeasure` / `mgf_gammaMeasure`.** `Mathlib/Probability/Moments/Basic.lean` defines `mgf` and proves `iIndepFun.mgf_sum`, but no closed-form MGF for Exp / Gamma. Would need to be proved by integrating the PDF (∫ exp(t·x) · r·exp(-r·x) dx = r/(r-t) for t < r).
3. **No MGF uniqueness theorem.** `Mathlib/Probability/Moments/ComplexMGF.lean` carries an explicit TODO acknowledging this gap. `Measure.eq_of_mgf_eq` does not exist.

**Partial-derivation path.** Can derive the *MGF identity* `mgf (∑ Xᵢ) μ t = ∏ mgf Xᵢ μ t` via `iIndepFun.mgf_sum` (real derivation, ~10 lines once `mgf_expMeasure` is in place). This captures the analytic content but cannot be lifted to the distribution-equality claim without MGF uniqueness.

**Alternative.** AFP (Isabelle's Archive of Formal Proofs) has more developed convolution-of-measures and characteristic-function infrastructure. A switch of the benchmark's active backend to Isabelle is feasible but requires the Docker image to install AFP (currently only `HOL-Probability` is prebuilt).

**Estimated effort to unblock in Lean.** 2–4 weeks: define `Measure.conv`, prove `iIndepFun → Measure.map (X+Y) μ = Measure.map X μ ⋆ Measure.map Y μ`, prove `mgf_expMeasure`, prove MGF uniqueness via characteristic-function inversion.

### A.5 `dist-exp-min` — Min of independent exponentials is Exp(∑ λ_i) — **DONE 2026-05-07 (survival-function form)**

**Textbook claim.** For `τ_1, ..., τ_n` jointly independent with `τ_i ∼ Exp(λ_i)`, `min(τ_1, ..., τ_n) ∼ Exp(∑ λ_i)`.

**Approach used.** Real derivation of the survival-function identity `μ{ω | t < min_i τ_i ω} = ENNReal.ofReal (exp(-(∑ rates) · t))` for `t ≥ 0` from joint independence and individual exponential laws. Steps: (1) `expMeasure_Ioi`: derive `expMeasure r (Set.Ioi t) = ofReal (exp(-r·t))` via complement of `Iic` + `ProbabilityTheory.ofReal_cdf` + `exponentialCDFReal_eq`; (2) `iIndepFun.meas_iInter` with comap-witness `⟨Set.Ioi t, measurableSet_Ioi, rfl⟩` gives `μ(⋂_i {τ_i > t}) = ∏ μ{τ_i > t}`; (3) combine with `exp_law` to push each marginal to `expMeasure (rates i)`; (4) `Real.exp_sum` collapses the product. Same level of formal rigor as `dist-exp-memoryless` (both are CDF-level identities); structure no longer axiomatizes the conclusion as a field.

**Result.** Lean code in `benchmarks/distributions.json` entry `dist-exp-min`. Verifies in Docker. Promoted from `reduced_core` to `full`.

**Estimated effort.** ~2 hours for proof + Docker iteration.

### A.6 `dist-thm-B.1.2-marginal` — Multivariate Gaussian marginal

**Textbook claim.** If `X = D · W + μ` with `W` a vector of iid `N(0, 1)`, then each `X_i ∼ N(μ_i, Σ_{ii})` where `Σ = D · Dᵀ`.

**Status: BLOCKED at v4.18.0.** Multivariate Gaussian is **not in Mathlib**. Mathlib only has 1D `gaussianReal`. Building `gaussianMv μ Σ : Measure (ι → ℝ)` (for finite `ι` and PSD `Σ`) — and proving its marginals are 1D Gaussian — is a Mathlib-scale contribution.

**Path.** Build a Mathlib-style multivariate Gaussian. Define it as the distribution of `D · W + μ` for `W` iid standard normal. The 1D marginal is a finite linear combination of independent standard normals plus a constant — Mathlib has `gaussianReal_const_mul`, `gaussianReal_add_const`. Sum-of-independent-Gaussians lemma is also missing in v4.18.0 (research confirms: "even Gaussian doesn't have a sum-of-two-Gaussians-via-convolution lemma in v4.18.0"). So building `gaussianMv` requires also building Gaussian convolution.

**Estimated effort.** 2–4 focused weeks. Significant Mathlib contribution.

### A.7 `dist-thm-B.1.3-conditional` — Bivariate Gaussian conditional expectation

**Textbook claim.** For `(X, Y)` jointly Gaussian: `E[X | σ(Y)] = μ_X + (ρ σ_X / σ_Y)(Y − μ_Y)` almost surely.

**Status: BLOCKED at v4.18.0.** Depends on A.6 multivariate Gaussian construction.

**Path.** Once `gaussianMv` exists, the conditional is a calculation: decompose `X = (ρ σ_X / σ_Y)(Y − μ_Y) + Z` where `Z` is Gaussian independent of `Y` with mean `μ_X`. Apply `condExp_indep_eq` for `Z`'s contribution.

**Estimated effort.** 1–2 focused weeks after A.6.

### A.8 `mc-thm-1.4.40` — Convergence to stationary distribution (finite state)

**Textbook claim.** For an aperiodic, irreducible, finite-state Markov chain: `lim_{n → ∞} P^n(i, j) = π_j` for every starting state `i`.

**Status: STILL BLOCKED (Lean and AFP).** Mathlib has prerequisite definitions (`Matrix.IsIrreducible`, `Matrix.IsPrimitive`, `doublyStochastic`, `IsMarkovKernel`) but no Perron–Frobenius for stochastic matrices, no convergence-of-powers theorem, and no aperiodicity definition. AFP probe (2026-05-08, `Stochastic_Matrix_Perron_Frobenius`): the entry contains `stationary_distribution_exists` and `stationary_distribution_unique` but **no `lim P^n` / `tendsto`** statement about iterating the stochastic matrix. So even with the expanded AFP install, A.8 is not directly wrappable; the spectral-gap convergence theorem would have to be proved on top of the Perron–Frobenius API.

**Path.** Either (a) build the convergence statement on top of AFP `Perron_Frobenius` / `Stochastic_Matrix_Perron_Frobenius` — the dominant-eigenvalue + simple-eigenvalue results are available, but the rate-of-convergence step still needs to be formalized; or (b) build from scratch in Mathlib (stochastic-matrix typeclass, aperiodicity, Perron–Frobenius for irreducible non-negative matrices, spectral-gap convergence of P^n).

**Estimated effort.** 4–8 focused weeks (real linear-algebra contribution, multiple PRs) in either Mathlib or AFP.

### A.9 `mc-thm-1.4.32` — Ergodic theorem for finite-state Markov chains — **DONE 2026-05-08 (AFP `Ergodic_Theory` library wrapper)**

**Textbook claim.** For an irreducible, aperiodic, positive recurrent (finite-state ⇒ automatic) Markov chain: `(1/n) ∑_{k=0}^{n-1} f(X_k) → E_π[f]` almost surely.

**Approach used.** Isabelle wrapper of `Ergodic_Theory.Ergodicity.birkhoff_theorem_AE` inside the `ergodic_pmpt` locale. The textbook claim is the specialization of Birkhoff's pointwise ergodic theorem to the path-space shift with the stationary measure as initial distribution; the wrapper records that specialization. The Lean side is a specification structure (`reduced_core`); the Isabelle side directly invokes the AFP theorem.

**Result.** Lean+Isabelle code in `benchmarks/markov_chains.json` entry `mc-thm-1.4.32`. Isabelle verifies via session `Ergodic_Theory` (43.92s in Docker). Promoted from `reduced_core` to `library_wrapper`. Router updated to dispatch `ergodic_theory` Isabelle-first.

### A.10 `mc-thm-1.4.25` — Stationary distribution uniqueness (finite state)

**Textbook claim.** For an irreducible, finite-state Markov chain (positive recurrence is automatic in finite state): the stationary distribution is unique.

**Status: UNBLOCKED via AFP `Stochastic_Matrices` (2026-05-08 probe).** The entry `Stochastic_Matrix_Perron_Frobenius` exposes:

- `stationary_distribution_exists`: `∃ v. A *st v = v` (every stochastic matrix admits a stationary distribution).
- `stationary_distribution_unique`: `fixed_mat.irreducible (st_mat A) ⟹ ∃! v. A *st v = v` (uniqueness under irreducibility).

A direct Isabelle wrapper of `stationary_distribution_unique` matches the textbook claim. A Markov-chain-flavoured variant in the `transition_matrix` locale is also available.

**Wiring done.** `python/isabelle_backend.py` recognizes the `Stochastic_Matrices`, `Perron_Frobenius`, and `Jordan_Normal_Form` AFP namespaces. `docker/Dockerfile.verify` now prebuilds `Stochastic_Matrices` alongside `Ergodic_Theory` and `Markov_Models`.

**Pending.** Docker image must be rebuilt with the new prebuild list before this entry can be promoted from `reduced_core` to `library_wrapper`. The wrapper itself is one short Isabelle theorem; do not promote until `docker compose run verify benchmarks/markov_chains.json` confirms green.

**Estimated effort.** ~1 hour to write the wrapper and Docker-iterate, after the next image rebuild lands.

### A.11 `mc-thm-1.3.12` — Recurrence criterion (finite state)

**Textbook claim.** State `i` is recurrent ⇔ `∑_{n=1}^∞ P^n(i, i) = ∞`.

**Status: STILL BLOCKED.** AFP `Markov_Models.Classifying_Markov_Chain_States` has the closely-related `recurrent_iff_U_eq_1` (`recurrent s = (U s s = 1)`) and the generating-function machinery `gf_G_eq_gf_F`, `gf_G_eq_gf_U`. Bridging from this to the textbook ∑P^n(i,i) form requires a real-analysis step (limit z→1 of the generating function `gf_G` equals the diagonal sum `G x x = ennreal (∑n. p x x n)`), which is non-trivial in Isabelle and not packaged as a single AFP lemma. Deferred.

**Path.** For finite state, all states in a recurrent class are positive recurrent (so `P^n(i, i) → π_i > 0`, so the sum is `+∞`); transient states have `P^n(i, i) ≤ ρ^n` for `ρ < 1` so the sum is finite. Both directions follow from A.8 + classical state-classification — so this stays subsumed by A.8 in Lean. In AFP, an alternative direct route via `gf_G_eq_gf_U` plus `Abel_summation` exists but needs proof engineering.

**Estimated effort.** 1 focused week after A.8 (Lean) or ~1 week of Isabelle bridging on top of `Markov_Models` (AFP).

### A.12 `mart-thm-2.6.7` — FTAP for finite-state finite-period markets (⇒ direction) — **DONE 2026-05-07 (with bounded-strategy hypothesis)**

**Textbook claim.** Existence of an equivalent martingale measure `Q` ⇒ no arbitrage.

**Approach used.** Embed the martingale-transform helper (mart-thm-2.2.9) inline (each benchmark is verified in isolation, so cross-benchmark composition requires duplication). With a bounded predictable strategy `φ`, the discounted P&L `V` is a `Q`-martingale by the embedded theorem; `E_Q[V_T] = E_Q[V_0] = 0` (with `V_0 = 0`); `V_T ≥ 0 P-a.s.` lifts to Q-a.s. via `Q ≪ P`; `integral_eq_zero_iff_of_nonneg_ae` then forces `V_T = 0 Q-a.s.`; finally `P ≪ Q` lifts the Q-zero set `{V_T > 0}` to a P-zero set.

**Result.** Lean code in `benchmarks/martingales.json` entry `mart-thm-2.6.7`. Verifies in Docker. Promoted from `reduced_core` to `full`.

### A.13 `mc-thm-1.1.2` — Path factorization for general Markov chains — **DONE 2026-05-07 (constructive definition)**

**Textbook claim.** `P(X_0 = i_0, ..., X_n = i_n) = λ_{i_0} ∏_{k=0}^{n-1} P(X_{k+1} = i_{k+1} | X_k = i_k)` for any Markov chain.

**Approach used.** Constructive: `pathProb` is **defined** as `initial × ∏ transitions` directly. The textbook factorization theorem becomes `rfl`. Same definitional pattern as `bm-def-5.1.1` (structural definition of standard Brownian motion) and `cv-poisson-def`. A future stronger version, when Mathlib has a discrete-time Markov-chain object, would derive `pathProb` from the kernel composition.

**Result.** Lean code in `benchmarks/markov_chains.json` entry `mc-thm-1.1.2`. Verifies in Docker. Promoted from `reduced_core` to `full`.

### Tier A summary

13 theorems. Status as of 2026-05-08: **6 done** (A.1, A.3, A.5, A.9, A.12, A.13), **1 ready-to-wrap pending Docker rebuild** (A.10), **6 remaining**:

| Target | Status | Blocker |
|--------|--------|---------|
| A.2 Doob L^p | partial — helpers verified locally | Fubini swap + Hölder + ENNReal algebra remaining; sketch in `docs/superpowers/sketches/doob_lp_v1.lean` |
| A.4 sum exp → Gamma | blocked | No measure convolution; no MGF uniqueness |
| A.6 MV Gaussian marginal | blocked | No multivariate Gaussian in Mathlib |
| A.7 bivariate Gaussian conditional | blocked | Depends on A.6 |
| A.8 Markov chain convergence | blocked | No `lim P^n` theorem in Mathlib or AFP `Stochastic_Matrices` |
| A.10 stationary uniqueness | wired, pending | Wrapper around AFP `stationary_distribution_unique`; needs Docker rebuild |
| A.11 recurrence criterion | blocked / deferred | AFP has gf_G/gf_U but limit z→1 bridging not packaged |

Total remaining estimated effort:

- **A.2** (~1–3 days, feasible at v4.18.0): highest-leverage near-term target.
- **A.4** (~2–4 weeks): build measure convolution + MGF uniqueness in Mathlib, OR add AFP `Sum_of_Exponentials`-like entry.
- **A.6/A.7** (~3–6 weeks): build multivariate Gaussian in Mathlib (genuinely missing).
- **A.8** (~4–8 weeks): build spectral-gap convergence of P^n on top of AFP `Perron_Frobenius`, or build the same in Mathlib.
- **A.10** (~1 hour after Docker rebuild): wrap `stationary_distribution_unique` as a Markov-chain wrapper; promote `mc-thm-1.4.25`.
- **A.11** (~1 week): bridging `gf_G` to the diagonal sum `G x x = ∑ p x x n` in Isabelle (or after A.8 in Lean).
- **A.9** (~1 day if switching to Isabelle/AFP backend; else after A.8).

The blockers are honest infrastructure gaps in Mathlib `v4.18.0`. Tier A is ~40% complete (5/13).

## Tier B — Needs Brownian Motion First

11 theorems. Each reduces to "first build a Mathlib-grade Brownian motion." The Mathlib community has been working on this for years; following / contributing to that effort is the path.

- `bm-prop-5.1.2` Gaussian-process characterization of BM.
- `bm-thm-5.1.4` BM Markov property.
- `bm-thm-5.1.5` BM martingale property.
- `bm-rmk-5.1.6-square` `B²_t − t` is a martingale.
- `bm-rmk-5.1.6-exp` Wald exponential martingale.
- `bm-thm-5.1.7` Reflection principle.
- `bm-thm-5.3.2` Hölder continuity (needs Kolmogorov continuity).
- `bm-cor-5.3.4` Nowhere differentiability.
- `bm-thm-5.3.5` Law of the iterated logarithm.
- `sc-thm-6.1.1` BM quadratic variation.

Once Brownian motion exists in Mathlib, several of these follow quickly:

- The martingale property and `B² − t` martingale follow from the increment law and the conditional-expectation API.
- The Wald exponential martingale follows from `mgf_gaussianReal` and the moment-generating-function characterization.
- Reflection principle requires the strong Markov property of BM, which Mathlib will need to develop.
- Hölder regularity needs Kolmogorov continuity (a real foundational theorem; not yet in Mathlib).
- Nowhere differentiability needs additional path-regularity machinery.
- LIL needs Borel–Cantelli (Mathlib has it) + careful tail-event analysis.

**Tier B is not in scope for this round.** Track Mathlib's progress on Brownian motion construction.

## Tier C — Needs the Stochastic Integral

21 theorems. Requires Tier B plus an Itô-integral construction (each component is research-grade).

- `sc-thm-6.2.5` Itô isometry.
- `sc-thm-7.1.1` Itô formula (1D).
- `sc-thm-7.1.2` Time-dependent Itô formula.
- `sc-thm-7.5.2` Two-dimensional Itô formula.
- `sc-thm-7.4.5` Itô process quadratic variation.
- `sc-thm-9.1.1` Lévy characterization.
- `sc-thm-9.1.8`, `gir-thm-9.1.7`, `gir-thm-9.1.8` Novikov + Girsanov (multiple versions).
- `gir-thm-9.3.4` Martingale representation theorem.
- `sc-thm-9.2.1` Feynman–Kac.
- `sc-thm-8.2.5` SDE existence/uniqueness.
- `sc-bs-pde`, `gir-bs-call-formula` Black-Scholes PDE / call price.
- `cm-thm-4.3.7` Stopped continuous martingale (needs continuous-time martingale).
- `cm-thm-4.3.9` Continuous-time Doob maximal inequality.
- `cm-thm-4.3.10` Continuous-time L^p martingale convergence.
- `mc-thm-1.2.11` Strong Markov property (general-state, continuous-time analogue).
- `pp-prop-3.3.6` Poisson interarrival exponential (needs the arrival-time formulation of a Poisson process).
- `pp-thm-3.3.9` Poisson superposition (needs the Poisson convolution + process-level argument).
- `pp-thm-3.3.10` Poisson thinning.

These are not in scope for the next stage. Keep the specifications as documentation.

## Recommendation

**Stage 1 (next 1–3 months).** Tier A.1, A.2, A.3 in order. These are the upstream-eligible pieces and they exercise the Mathlib `condExp` / `Submartingale` API. Each successful contribution lands as a Mathlib PR.

**Stage 2 (3–6 months).** Tier A.4, A.5 (distributions); then A.8 / A.10 / A.11 (Markov chain Perron–Frobenius cluster).

**Stage 3 (6+ months).** Tier A.6, A.7 (multivariate Gaussian — bigger contribution); A.9 (ergodic theorem); A.12 (FTAP); A.13 (Markov chain layer).

**Tier B / Tier C.** Follow upstream Mathlib Brownian-motion / stochastic-integral progress; contribute when prerequisites land. Keep the specifications as `reduced_core` documentation in the meantime.

## Working Rules

1. Pick one Tier A target. Open a working branch.
2. Write the proof iteratively in a Lean file inside the relevant benchmark JSON. Verify in Docker after each step.
3. Once the proof compiles end-to-end, replace the spec / algebraic-core Lean snippet in the benchmark with the real proof. Update `formalization_status` to `full` and `formalization_scope` to describe what was actually proved.
4. Run `python3 -m pytest tests/test_router.py` and `python3 -m python.coverage_report` before committing.
5. Where the result is a Mathlib-eligible lemma (A.1, A.2, A.3, A.6, etc.), open a Mathlib PR.
6. Do NOT inflate `full` based on a spec-with-axiomatized-conclusion. The proof must do real work.

## Out of Scope For This Document

- Scheduling and project management.
- Detailed Mathlib-PR writing guidance (already documented in Mathlib's contribution guide).
- The infrastructure for Brownian motion construction (Mathlib has its own working group on this).
