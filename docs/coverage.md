# Formalization Status

This project distinguishes two claims:

1. **Backend verification coverage:** active Lean code checks successfully.
2. **Faithful theorem formalization:** the checked statement closely matches the course theorem AND the proof is a real derivation, not a structural projection from an axiomatized conclusion.

The first claim is useful engineering evidence. The second is the academic claim. Do not collapse them.

## Status Vocabulary

- `full`: a faithful formal **derivation** of the textbook theorem from its hypotheses. The hypotheses must be encoded honestly (not the conclusion in disguise) and the proof must do real work — `ring`/`simp`/`rfl` on a structure-projection target does NOT qualify.
- `library_wrapper`: the active code directly invokes a named Lean library theorem whose statement matches the benchmark theorem. The library does the real work.
- `reduced_core`: the active code is honest but narrower than the textbook theorem. This includes:
  - Algebraic / analytic / distributional core checks (e.g., a constant-θ MGF identity behind Wald's exponential).
  - Lean specifications where the textbook conclusion is encoded as a structure field and the proof reads it off via projection. The structure pins down the textbook STATEMENT but does not derive the conclusion.
- `placeholder`: active prover code verifies but does not yet encode a meaningful formal statement of the textbook theorem.

For delivery claims, count only:

```text
full + library_wrapper
```

Report `reduced_core` and `placeholder` separately. **Spec-with-axiomatized-conclusion is `reduced_core`, not `full`.**

## Current Audit

Refresh with:

```bash
python3 -m tools.verify.coverage_report
```

Coverage as of 2026-05-20 (extended mathematical-finance pass: put greeks, higher-order BS greeks, Bachelier greeks, digital greeks, BS-Merton with dividends, Garman-Kohlhagen FX, Black-76 greeks; second pass: Bachelier γ/θ, asset-or-nothing γ, BS-Merton δ/γ/vega, American options in binomial tree; third pass: CRR drift-quotient limit closing the analytic content of CRR-to-BS; fifth pass: cash-or-nothing digital gamma closing the previously deferred quotient-rule item; sixth pass: full digital ρ/vega/θ matrix for cash and asset variants — 6 theorems closing the remaining digital Greek gap; seventh pass: Black-76 ρ and θ closing the futures-options Greek set; eighth pass: CRR drift limit n-form `n·(2p_n−1)·σ·√(T/n) → (r−σ²/2)T` closing the previously deferred substitution work; ninth pass: Phase 5 broader mathematical-finance — fixed-income ZCB pricing/yield/duration/convexity, two-asset Markowitz portfolio theory with completing-the-square factorization, CAPM beta + portfolio linearity — 12 theorems extending the project beyond derivatives pricing into fixed income and portfolio theory; tenth pass: Phase 6 quant-risk + N-asset portfolio + bond immunization — Gaussian VaR/CVaR closed forms with affine/scaling identities, bond portfolio rate sensitivity + Redington-style first-order immunization, N-asset Markowitz variance via Finset double sum with diagonal/iid/PSD/two-asset specializations — 15 theorems; eleventh pass: Phase 7 performance / coherent risk / fixed-income depth / static bounds / two-fund separation — Sharpe (√T scaling + scale invariance) + Kelly criterion, gaussian VaR/CVaR coherent risk-measure axioms (translation, homogeneity, monotonicity, gaussian subadditivity via joint-stdev triangle inequality), annuity geometric-series closed form + forward/spot consistency + coupon-bond YTM monotonicity, Phi ≤ 1 + BS call/put price upper bounds + box-spread arbitrage identity, capital market line equation + Sharpe invariance + two-fund decomposition — 23 theorems extending the project into performance measurement, axiomatic risk, and multi-fund portfolio theory; twelfth pass: Phase 8 extended performance / second-order immunization / Asian option inequality — Sortino/Treynor/Information ratios + tracking-error decomposition, second-derivative bond rate sensitivity ∂²P/∂r² = C_P·P + Redington second-order convexity-matching immunization, two-element and equal-weight n-element AM-GM with two-date geometric ≤ arithmetic Asian payoff bound — 13 theorems; **thirteenth pass: Phase 9 credit-risk + strike Greeks + multi-period Kelly** — reduced-form credit spread under constant hazard with survival monotonicity, BS strike-direction derivatives (∂_K bsV, ∂_K bsP, ∂²_K bsV) via magic-identity collapse + put-call parity, multi-period Kelly criterion with myopia + fraction sign analysis — 14 theorems):
**236 / 258 delivery-ready** (218 full + 18 library wrappers), 22 reduced cores, 0 placeholders.

> **Duplication + status audit (2026-06-03).** A five-reviewer sweep of all 216
> then-`full` entries asked two questions: does any MathFin module re-derive
> content already in pinned Mathlib / Degenne's BrownianMotion package, and is
> any `full` really a wrapper? The foundations tower came back clean — the
> package at pin `fa590b1` has **no** sorry-free L²-adapted stochastic integral
> (it stops at the elementary simple-process integral), no strong-type Doob L^p
> (weak-type only — same as Mathlib, whose own docstring defers the L^p version),
> no Wald/X²−t martingales, no Itô formula; our Wiener-vs-Itô division and the
> BrownianMartingale division-of-labor header were re-verified accurate. The
> Portfolio/Performance/Risk/FixedIncome slice had zero findings (geometric
> series, Cauchy–Schwarz etc. are consumed from Mathlib, never re-proved).
> Verified findings, all applied: `full`→`library_wrapper`:
> `ce-prop-2.1.11-jensen` (Mathlib's `ConvexOn.map_condExp_le_of_finiteDimensional`
> proves textbook Jensen from bare convexity; our explicit-subgradient derivation
> was strictly weaker — `Foundations/CondExpJensen.lean` deleted, benchmark now
> wraps Mathlib), `mf-carr-madan-log` (was a `Real.log_div` alias; alias lemma
> deleted), `cv-prob-space` (`measure_univ`/`measure_empty`).
> `full`→`reduced_core`: `pp-thm-3.3.5` and `mc-thm-1.1.2` (THEOREM-named entries
> whose conclusion is a projected structure field / definitional `rfl`; definition
> entries `bm-def-5.1.1`/`cv-poisson-def`/`mc-def-1.1.1` keep the documented
> definitional-`full` convention). Coherence fix: `am_gm_two` now specializes
> Mathlib's `Real.geom_mean_le_arith_mean2_weighted` instead of re-proving it;
> documented-distinction cross-references added for the Carr–Madan second-order
> remainder (the `n = 1` case of Mathlib's `taylor_integral_remainder`, kept in
> explicit-`HasDerivAt` form) and the StandardNormal MGF (pdf-form vs Mathlib's
> measure-form `mgf_gaussianReal`). New guardrail:
> `test_expected_reduced_cores_stay_reduced_core`. Upstream opportunity recorded
> in `docs/bridges.md` (our L² martingale convergence could discharge the
> package's sorry'd `SquareIntegrable` targets).

> **Honesty re-audit (2026-05-29).** A dedicated benchmark-`formalization_status`
> sweep (four adversarial reviewers over all 11 files / 251 theorems, every
> finding source-verified) reclassified **13 over-credited entries**, dropping
> delivery-ready from 235→222. The pattern was the same one found in the Itô
> stack: a benchmark named after a deep theorem but proving only an algebraic
> shadow / a conclusion read off a hypothesis / an unfaithful library wrapper.
> Reclassified `full`→`reduced_core`: `mf-tangent-portfolio-foc` (FOC by `ring`,
> no calculus), `mf-american-supermartingale` + `mf-american-intrinsic-bound`
> (`le_max` on the Bellman def, not the measure-theoretic supermartingale),
> `mf-kmv-merton-pd` (only the ≤1 bound proved), `mf-markowitz-n-psd`
> (conclusion-in-hypothesis), `mf-newton-raphson-fixed-at-root` (definitional
> unfold), `mart-thm-2.3.6` (wraps the bounded-time submartingale *inequality*,
> not the UI optional-stopping *equality*). `full`→`library_wrapper`:
> `bm-thm-5.1.5` (one-line Degenne re-export). `library_wrapper`→`reduced_core`:
> the 5 `markov_chains` entries whose `library_wrapper` credit rested on a
> since-removed second backend while the active Lean code is a structural
> specification (matching how `poisson_processes` already tiers its structural
> entries). See `docs/deep-review-2026-05-29.md`.
>
> **Upgrade-properly round (2026-05-29).** Rather than only relabel down, two of
> those entries were *earned back to `full`* by re-pointing the benchmark at the
> genuine derivation that **already existed** in the library (the benchmark had
> been wrapping the shallow algebraic lemma instead): `mf-tangent-portfolio-foc`
> now wraps `sharpeSqTwo_critical_iff_crossProduct_FOC` (the Sharpe FOC as a
> genuine `HasDerivAt` critical-point characterisation), and `mf-kmv-merton-pd`
> now wraps `kmvPD_eq_one_sub_survival_probability` (KMV PD = the actual
> risk-neutral default probability `1 − Q(V_T>F)`, via `riskNeutralProb_S_T_gt_K`).
> Both re-pointed snippets were compile-verified. Balancing this, the algebraic
> shadow `mf-kmv-survival-Phi-d2` (the normal-CDF symmetry `1 − Φ(−x) = Φ(x)`,
> previously `full`) was demoted to `reduced_core`. Net: 222→223 delivery-ready,
> but now backed by the genuine theorems. The remaining reduced_core entries are
> either inherently one-line facts (no deeper theorem exists) or gated on
> machinery not yet in Lean — relabeling *those* up would re-introduce the
> overclaim.

> **Summit A — continuous-time Itô formula (2026-06-02).** Promoted `sc-thm-7.1.1`
> (Itô's Formula) `reduced_core`→`full`: the bounded-derivative continuous-time L² Itô
> formula `f(B_T)−f(B_0) = itoIntegralCLM_T gf' + ½∫₀ᵀ f″(B_s) ds` is now *derived* from
> foundational primitives, with the stochastic integral the genuine continuous Itô integral
> `itoIntegralCLM_T gf'` (the L²-limit of the Riemann–Itô sums). The proof chain (Summit A):
> `tendsto_weighted_qv` (weighted quadratic variation) + `tendsto_ito_remainder` (vanishing
> Itô–Taylor remainder) + `itoIntegralCLM_T_of_bdd_cont` (Riemann↔CLM bridge), assembled in
> `ito_formula_L2_bddDeriv`. Scope: `f ∈ C³` with bounded `f′,f″,f‴` — a faithful but
> strictly C³-bounded specialization of the C² textbook statement (the gap to unrestricted
> C² is Summit C localization, not yet formalized). All four Summit-A theorems are
> `#print axioms`-clean (AxiomAudit-pinned). `coverage_report`: `stochastic_calculus.json`
> 4→5 full, 7→6 reduced.

> **Engine→pricing coherence — deliberate stop (2026-06-03).** The continuous Itô
> engine `itoIntegralCLM_T` has its flagship consumer (`itoIntegralCLM_T_brownian`:
> `∫₀ᵀ B dB = ½(B_T²−B₀²−T)` through the CLM), and the operational continuous-time
> pricing result — the discounted GBM is a `Q`-martingale (`discountedGBM_isMartingale`,
> via the Wald exponential) — is already proved (an AxiomAudit-pinned library theorem). The one *missing* link, identifying the
> discounted price *with* the engine (`e^{−rt}S_t = S₀ + itoIntegralCLM_T(σ·e^{−r·}S_·)`),
> was scoped and **declined**: the GBM exponential is unbounded, so it is not a short
> argument but a second keystone (~400 lines — a parallel clamp-truncation layer plus the
> martingale-difference L² limit `∑σM_{t_k}ΔB → M_T−1`). It would yield an *alternative
> derivation route* to a theorem already held, not a new result, so it is recorded here as
> a known, bounded, **not-pursued** build. See *Geometric Brownian motion* /
> *Continuous-time first FTAP* in `blueprint.md`.

> **Path-1 upgrades (2026-06-04).** Seven reduced cores earned `full` by the
> upgrade-properly discipline (build the genuinely deeper theorem; never relabel):
> `mart-thm-2.3.6` — the conditional-expectation-form **optional sampling
> inequality** for submartingales (`Foundations/OptionalSamplingInequality.lean`),
> absent from Mathlib, derived as *optional sampling equality + monotone
> compensator* through the Doob decomposition;
> `mf-markowitz-n-psd` — PSD **derived** from genuine L² random returns via the
> self-dot variance identity on Mathlib's covariance API
> (`Portfolio/CovariancePSD.lean`);
> `mf-cvar-rockafellar-uryasev` — the genuine **Rockafellar–Uryasev variational
> theorem** (`IsLeast`) for the Gaussian loss, minimality by the pointwise tail
> certificate (`RiskMeasures/RockafellarUryasev.lean`, which previously recorded
> only the additive identity and explicitly deferred this);
> `mf-newton-raphson-fixed-at-root` — genuine **local quadratic convergence**
> `(L/m)·e²` + basin convergence of the Newton iterates
> (`BlackScholes/NewtonConvergence.lean`);
> `mf-kmv-survival-Phi-d2` — re-pointed at the probabilistic survival statement
> `Q(V_T > F) = Φ(DD)` through the lognormal tail;
> `mf-american-supermartingale` + `mf-american-intrinsic-bound` — the
> **path-space Snell envelope** (`Binomial/SnellEnvelope.lean`): payoff
> dominance, supermartingale property, adaptedness, and minimality over
> arbitrary path-processes, plus the identification theorem
> `snell = e^{−rk}·americanPrice` exhibiting the scalar Bellman recursion as
> the Markov instance (the conditional expectation is the explicit node
> average, which on a finite tree it *is* — same pathwise idiom as
> `Binomial/MartingaleRepresentation.lean`).
> All new load-bearing theorems are AxiomAudit-pinned.

The line below is the pre-re-audit historical record (kept for provenance):
**235 / 251 delivery-ready** (211 full + 24 library wrappers), 16 reduced cores, 0 placeholders.

## History

Per-pass session logs and the pre-2026-05 hybrid-backend validation records
were removed from this file on 2026-05-30, when the SymPy and Isabelle backends
were stripped (the project is Lean-only). They remain in git history. The
2026-05-29 honesty re-audit — the basis for the current counts above — is also
recorded in `docs/deep-review-2026-05-29.md`.
