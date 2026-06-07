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
**239 / 261 delivery-ready** (221 full + 18 library wrappers), 22 reduced cores, 0 placeholders.

> **Poisson cluster + Itô-QV upgrade round (2026-06-05).** Four reduced cores
> earned `full` by replacing statement-level specs with genuine derivations,
> each backed by a new `Foundations/` module: `pp-thm-3.3.9` (superposition —
> the Poisson convolution identity `Poisson(a) ∗ Poisson(b) = Poisson(a+b)`,
> absent from Mathlib, proved by singleton-ext + binomial collapse;
> `PoissonSuperposition.lean`), `pp-thm-3.3.10` (thinning — the
> binomial-marking factorisation into `Poisson(pr) ×ₘ Poisson((1−p)r)`, so the
> thinned marginals AND the independence of the streams are derived;
> `PoissonThinning.lean`), `pp-thm-3.3.5` (marginal law re-earned via the
> interarrival-construction route this file had flagged: Erlang arrival law
> composed with the new Gamma-CDF difference identity
> `∫₀ᵗ γ_k − ∫₀ᵗ γ_{k+1} = e^{−rt}(rt)ᵏ/k!`; `PoissonCounting.lean`), and
> `sc-thm-7.4.5` (QV of an Itô process in the constant-σ/Lipschitz-drift
> regime — drift contributes nothing, with explicit `1/n` L² rates;
> `ItoProcessQV.lean`; the previous spec was degenerate — its "stochastic
> piece" was a Lebesgue integral of σ). `pp-prop-3.3.6` stays `reduced_core`
> honestly but its core is now derived, not assumed: the FIRST interarrival
> is proved exponential from the counting axioms and the memoryless survival
> factorisation is proved from independent increments
> (`PoissonInterarrival.lean`); the full-sequence iid claim still needs the
> strong Markov property (upstream-gated). Net: **225 full + 18 wrappers =
> 243 / 261 delivery-ready, 18 reduced cores.**

> **Finance layer over the Poisson/QV track (2026-06-06).** Six new `full`
> entries make the freshly-derived foundations load-bearing in the pricing
> layer: `mf-variance-swap-drift-immunity` (realized variance of GBM
> log-returns → `σ²T` in **L²** for ANY drift — the variance-swap fair
> strike is a QV functional, immune to the physical-vs-risk-neutral drift;
> strengthens the phase-34 expectation-level limit;
> `VarianceSwapDriftImmunity.lean`, first pricing consumer of
> `ItoProcessQV`), `mf-first-to-default-spread` (FtD basket spread = Σ
> single-name hazards under independence — `ExpMin.minimum_survival`
> bridged into the `Credit.lean` vocabulary; `FirstToDefault.lean`),
> `dist-poisson-pgf` (the Poisson pgf `E[x^N] = e^{r(x−1)}` for every real
> `x`, absent from Mathlib; `PoissonPgf.lean`), and the Merton (1976)
> jump-diffusion trio (`mf-merton-call-series`,
> `mf-merton-spot-recombination`, `mf-merton-put-call-parity`): the price
> is *defined* as the expectation over the Poisson jump count, so the
> textbook series, the compensation identity `E[spot_N] = S₀` (the pgf at
> `1+k`), and parity `C − P = S₀ − Ke^{−rT}` are theorems — and every
> series term is separately proved equal to a discounted conditional
> expected payoff (`bs_call_formula` on `(ℝ, gaussianReal 0 1)`).
> Terminal-mixture-law scope, exactly parallel to `BSCallHyp`: the
> compound-Poisson jump *SDE* is upstream-gated and not claimed
> (`MertonJumpDiffusion.lean`). Net: **231 full + 18 wrappers = 249 / 267
> delivery-ready, 18 reduced cores** (corpus 261 → 267).

> **Merton dominance + classic display; Markov path law (2026-06-06, second
> round).** Two new `full` entries deepen the Merton layer:
> `mf-merton-dominance` — *jump risk is never free*,
> `C_BS(S₀,σ) ≤ C_Merton(S₀,σ,k,δ,Λ)` for every `Λ`, `δ`, `k > −1`, proved
> by pricing the two jump channels separately: per-term vol-monotonicity
> (`bsV_strictMonoOn_sigma`, vega) lowers the jump vol to `δ = 0`, and there
> a Jensen floor comes from the new spot-direction convexity
> `bsV_spot_convexOn` (gamma ≥ 0 second-derivative test, the S-direction
> dual of `bsV_strike_convexOn`; `SpotConvexity.lean`) whose supporting
> tangent at `S₀` has its linear term integrate to zero by the compensation
> identity `integral_mertonSpot` (`MertonDominance.lean`). And
> `mf-merton-classic-display` — the textbook `Λ′ = Λ(1+k)` form, driven by
> the rate-shift invariance
> `bsV K r σ (S·e^{cτ}) τ = e^{cτ}·bsV K (r+c) σ S τ`
> (`bsV_spot_exp_rate_shift`) at `c_n = r_n − r` plus Poisson-weight
> absorption (`MertonClassicDisplay.lean`). One reduced core earned `full`:
> `mc-thm-1.1.2` (path distribution of a Markov chain) — the chain's law is
> now *constructed* via the pin's Ionescu–Tulcea trajectory kernels
> (`Kernel.trajMeasure`) from kernels that read only the last history
> coordinate, and `P(X₀=i₀,…,Xₙ=iₙ) = init(i₀)·∏ P(iₖ,iₖ₊₁)` is derived by
> induction through the comp-product recursion of the marginals, replacing
> the prior definitional `rfl` (`Foundations/MarkovPathMeasure.lean`; the
> converse characterization is not claimed). The same `Kernel.traj` re-cost
> found the other five Markov reduced cores still honestly gated: recurrence
> needs renewal theory / fundamental-matrix algebra, convergence needs
> Perron–Frobenius, the ergodic theorem needs both, stationarity-uniqueness
> needs recurrence, and the strong Markov property needs stopping-time
> kernels — none in the pin. Net: **234 full + 18 wrappers = 252 / 269
> delivery-ready, 17 reduced cores** (corpus 267 → 269).

> **Values-gates round (2026-06-06, evening).** The honesty conventions this
> file documents became *mechanically enforced*: `tests/test_values.py` adds
> (1) a forbidden-text scan over `MathFin/` sources (no
> sorry/admit/native_decide/polyrith/`?`-suggestion tactics/hammer/loogle/
> leansearch outside comments), (2) a **definitional-`rfl` tripwire** — no
> `full` entry may cite a theorem whose proof is bare `rfl`/`unfold; rfl`
> (the reduced_core pattern in disguise), (3) blueprint-spine ⊆ curated
> audit, (4) byte-freshness of the new GENERATED exhaustive audit
> `MathFin/AxiomAuditGen.lean`, which `#guard_msgs`-pins every
> proof-position MathFin constant cited by the corpus (222 names vs the
> curated file's headliners). CI (`build.yml`) now runs pytest + `ledger
> status` before the Lean build, so these gates and ledger freshness are
> push-enforced, not session discipline. First-run catches: the tripwire
> demoted `mf-kelly-n-periods-linearity` `full`→`reduced_core` (its cited
> lemma states `T·kellyGrowth = T·(unfolded formula)` by `rfl`; the genuine
> multi-period iid model is not formalized — same class as the 2026-05-29
> newton-raphson demotion, now pinned in `EXPECTED_REDUCED_CORE_THEOREMS`),
> and the blueprint-coverage check found seven spine headliners unguarded
> (including `bs_identity`), now pinned in the curated audit. Net: **233
> full + 18 wrappers = 251 / 269 delivery-ready, 18 reduced cores.**

> **Summit A′ round (2026-06-07).** Two reduced cores earned `full`, each by
> replacing the named gap with the actual mathematics. (1)
> `mf-kelly-n-periods-linearity` — repairing the previous round's
> definitional-`rfl` demotion: the n-period iid model is now real measure
> theory (`Performance/Kelly.lean`): one period's wealth multiplier is the
> two-point law `kellyReturnMeasure p b f`, n periods are its n-fold
> `Measure.pi`, and `E[∑ log Rᵢ] = n·kellyGrowth p b f` is *computed* via
> linearity of expectation through the product measure's coordinate
> evaluations. (2) `sc-thm-7.1.2` — the **time-dependent Itô formula**
> (Summit A′): `f(T,B_T) − f(0,B₀) = ∫₀ᵀ f_x(s,B_s) dB_s +
> ∫₀ᵀ (f_t + ½f_xx)(s,B_s) ds` a.e., the classical `df = f_x dB +
> (f_t + ½f_xx) dt`, with the stochastic integral the genuine
> `itoIntegralCLM_T`. The three Summit-A limit arguments redone with
> `(t,x)`-dependence: `WeightedQuadraticVariation` generalized to bounded
> **adapted weight processes** (the fluctuation engine never cared the
> weight was `g(B_s)`; `tendsto_riemann_L2_process` exported standalone for
> the drift term), the 2D Itô–Taylor remainder vanishing at `O(1/n)`
> (`ItoFormulaTDRemainder.lean` — time/cross/space split bounded by
> `C_tt Δt² + C_tx|ΔB|Δt + C_xxx|ΔB|³`), and the time-dependent Riemann↔CLM
> bridge (`ItoIntegralRiemannBridgeTD.lean`). Assembly in
> `Foundations/ItoFormulaTD.lean`; `f_t`'s joint continuity is *derived*
> from its bounded partials (jointly Lipschitz), not assumed; unbounded
> coefficients stay the named gap, as in 7.1.1. All four new headliners
> axiom-pinned in the curated audit and the spine node
> `thm:ito-formula-td-l2` added. Net: **235 full + 18 wrappers = 253 / 269
> delivery-ready, 16 reduced cores.**

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
> self-dot variance identity, consuming Mathlib's `variance_sum'`
> (`Portfolio/CovariancePSD.lean`);
> `mf-cvar-rockafellar-uryasev` — the genuine **Rockafellar–Uryasev variational
> theorem** (`IsLeast`) for the Gaussian loss, minimality by the pointwise tail
> certificate (`RiskMeasures/RockafellarUryasev.lean`, which previously recorded
> only the additive identity and explicitly deferred this);
> `mf-newton-raphson-fixed-at-root` — genuine **local quadratic convergence**
> at the sharp Newton–Kantorovich constant `(L/(2m))·e²` (integral form of the
> Taylor remainder) + basin convergence of the Newton iterates
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

> **Post-audit values sweep (2026-06-04, follow-up).** A second adversarial
> audit (four fresh reviewers over the Path-1 commit) confirmed the
> load-bearing layer — counts, statuses, scope notes, axiom pins, and the
> absence of all five headline theorems from Mathlib/BrownianMotion all
> re-verified independently — and surfaced finishing work, applied in full:
> `submartingale_optional_sampling` now consumes Mathlib's
> `Submartingale.monotone_predictablePart` (the local helper had re-derived it
> verbatim) and documents the BrownianMotion package's `sorry`-stubbed `⊓`-form
> sibling as an upstream-donation candidate;
> `portfolioVarN_covariance_eq_variance` consumes `variance_sum'` instead of
> re-tracing its bilinearity chain; **Newton sharpened to the textbook
> constant** — `(L/(2m))·e²` via the integral form of the Taylor remainder,
> basin relaxed to `L·δ ≤ m` (the uniform mean-value bound had silently cost a
> factor 2); two dead `have`s and an orphaned `@[simp]` lemma removed; the
> seven upgraded entries' stale `description` fields rewritten (four still
> asserted pre-upgrade "NOT the stronger result" disclaimers); and the build
> log swept clean — six `ring`-falls-back-to-`ring_nf` info sites and one
> `simpa` lint fixed at root (`congr`/`convert` depth bumps so `ring` sees a
> genuine ring goal instead of `exp A = exp B`).

> **Headline-theorem wiring (2026-06-04, same day).** The library's deepest
> results were benchmark-orphaned — proved on main since 2026-05-30 and
> AxiomAudit-pinned, but visible in no benchmark entry. Three entries added,
> each verified L5 in-container before landing:
> `mf-crr-gaussian-limit` (`crr_tendsto_gaussian_inDistribution` — the
> distributional CLT for the CRR tree: per-step charFun computed exactly,
> upgraded to weak convergence by Lévy's continuity theorem),
> `mf-crr-bs-call-convergence` (`binomialPrice_call_tendsto_bs_closed` — the
> n-step binomial call price converges to the literal
> `S₀·Φ(d₁) − K·e^{−rT}·Φ(d₂)`; bounded-put + put-call-parity route, no
> uniform-integrability machinery), and `gir-continuous-ftap`
> (`discountedGBM_isMartingale` — the discounted GBM is a martingale under
> the risk-neutral measure: the EMM property, i.e. the operational
> continuous-time first FTAP). The stale `mf-crr-prob-half` scope sentence
> claiming the distributional convergence "is upstream-gated on
> triangular-array CLT" (false since 2026-05-30) was corrected to point at
> the new entries. In the same pass, all 157 stale `lean/MathFin/<X>.lean`
> prose path references (the pre-reorg flat layout) were remapped to the real
> `MathFin/<Section>/<X>.lean` paths, using each entry's own compiled imports
> as the authoritative mapping (the old combined files that were *split* in
> the reorg — e.g. `StrikeConvexityAndRiskAdditivity.lean` — map to different
> targets per entry, which a global rename table would have gotten wrong);
> the ten entries whose snippet docstrings changed were re-verified
> in-container.

The line below is the pre-re-audit historical record (kept for provenance):
**235 / 251 delivery-ready** (211 full + 24 library wrappers), 16 reduced cores, 0 placeholders.

## History

Per-pass session logs and the pre-2026-05 hybrid-backend validation records
were removed from this file on 2026-05-30, when the SymPy and Isabelle backends
were stripped (the project is Lean-only). They remain in git history. The
2026-05-29 honesty re-audit — the basis for the current counts above — is also
recorded in `docs/deep-review-2026-05-29.md`.
