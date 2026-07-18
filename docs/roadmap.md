# Math depth roadmap

This document captures the strategic discussion from 2026-05-22 on what
"ultimate Lean/Mathlib mathematical finance repo" actually means, why depth beats
breadth at this stage, and what the concrete next round would look like.

---

## 2026-06-29 — POST-ITÔ STRATEGIC UPDATE: the gate is open (supersedes the "out of reach" framing below)

> **Update (2026-07-16) — optimal market making, single-asset closed-form (corpus 330 → 333).** A new
> breadth axis opens: `Foundations/MarketMakingRiccati` formalizes the single-asset (`d = 1`) closed-form
> (LQ/Riccati) approximation of Bergault–Evangelista–Guéant–Vieira (arXiv:1810.04383). Three `full`
> entries — the Riccati coefficient `mf-mm-riccati` (`a(t) = Â·tanh(Â(T−t))` solves `a' = a² − Â²`; the
> `tanh` derivative is derived locally, Mathlib carrying none at this pin), the value-function verification
> `mf-mm-value-function` (the quadratic ansatz solves the **approximate** quadratic-Hamiltonian HJ equation
> given the Riccati/linear ODE system — Prop. 1 at `d = 1`, the `B`/`C` coefficients certified by the `ring`
> closure), and the closed-form quotes `mf-mm-quotes` (constant half-spread + inventory-linear skew,
> instantiated at the Model-A/Model-B constants). **Honest scope** (mirroring `mf-almgren-chriss-EL`): the
> *approximate* HJ solution only — the stochastic-control substrate (true value function + verification
> theorem), the approximation-to-truth (numerical in the paper), the multi-asset matrix-Riccati case, and the
> `T → ∞` ergodic limit are deferred follow-ups. Natural next rungs: the **matrix Riccati** (multi-asset, via
> `Matrix.exp` + spectral decomposition) and the Appendix-A **jump (Brémaud–Jacod) Girsanov** construction
> (wiring into the change-of-measure engine).
>
> **Update (2026-07-16, later) — the matrix Riccati rung landed (corpus 333 → 335).** The multi-asset
> follow-on above is now done: `Foundations/MatrixMarketMakingRiccati` formalizes the **matrix-Riccati core of
> BEGV Proposition 2** (the `A`-coefficient + change of variables; `B`/`C` and the value-function verification
> stay out of scope), the matrix analogue of the scalar closed form. Two `full` entries — `mf-mm-matrix-riccati` (the abstract matrix
> Riccati ODE `a'(t) = a(t)·a(t) − Â·Â` solved in closed form for any Hermitian `Â`) and `mf-mm-matrix-value`
> (its market-making instantiation `A' = 2·A·D₊·A − (γ/2)·Σ` via the `D₊^{±½}` change of variables). The key
> move is **spectral reduction, not `Matrix.exp`**: with `Â = U·diag(λ)·Uᴴ`, defining
> `a(t) = U·diag(riccatiCoeff (λᵢ) T t)·Uᴴ` reduces the matrix ODE, on each eigenvalue, to the *scalar*
> `hasDerivAt_riccatiCoeff` — no matrix `tanh` (absent at this pin) is ever built. Mathlib carries no
> matrix-valued differentiation, so the matrix-level `HasDerivAt` is taken under the `L∞` operator norm
> (`open scoped Matrix.Norms.Operator`), lifting the diagonal core's derivative through `diagonalLinearMap`.
> **Honest scope**: in `mf-mm-matrix-value`, `Â` enters by its defining relation `Â·Â = γ·(D₊^{½}ΣD₊^{½})`
> (the matrix-square-root *construction* is out of scope — the verified content is the change of variables);
> the `B`/`C` coefficients (matrix variation-of-parameters), the general-`d` value-function verification, and
> the optimal-control substrate remain deferred.
>
> **Direction (course-correction, 2026-07-16).** These two entries are a deliberate *flag-plant* — the
> library's first matrix-analytic finance (eigendecomposition, a committed matrix-norm policy, spectral
> reduction) — not the start of a market-making build-out. The Riccati is the **LQ-approximation** view; the
> *fundamental* structure is the exact Hopf–Cole linearisation of the Avellaneda–Stoikov HJB into a linear
> ODE system / matrix exponential (Guéant–Lehalle–Fernandez-Tapia), which the exact multi-asset problem lacks
> a closed form for (hence BEGV approximate). So we **stop the Riccati drill** here: the `B`/`C` refinements,
> the matrix-sqrt existence, and the `T→∞` limit are *within-the-approximation* items, deprioritised. If we
> ever deepen market making, the honest target is the **exact linearisation** (a real project, matrix-exp-gated),
> not more approximation. Market making is a stochastic-control *satellite*, orthogonal to the library's depth
> spine (Itô → Girsanov → FTAP); the leverage stays on that spine — the DMW FTAP crown, the 2D covariation Itô,
> Girsanov L²/Novikov — which is where results compound. (The Appendix-A **jump Girsanov** remains a candidate
> only because it wires into the existing change-of-measure engine, not because it grows the MM island.)
>
> **Update (2026-06-29, evening) — Phase 1 done (corpus 306).** Since this strategic update, the
> **convex-duality unification** (I↔IV — the architecture doc's #1 seam,
> [`mathematical-architecture.md`](mathematical-architecture.md)) was realized: the FTAP (pricing) and
> the coherent-risk representation (risk) are now *one* Hahn–Banach root (`Foundations/ConvexDuality`,
> `RiskMeasures/AcceptanceSet`). That was the most-tractable, highest-leverage seam (finite-dim convex
> analysis, no Itô dependency). The Itô-track crown jewels below are next — **Girsanov (#2)** is the
> queued bridge ([#40](https://github.com/raphaelrrcoelho/formal-mathfin/issues/40); first brick = the
> adapted Doléans–Dade exponential), and the superhedging strong-duality *equality* hit a Mathlib
> **Farkas gap** ([#39](https://github.com/raphaelrrcoelho/formal-mathfin/issues/39)).

> **Update (2026-06-30) — Phase 2: Girsanov, the martingale side (corpus 308).** The continuous EMM is
> now an *explicit* change of measure: `Foundations/Girsanov.bs_discounted_isQMartingale` tilts the
> physical measure by the Girsanov density `Q = withDensity(exp(−θX_T − ½θ²T))` (constant `θ = (μ−r)/σ`)
> and proves the discounted stock a `Q`-martingale on `[0,T]`, on a reusable Bayes engine
> `Foundations/ChangeOfMeasure.changeOfMeasure_setIntegral_eq` — **retiring the Wald shortcut**. The
> feasibility spike confirmed the tower's blocker: the general adapted Doléans–Dade exponential needs an
> **Itô formula for a function of an `∫θ dB` process** (and a pathwise QV `⟨∫θdB⟩ = ∫θ² ds`), *neither*
> present — every `ito_formula_*` is `f(t,B_t)`, and QV exists only in expectation. So general adapted
> `θ` and the *distributional* Girsanov (`gir-thm-9.1.8`, drift-corrected `B^θ` is `Q`-Brownian) stay
> `reduced_core`, honestly documented — an Itô-tower item to re-scout, not force. See
> [#40](https://github.com/raphaelrrcoelho/formal-mathfin/issues/40).

> **Update (2026-07-05) — Phase 2 distributional Girsanov, CONSTANT θ FULLY CLOSED (corpus 314).** The
> re-scout paid off: for *constant* `θ` the distributional Girsanov is now complete —
> `Foundations/GirsanovConstantTheta.Btheta_isQBrownianMotion` proves the drift-corrected
> `B^θ_t = X_t + θ t` is a genuine `Q`-Brownian motion: zero start, Gaussian increments
> `B^θ_t − B^θ_s ~ N(0, t−s)`, **and** independence of disjoint increments (corpus `gir-const-theta-qbm`,
> `full`; marginal `gir-const-theta-marginal`, `full`). Crucially this needs **no** adapted-integrand Itô
> formula and **no** "conditional-MGF ⟹ independence" lemma (a presumed Mathlib gap — only the reverse
> `condExp_indep_eq` exists): the independence is reached via `indepFun_iff_charFun_prod`, factorising the
> Gaussian joint characteristic function through the Gaussian law of every linear combination of the
> increments (from the joint-MGF factorisation, a `condExp_mul` pull-out). All
> on the existing Bayes engine + Wald exponentials + Mathlib's characteristic-function machinery.
> **Refactored 2026-07-06:** this ten-lemma characteristic-function chain is now the reusable,
> process-agnostic `Foundations/ExpMartingaleQBrownian.isQBrownianMotion_of_expMartingale` — const-θ
> supplies only its exponential martingale (`expBtheta_isQMartingale`, as `IsExpQMartingale`) and
> instantiates it; the simple-/continuous-θ Route-α bricks reuse the same seam. See
> [#40](https://github.com/raphaelrrcoelho/formal-mathfin/issues/40).
>
> **Update (2026-07-06) — SIMPLE (piecewise-constant) adapted θ FULLY CLOSED (corpus 315).** The
> abstraction paid off: `Foundations/GirsanovSimpleTheta.Btheta_simple_isQBrownianMotion` (corpus
> `gir-simple-adapted`, `full`) proves `B^θ_t = X_t + ∑_i c_i(s_{i+1}∧t − s_i∧t)` is a `Q`-Brownian
> motion for bounded `𝓕_{s i}`-measurable multipliers — the general bounded-**adapted**-θ Girsanov for
> the simple case, strictly beyond constant θ, via the spine `simple_spine_ae` fed to the Bayes engine
> with an `L²`-Hölder mixed-time integrability, and one application of `isQBrownianMotion_of_expMartingale`
> (no charFun chain re-derived). What now stays `reduced_core` is only the **fully general
> continuous-adapted** θ (`gir-thm-9.1.8`) — it is infrastructure-gated, not sorry-blocked: the tower has
> the Itô-integral CLM isometry (`itoIntegralCLM_T`) and simple-integrand density, so what remains is the
> **σ-realization** `processToLp_of_bdd_adapted_cont` (a bounded adapted *continuous* integrand as an `L²`
> predictable class) plus an `L²→L¹` density-convergence step — its own focused effort (brick α4, see
> `docs/plans/2026-07-06-girsanov-track-alpha.md`).

> **Update (2026-07-10) — bounded PREDICTABLE θ CLOSED (Girsanov Rung 1, corpus 319).** The Girsanov
> ladder extends one more rung: `Foundations/GirsanovPredictableTheta.Btheta_isQBrownianMotion_predictable_of_bdd`
> (new `full` entry `gir-thm-9.1.8-predictable`) drops the path-continuity of `gir-thm-9.1.8` and proves
> `B^θ_u = B_u + driftContinuousMod θ̂ u` is a `Q`-Brownian motion for a bounded **predictable** `θ` — the
> honest domain of the Itô `L²` integral. The front half is a **Route-B marshalled** density approximation:
> `θ` is approximated in `L²` by clamped dense simple processes marshalled into single-partition `(s,c)`
> form (`Foundations/SimpleProcessPartition.lean`), so the simple-θ exponential-martingale identity applies
> per `n`; where the continuous case had the drift converge *everywhere* (deterministic Riemann sums), here
> **all three** integrand functionals — stochastic integral, drift, quadratic variation — converge only in
> `μ`-measure (via the drift-modification tower's `L²`-slice energy identity), and are fused through a
> **common a.e.-subsequence** (`exists_subseq_tendsto_ae₂`) into the same set-integral engine plus a generic
> Fatou-`L²` limit (`memLp_two_of_subseq_ae_of_sq_bound`, used for both the density and the mixed-time
> product), keyed on the partition-generic moment bounds of `Foundations/GirsanovSimpleDoleansMoments.lean`.
> The limit drift is the genuinely-`𝓕`-adapted `driftContinuousMod θ̂` (=ᵐ `∫₀ᵘθds`), so no fresh
> predictable-progressive lemma was needed. **Rung 2** (fully general `L²`/progressive θ under Novikov,
> unbounded, `sc-thm-9.1.8`) remains `reduced_core`.

> **Update (2026-07-09) — CONTINUOUS bounded-adapted θ FULLY CLOSED; Track-α COMPLETE (corpus 318).** Both
> gating pieces named above landed, and `gir-thm-9.1.8` flips `reduced_core → full`:
> `Foundations/GirsanovAdaptedTheta.Btheta_isQBrownianMotion_adapted` proves `B^θ_u = B_u + ∫₀ᵘθ ds` is a
> `Q`-Brownian motion for a bounded (`|θ| ≤ C`), `𝓕`-adapted, path-continuous `θ`, under
> `Q = μ.withDensity(exp(−∫₀ᵀθ dB − ½∫₀ᵀθ² ds))`. The route is **spine-free**: rather than build a
> continuous Doléans stochastic exponential and prove it a martingale (a Novikov crux), the simple-θ
> exponential-martingale identity (on the `unifPart` approximants `c⁽ⁿ⁾_i = θ(tᵢ)`) is passed to the limit —
> the stochastic exponent `Wⁿ = ∑θ(tᵢ)ΔBᵢ → ∫θ dB` in `L²` (`itoIntegralCLM_T_of_bdd_adapted_cont`), the
> drift parts converge everywhere, and the mixed-time set-integral limit goes through the a.e.-subsequence
> engine `tendsto_setIntegral_of_subseq_ae_of_sq_bound` (route-A L⁴/AM-GM uniform `L²` bound), then one
> application of `isQBrownianMotion_of_expMartingale`. This is the culmination of the constant → simple →
> continuous-adapted arc. **What now stays `reduced_core` is only the strictly more general `L²`/progressive-θ
> under Novikov (unbounded, merely progressively measurable), at `sc-thm-9.1.8`.** See
> `docs/plans/2026-07-06-girsanov-track-alpha.md` (Track-α COMPLETE).

> **Update (2026-07-07) — finance-delivery breadth: the Vasicek affine bond price + the T-forward measure
> (corpus 315 → 317, [#46](https://github.com/raphaelrrcoelho/formal-mathfin/issues/46)).** A pause on the
> Girsanov-α4 depth track to cash in two finance-delivery items off machinery already load-bearing — no new
> frontier. (1) **Vasicek zero-coupon bond price** (`FixedIncome/VasicekBondPrice`, entry
> `mf-vasicek-bond-price`, **`full`**): `P(0,T) = 𝔼[exp(−∫₀ᵀ r_s ds)]` as the Gaussian Laplace transform of the
> integrated short rate, collapsing to the **affine term structure** `P = A(T)·exp(−B(T)·r₀)`,
> `B(T) = (1−e^{−κT})/κ`. Fubini-free by carrying `∫₀ᵀ r_s ds = M(T) + σ∫₀ᵀ g dB` in its Wiener representation
> (integrated OU kernel `g(u) = (1−e^{−κ(T−u)})/κ`, exactly one integration up from the OU-solution model
> `mf-vasicek-sde-terminal-gaussian` already `full`); law from `wienerIntegralLp_hasLaw_gaussian` + the FTC
> `∫₀ᵀ g² = V(T)`; price from the centred Gaussian MGF. The `vasicekShortRate_hasLaw_gaussian` derivation is now
> load-bearing for pricing, not an orphan. (2) **T-forward measure** (`FixedIncome/ForwardMeasure`, entry
> `mf-forward-measure-spot`, **`full`**): the ZCB-as-numéraire measure `Q^T` with `𝔼^{Q^T}[S_T] = S_0/P(0,T) =
> F(0,T)` — the natural next `changeOfNumeraire` instance the finance-delivery track wanted, honestly scoped
> (degenerate `Q^T = Q` under the constant-rate ZCB; construction carries to stochastic rates). **Not built,
> honestly:** CVaR's Rockafellar–Uryasev variational theorem was found **already complete**
> (`gaussianCVaR_isLeast_ruObjective`), as was the coherence quartet; the geometric-Asian *closed-form price*
> (only the AM-GM payoff bound `mf-asian-geom-le-arith-two` exists) stays open — it needs the BM joint-Gaussian
> covariance `(1/n²)∑∑min(tᵢ,tⱼ)`, a focused effort not to be rushed. Depth track (Girsanov-α4) resumes next.

> **Update (2026-07-08) — geometric-Asian lognormality, the two-date crux (corpus 317 → 318).** The
> geometric-Asian item the note above flagged open is now **partially closed**: `mf-asian-geom-driver-gaussian`
> (`BlackScholes/AsianGeometric.asianGeom_driver_hasLaw`, **`full`**) proves the two-date log-driver
> `(B_s + B_t)/2 ~ N(0, (3s+t)/4)`, turning `√(S_s·S_t)` into a priceable lognormal. The joint-Gaussian
> `∑∑min` obstacle dissolved via the Vasicek trick — read the sum of Brownian values as a single Wiener
> integral of a deterministic step kernel — enabled by a new **foundational brick**,
> `Foundations/WienerIntegralIndicator.wienerIntegralLp_stepIndicator` (`∫ 𝟙_{(s,t]} dB = B_t − B_s`, from
> `LinearMap.extendOfNorm_eq`). The n-date extension (Finset covariance sum) is now unblocked — a mechanical
> follow-on. Depth track (Girsanov-α4) resumes next.

> **DELIVERED (2026-07-03) — SDE existence made pathwise: the E-fixed point as a sample-path process
> ([#19](https://github.com/raphaelrrcoelho/formal-mathfin/issues/19) → existence bridge).** The Picard
> solution, previously banked only as the abstract `L²`-fixed point `picardSolution ∈ E`, is now realized
> as a genuine **pathwise** process. `Foundations/SDEPathwise.sde_pathwise_decomposition` slices the
> fixed-point equation `X = Φ(X)` into the sample-path identity
> `X_t(ω) = η(ω) + driftContinuousMod(b∘X)_t(ω) + itoContinuousMod(σ∘X)_t(ω)`. The enabling crux —
> `Foundations/DriftProcessModification.driftProcessAssembled_coeFn` — identifies the abstract
> `extendOfNorm` drift operator's `coeFn` with the honest pointwise-`limUnder` drift `driftContinuousMod`
> a.e.; it is **proved** (the Itô side gets the analog for free by construction) via two convergences of
> `driftSimpleProcessLp Vₙ` (CLM-continuity and a.e., the latter from `driftContinuousMod_tendsto` — a
> **direct Chebyshev** maximal bound, no martingale — lifted per-slice→trim through the
> predictable-measurable convergence set) that are unique in measure. Axiom-clean, pinned in `AxiomAudit`.
> **Drift refined to the honest single integral (#33, same session):**
> `DriftProcessModification.driftContinuousMod_eq_setIntegral` proves `driftContinuousMod g t ω =
> ∫₀ᵗ ⇑g(s,ω) ds` a.e. for every `t ≤ T` (subsequence from the `L¹(μ)` decay of the ω-slice energies
> `Dₙ = ‖simpleAssembly_T Vₙ − g‖²`, then interval Cauchy–Schwarz); `SDEPathwise.sde_pathwise_drift_eq_setIntegral`
> specializes it to `b∘X`, so the strong solution's drift term is the recognizable `∫₀ᵗ b(X_s) ds`. The
> pathwise-existence bridge is now complete on the drift side, all axiom-clean.

> **DELIVERED (2026-07-02) — SDE existence via Picard
> ([#44](https://github.com/raphaelrrcoelho/formal-mathfin/issues/44)).** The strong solution of
> `dX = b(X)dt + σ(X)dB` is now **constructed as a Picard fixed point** in the predictable `L²` space `E`,
> its diffusion term the actual assembled Itô integral: `Foundations/SDEExistence` proves the contraction
> estimate `‖Φ X − Φ Y‖ ≤ (T·L_b + √T·L_σ)‖X − Y‖` and gets existence **and** uniqueness via Banach's
> theorem (`picardMap_exists_unique_fixedPoint`), delivered as the **`full`** entry
> `sde-picard-existence-uniqueness`. **Honest remainder:** the `L²`/`E` formulation, conditional on the
> small-horizon contraction constant `< 1`. (The abstract-operator benchmark `sc-thm-8.2.5` has since had
> its **uniqueness** half flipped to **`full`** by a *direct* pathwise Grönwall argument — see #19 below —
> rather than by the `ℝ≥0`↔`ℝ` E-translation.)

> **DELIVERED (2026-07-03) — SDE strong-solution uniqueness via the L²-energy Grönwall argument
> ([#19](https://github.com/raphaelrrcoelho/formal-mathfin/issues/19)).** The **uniqueness half of Theorem
> 8.2.5** (`sc-thm-8.2.5`) is now a genuinely *derived* theorem — flipped **`reduced_core` → `full`**.
> `Foundations/SDEUniqueness` proves two `L²` strong solutions of `dX = μ(X)dt + σ(X)dB` sharing the driver
> agree a.s. at every time: the state energy `E t = 𝔼[(Xₜ−Yₜ)²]` satisfies `E t ≤ (2·Cdrift·t+2·Cdiff)·∫₀ᵗE`
> and `gronwall_zero_of_le_const_mul_integral` (a reusable integral Grönwall obtained from Mathlib's
> differential form via the FTC primitive `G t = ∫₀ᵗ E`) forces `E ≡ 0`. The **drift** bound is *derived*
> from Lipschitz `μ` (`drift_energy_le`: Cauchy–Schwarz in time + Tonelli); the **diffusion** rides the Itô
> isometry. `IsL2SolutionPair.uniqueness` packages it — uniqueness is a **theorem, not an assumed field**
> (the honest reading of "translate to the structure fields"), guarded by a non-vacuity example. **Honest
> remainder:** the uniqueness *half* only (existence stays the conditional-`E` Picard result); the
> diffusion's sole assumed property is the Itô isometry energy bound — a proven property of the Itô
> integral (`itoProcessCLM_norm_sq`), cited, not the conclusion.

> **DELIVERED (2026-07-03) — the change of numéraire, both seam directions (substantial advance on
> [#45](https://github.com/raphaelrrcoelho/formal-mathfin/issues/45)).** (1) `Foundations/Numeraire.changeOfNumeraire`
> is the abstract price-invariance law `N₀·𝔼^{Q^N}[X/N_T] = B₀·𝔼^Q[X/B_T]` (density `dQ^N/dQ = (N_T·B₀)/(N₀·B_T)`,
> no integrability hypothesis), **`full`** entry `mf-change-of-numeraire`, **consumed** by two instances — the
> BS stock numéraire (`stockNumeraireMeasure_eq_numeraireMeasure`) and Margrabe's `S²`-numéraire
> (`exchangeOption_numeraire_price`, entry `mf-exchange-numeraire`). (2) `Performance/KellyNumeraire.kellyNumeraire_isRiskNeutral`
> (entry `mf-kelly-numeraire-emm`) delivers the *log-optimal = numéraire ⇒ EMM* direction: the growth-optimal
> (Kelly) wealth as deflator turns the physical measure into the EMM, the `p`-independence being the Kelly FOC.
> **Honest remainder for #45:** direction (2) is the **discrete, two-outcome** shadow; the **continuous**
> Long/Platen benchmark (deflated prices are `P`-martingales for a continuous market) still needs a
> state-price-density model absent from the tower. #45 stays open for that continuous core.

> **Forward — two tracks (name the axis first).** The remaining work splits cleanly, and the axis
> decides the phase:
> - **Finance-delivery track** (finance theorems — the q-fin.MF / "formal theory of finance" artifact):
>   the **numéraire bridge** IV↔I ([#45](https://github.com/raphaelrrcoelho/formal-mathfin/issues/45) —
>   change-of-numéraire formula + `S²`-numéraire instance + the discrete Kelly numéraire-portfolio ⇒ EMM
>   all delivered 2026-07-03; only the *continuous* Long/Platen benchmark still OPEN); the forward-measure
>   (bond numéraire) instance is the natural next `numeraireMeasure` instance; **finance
>   breadth** ([#46](https://github.com/raphaelrrcoelho/formal-mathfin/issues/46) — exotic + American
>   options, Vasicek bond pricing, coherent-risk/CVaR breadth). These ship finance results — bridges and
>   theorems like convex-duality (I↔IV) and Feynman–Kac (II↔III).
> - **Depth / landmark track** (Mathlib-absent formalization landmarks — the AI4Math axis): SDE existence
>   ([#44](https://github.com/raphaelrrcoelho/formal-mathfin/issues/44)); general adapted-θ Girsanov
>   ([#40](https://github.com/raphaelrrcoelho/formal-mathfin/issues/40)); superhedging strong duality /
>   finite-dim Farkas ([#39](https://github.com/raphaelrrcoelho/formal-mathfin/issues/39)); the
>   generator/Kolmogorov (II↔III) and Cox/intensity (IV) abstractions (plan Phases 5.1–5.2). These deepen
>   a pillar; they do not ship a finance result. **The 2026-05-22 head below (breadth vs depth) is the
>   same tension, now named by axis.**

A whole-program validation (three independent reviewers + maintainer adjudication + the env-linter)
re-grounds the strategy. **The 2026-05-22 head below is now partly stale, and that staleness is the
single most important finding.** That section says the deep tier is *"out of reach … needs a fuller
stochastic-calculus layer (unrestricted Itô, continuous-time Girsanov, BSDEs)"* and files Girsanov/SDE
under *"explicitly out of scope (itô-gated, do not attempt without upstream)"* — predicting *"when Itô
lands, the deepest quant results become possible."* **Itô has since landed** (Summits A–C; the phase log
records it). The library spent a month building the exact gate it named, then never walked through it.

**Validation verdict (where the program stands):**
- **Floor — solid.** An adversarial pass over the headline `full` entries (Itô tower, BS-PDE keystone,
  FTAP rungs, CRR→BS, Greeks) found no overclaims: hypotheses honest, scope documented, axioms clean.
- **Infrastructure — exceeds world-class in rigor, with minor cosmetic gaps.** The input-hash
  verification ledger, per-theorem `#print axioms` audit, kernel-replay, and the values-review cadence
  exceed what Mathlib/FLT/Carleson ship. Genuine gaps are operational/cosmetic: no doc-gen4 API site,
  no Leanblueprint web render. (The env-linter is now wired — `lake lint`, advisory.)
- **Itô tower — publishable-grade, scalar-by-design, with navigability friction.** The Summit-C
  double-cutoff localization is exemplary. Scalar-only is deliberate. Real debt: naming-suffix drift
  (`_T`/`_Infinite`/`_TD`/none) and no single exported "the Itô formula."
- **THE CEILING — the 17 `reduced_core` entries.** These are spec-level *encodings* (a `structure`
  whose fields assume the conclusion), written when the deep theorems were genuinely out of reach.
  **Girsanov, SDE existence/uniqueness, martingale representation, Lévy's characterization are stubs.**
  This — a magnificent Itô tower whose deepest intended consumers are still stubs — is the precise gap
  between "very-good structural-depth library" and "top-notch stochastic-finance library."

**The path to top-notch — cash in the Itô tower (verified reachable, NOT upstream-gated):**
The crown-jewel conversions build on assets that already exist (`waldExponential_isMartingale`,
`itoIntegralCLM_T` + its isometry, `withDensity` change-of-measure, the static `GaussianGirsanov`
Esscher tilt). They do **not** depend on the one genuinely upstream-gated frontier (general
adapted-coefficient Itô, blocked on Degenne's continuous-modification π-system). Ranked by value × feasibility:

| # | Conversion (reduced_core → full) | Value | Difficulty | Unlocks |
|---|---|---|---|---|
| 1 | **Novikov** (gir-thm-9.1.7) | 9 | MEDIUM (~150-200 ln) | the gateway: the adapted Doléans-Dade exponential `Z_t=exp(∫θdB−½∫θ²ds)` as a martingale |
| 2 | **Girsanov** — martingale + distributional (const → simple → continuous adapted) ✅ (2026-06-30 → 2026-07-09) | 9 | DONE (bounded adapted continuous θ): `bs_discounted_isQMartingale` = the EMM as an explicit measure change + a reusable Bayes engine; the distributional Girsanov `Btheta_isQBrownianMotion` (const) → `Btheta_simple_isQBrownianMotion` (simple) → **`Btheta_isQBrownianMotion_adapted` (bounded adapted continuous, `gir-thm-9.1.8` `full`)**, all one application of the process-agnostic `isQBrownianMotion_of_expMartingale` — spine-free, no adapted-integrand Itô formula, no Novikov crux. Only the strictly more general `L²`/progressive-θ under Novikov (`sc-thm-9.1.8`) stays open | risk-neutral pricing under measure change |
| 3 | **SDE existence/uniqueness** (sc-thm-8.2.5) | 9 | HIGH (~300-400) | the SDE model zoo (Vasicek/CIR/Heston/jump-diffusion) — Picard on the Itô isometry |
| 4 | **Martingale representation** (gir-thm-9.3.4) | 9 | HIGH (Clark-Hida; may need upstream) | hedging / replication / market completeness |
| 5 | **2D Itô formula** (sc-thm-7.5.2) | 7 | LOW-MED | multi-asset derivatives (the 1-D TD formula is already built) |

The **first brick** for #1-#3 is the same: the adapted **Doléans-Dade stochastic exponential** as a
martingale — generalizing the existing constant-α Wald exponential to an adapted integrand via
`itoIntegralCLM_T`. Lay it once; Novikov, Girsanov, and the SDE drift-term all consume it.

**Lower-leverage / deliberately deferred** (per the reviewers): the Markov-chain reduced_core cluster
(side branch for a *continuous-time* finance library), the reflection principle / LIL / nowhere-diff
(canonical BM results, no finance consumers). **Engineering polish** (friction, not ceiling): the
Itô-tower naming consolidation, a bundled `IsBrownianMotion` structure, a doc-gen4 site, Leanblueprint
web. Do these to remove friction; they do not raise the mathematical ceiling.

**Bottom line:** the program is already top-tier in rigor and floor-integrity. The distinctive move to
top-notch is not more breadth or polish — it is to **convert the crown-jewel `reduced_core` stubs into
genuine derivations**, starting with the Doléans-Dade exponential → Novikov → Girsanov chain. That is
the work that turns "a deep tower" into "a deep tower that is actually used."

---

## The honest distinction

There are three different things people mean by "high-quality formal
math library":

* **Coverage**: most textbook results in the field are formalised.
  Measured by theorem count.
* **Structural depth**: the library organises results around a small
  number of *principles* whose consequences flow as one- to three-line
  corollaries. The hierarchy is visible in the file structure.
* **Original mathematics**: theorems in the library are *contributions* to
  mathematics, not formalisations of textbook material. Mathlib's
  reputation rests largely on this (sphere eversion, Polynomial
  Freiman-Ruzsa, etc.).

Our library is at *medium coverage + partial structural depth + no
original mathematics*. The third tier is out of reach: original quant-
finance mathematics either needs a fuller stochastic-calculus layer
(unrestricted Itô, continuous-time Girsanov, BSDEs — beyond the `[0,T]`
L² slice the library builds) or is research-
grade work (Föllmer-Schied dual, robust price bounds under model
uncertainty, Lee 2004 moment formula at full rigor).

What's *in reach* is more structural depth, which is what the next
round should pursue.

## Why depth beats breadth

* **Diminishing returns on breadth.** 250+ theorems is enough. Adding
  another 20 textbook verifications takes the count to 270 but doesn't
  change what the library *is*. The proof shape (`unfold; field_simp;
  ring`) tells the reader what the additions are.

* **Coverage gaps are mostly upstream-gated.** The remaining missing
  items — Heston, local vol, SABR, continuous-time Girsanov, BSDEs —
  need a fuller stochastic-calculus layer than the `[0,T]` L² Itô
  integral the library builds for itself. We can't fix that with more
  `field_simp`. (Itô's formula and Margrabe have since been delivered —
  see the phase log below.)

* **The slop ratio sharpens with more breadth.** Of the 216 "full"
  derivations, roughly 30 are genuinely non-trivial (the continuous-time
  L² Itô formula, Doob L^p,
  Wiener L² isometry, joint-stdev triangle, Kelly FOC, Sharpe √T,
  second-order immunization, Asian AM-GM, Merton-tree one-period
  dominance, etc.). The other ~180 are closed-form verifications.
  Adding 20 more closed-form checks moves the ratio from 30:180 to
  30:200 — the wrong direction.

* **Depth additions are multiplicative.** A reflection principle for
  binomial walks unlocks barrier-option pricing as a whole category.
  A continuous-convexity bridge collapses K-direction reasoning across
  the library. A discrete martingale representation makes hedging
  discussions tractable. Each depth theorem leverages future ones.

## What "ultimate Lean/Mathlib mathematical finance" looks like

Concretely:

1. **A small set of named structural principles** that *generate*
   the consequences. We have nine (Garman normal form, strike
   convexity, price bounds rectangle, Greek signs, convex pricing
   functional, gaussian MGF, exponential discount, Merton-tree
   one-period, replicating uniqueness). Target ~15.

2. **At least one genuinely-non-trivial theorem per category** —
   not just a definition + ring. Currently ~8 categories are represented
   among the ~30 non-trivial results above. Target ~15–20.

3. **An honest hierarchy** between foundational math, principles, and
   verifications. README now distinguishes the three tiers; file
   organisation could enforce it more strongly.

4. **Eventual upstream contributions to Mathlib** — when Itô lands,
   the deepest quant results become possible. The library's structure
   should be ready to accommodate them.

What it explicitly is *not*:

* The largest theorem count.
* The broadest textbook-chapter coverage.
* Original mathematics. Tao level is original mathematics; that's a
  different game.

## Concrete next-round candidates — STATUS

Three depth theorems were planned. As of 2026-05-22, **all three cores have
shipped** in `BlackScholes/StrikeConvexity.lean`, `Binomial/MertonAmericanCallTree.lean`,
and `Binomial/PathReflection.lean`:

1. **Multi-step Merton 1973 in the binomial tree** — DONE
   (`Binomial/MertonAmericanCallTree.lean`).
   `americanPrice = binomialPrice` at every horizon `n` for the non-dividend
   call (`r ≥ 0`, `K ≥ 0`). The one-period continuation dominance
   (Jensen + martingale identity + discount shift) extends to multi-step
   via induction on `n` with monotonicity of the one-period operator at
   the inductive step. Three new theorems: `call_intrinsic_le_binomialPrice`,
   `americanCallPrice_le_binomialPrice`, `americanCallPrice_eq_binomialPrice`.

2. **Continuous convexity of `K ↦ bsV K r σ S τ` on `(0, ∞)`** — DONE
   (`BlackScholes/StrikeConvexity.lean`). Bridges `ConvexPricingFunctional`
   (finite-state) to the actual BS formula via
   `convexOn_of_deriv2_nonneg'` + `hasDerivAt_bsV_KK`. K-convexity now
   visible at **three scales** in the library: payoff
   (`convexOn_call_payoff`), finite-state price
   (`callPrice_finiteState_convexOn_K`), continuous BS price
   (`bsV_strike_convexOn`). PDF positivity in `BreedenLitzenberger.lean`
   becomes an actual derivation rather than a standalone fact.

3. **Discrete reflection principle for binomial paths — full**
   — DONE (`Binomial/PathReflection.lean`, ~370 LOC, both halves landed).
   * **Algebraic core**: `walkPos (reflectAfter τ ω) k = 2·walkPos ω τ −
     walkPos ω k` for `τ ≤ k` (via prefix/suffix sum decomposition);
     `reflectAfter_involutive`; endpoint corollary.
   * **Hitting-time bijection**: `firstHit ω a`, invariance under
     reflection (`firstHit_reflectAfter_firstHit`), reflection-at-first-hit
     involution (`reflectAtFirstHit_involutive`), and the full
     **`reflectionPrincipleEquiv a b`** between `{ω : hits a, ends at b}`
     and `{ω : hits a, ends at 2a − b}` as a Mathlib `Equiv`. Both
     directions of the bijection are the same reflection map (involution).

Total ~600 LOC across three modules, all landing in one session. Each
ships a theorem whose statement is non-trivial and whose proof is real
math (calculus / induction / combinatorial sum decomposition,
respectively).

## Larger, multi-session candidates

If the project continues beyond the next round:

4. **Variance-optimal hedging in finite-state markets** (~250 LOC).
   Given a contingent claim `X` and a tradable subspace, the
   variance-optimal hedge is the `L²(q)`-orthogonal projection.
   Finite-dimensional Hilbert space.

5. **Discrete-time martingale representation in binomial** (~500 LOC).
   Every Q-martingale is the discrete stochastic integral of a
   predictable process w.r.t. the discounted asset. Constructive.

6. **Optimal-stopping characterisation** (~400 LOC). Snell envelope
   equals `sup_{τ stopping time} E^Q[e^{−rτ} g(S_τ)]`. Requires
   defining stopping times on the binomial path space.

7. **Carr-Madan full integral identity** (~400 LOC). Taylor with
   integral remainder for the log-payoff, expressed as static
   portfolio of OTM puts + calls. Requires `intervalIntegral`
   calculus.

8. **Carr-Lee moment formula** (~600 LOC). Existence of `E[S_T^p]`
   bounded by wing-decay rate of implied vol `σ²(K) · T`. Real-
   analytic, genuinely surprising.

## What this library can *not* become without Mathlib upstream

Honest scope statement:

* **Continuous-time Itô calculus**: Mathlib does not ship a general Itô
  integral at the current pin, so the library builds its own L²-adapted
  integral on `[0,T]` (`itoIntegralCLM_T`) and the bounded-derivative L²
  Itô formula on top of it (`ito_formula_L2_bddDeriv`); Margrabe is
  delivered via change of numéraire. Still out of reach without a fuller
  (localized / unbounded) stochastic-calculus layer: unrestricted-`C²`
  Itô, continuous-time Girsanov, Heston, local volatility, SABR, BSDEs.

* **Continuous Poisson processes**: Mathlib has the discrete
  `PoissonPMF`; continuous-time Poisson processes (interarrival
  exponential, superposition, thinning, Lévy processes) are
  upstream-gated.

* **Fine Brownian path machinery**: reflection principle for BM,
  nowhere-differentiability of BM paths, law of iterated logarithm —
  these need path-level machinery beyond what's currently in
  Mathlib's `BrownianMotion`.

The library can be excellent without these. It cannot be "complete"
mathematical finance without them.

## Conclusion

The path to "the formalization library that defines what mathematical finance
looks like in Lean/Mathlib" runs through structural depth, not theorem
count. Three depth theorems plus continued slop-folding plus honest
documentation get us a coherent library that a quant practitioner would
respect. They do not get us to Tao level — that requires original
mathematics, which is a different project.

---

# mathematical-finance roadmap (unblocked path)

the 16 remaining `reduced_core` theorems in `docs/coverage.md` are upstream-gated on the itô integral, measure-change machinery, and continuous-time poisson processes. this document captures what can be built **without** waiting on upstream mathlib or degenne work, framed as a mathematical-finance project rather than a textbook audit.

all of it either (a) reuses the existing `bsd1`/`bsd2`/`Phi`/`bs_identity`/`hasDerivAt_Phi`/`bsV` infrastructure, (b) is a parallel construction to black-scholes using the same gaussian machinery, or (c) is discrete-time / classical-analysis material that doesn't touch the itô integral.

## phase 1: complete the static black-scholes world (DONE 2026-05-18)

all six items shipped in a single session. all axioms-clean; all benchmarked as `full` in `benchmarks/mathematical_finance.json`.

- [x] **black-scholes put formula** — `BlackScholesPut.lean`. derived by direct integration on the left tail (`integral_exp_mul_gaussianPDFReal_Iic` primitive). put-call parity proved as corollary.
- [x] **vega**: `∂V/∂σ = S · ϕ(d_1) · √τ` — `BlackScholesPDE.lean` (extended). magic identity collapses both `∂_σ d_1` chain-rule contributions.
- [x] **rho**: `∂V/∂r = K · τ · e^{-rτ} · Φ(d_2)` — `BlackScholesPDE.lean` (extended). same magic-identity collapse.
- [x] **cash-or-nothing digital option** — `BlackScholesDigital.lean`. direct integration on `Ioi(-d_2)`.
- [x] **asset-or-nothing digital option** — `BlackScholesDigital.lean`. plus call decomposition `C = AssetDigital − K · CashDigital` as corollary.
- [x] **forward and futures pricing** under no-arbitrage — `BlackScholesForward.lean`. derived from Gaussian MGF; also gives the discounted-asset martingale property `E_Q[e^{-rT} S_T] = S_0`.

milestone DONE: complete BS sensitivities (delta + gamma in `BlackScholesPDE.lean`, plus vega + theta + rho) plus the full vanilla european product set (call, put, 2 digitals, forward).

## phase 2: vanilla derivatives theory complete (DONE 2026-05-18)

all three items shipped in the same session as phase 1. all axioms-clean; all `full` in `benchmarks/mathematical_finance.json`.

- [x] **bachelier model option pricing** — `BachelierModel.lean` (~330 lines). key new primitive: the **truncated mean of N(0, 1)** `∫_a^∞ z ϕ(z) dz = ϕ(a)`, proved via FTC `integral_Ioi_of_hasDerivAt_of_tendsto` with antiderivative `-ϕ` (and `(-ϕ)' = z · ϕ`). also includes the volume-integrability of `z · ϕ(z)` via withDensity transfer from `Integrable id (gaussianReal 0 1)`.
- [x] **implied volatility uniqueness via vega-positivity** — `ImpliedVolatility.lean`. uses `bsV_vega_pos` + `strictMonoOn_of_deriv_pos` + `StrictMonoOn.injOn`.
- [x] **black formula for futures options** — `BlackFutures.lean`. specialization of `bs_call_formula` with `r = 0` (zero drift for futures) plus independent discount.

milestone DONE: rigorous theory of vanilla derivatives. covers the standard closed-form option pricing models taught in a quant program.

## phase 3: discrete-continuous bridge (PARTIAL 2026-05-18, deeper progress same day)

- [x] **discrete-time binomial tree pricing framework** — `BinomialModel.lean`. includes:
  - risk-neutral up-probability `crrUpProb u d r = (e^r − d)/(u − d)` + no-arbitrage condition `BinomialNoArb` + `(0, 1)`-range proof.
  - single-period option price `binomialOptionPriceOnePeriod`.
  - **replicating-portfolio theorems** (cost, up-state payoff, down-state payoff) — three full proofs.
  - multi-period `binomialPrice` via well-founded recursion on remaining steps; one-step consistency lemma; linearity and scalar-homogeneity in the payoff; constant-payoff price closed form `e^{-rn} · c`.
- [x] **CRR parameterization + classical-analytic limit core** — `BinomialCRRConvergence.lean`.
  - CRR parameterization: `crrUp = e^{σ√Δt}`, `crrDown = e^{−σ√Δt}`, `crrPerStepRate = rΔt`, `crrProb` definitions.
  - one-step risk-neutral martingale identity (exact algebraic): `p_n · u_n + (1 − p_n) · d_n = e^{rΔt}`.
  - exponential difference-quotient limits: `(e^{cx}−1)/x → c`, `(e^{c·h²}−1)/h² → c`, `(e^{c·h²}−1)/h → 0`, `(e^{σh} − e^{−σh})/h → 2σ`. all proved via `HasDerivAt` + `hasDerivAt_iff_tendsto_slope`.
  - **`crrProb_tendsto_half`**: `p_n → 1/2` as `n → ∞`. the substantive analytic step — `p_n` becomes asymptotically symmetric Bernoulli. ~80 lines, uses quotient-of-limits + composition with `h_n = √(T/n)`.
  - **`crr_variance_limit`**: `4 σ² T · p_n (1 − p_n) → σ² T`. direct corollary.
- [x] **full pricing-convergence theorem**: `binomialPrice → bs_call_price` as `n → ∞` — **DONE** via route (b): characteristic functions + Lévy's continuity theorem on the log-returns (`binomialPrice_call_tendsto_bs`, `Binomial/CRRCharFun.lean`). No triangular-array CLT needed — the bounded *put* payoff converges weakly directly and put-call parity lifts it to the call. The literal closed form `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)` is `binomialPrice_call_tendsto_bs_closed` (`Binomial/CRRClosedForm.lean`).

milestone (achieved): the CRR↔BS correspondence is complete — the variance limit, `p_n → 1/2`, the drift limit `n · (2 p_n − 1) · σ√Δt → (r − σ²/2) T` (`crr_drift_limit_n`, `DriftLimit.lean`), and full distributional + price-level convergence to the BS closed form (`binomialPrice_call_tendsto_bs` / `…_closed`).

## phase 4: upstream foundations

real upstream contributions that would land in mathlib or degenne. each is a separate PR. all four items are ready to submit; awaiting an upstream-PR session.

- [ ] **`Real.erf` for mathlib**. mathlib has no error function. drafting it would unlock cleaner standard-normal-CDF APIs across this project and the broader probability ecosystem. ~300 lines plus the `Real.erfc`, `Real.erfinv` companions and basic identities. would also let us replace our local `Phi` definition with `(1 + erf(x/√2))/2`. **status**: not yet drafted; multi-day work.
- [x] **`gaussianReal_Iic_hasDerivAt` for mathlib**: proved as `hasDerivAt_Phi` in `MathFin/GaussianCDFDeriv.lean` (~80 lines via FTC). ready to upstream as a separate PR (`Φ' = ϕ` is the missing piece).
- [x] **mathlib PR (drafted in `staging/mathlib-pr/`)**: the 4 gaussian tail / completing-the-square lemmas. ready to submit.
- [x] **degenne PR (drafted in `staging/degenne-pr/`)**: the two BM martingales `IsFilteredPreBrownian.squareSubTime_isMartingale` and `IsFilteredPreBrownian.waldExponential_isMartingale`. ready to submit.

## explicitly out of scope (itô-gated, do not attempt without upstream)

these wait on mathlib developing the itô integral or on degenne's brownian-motion library:

- girsanov theorem
- novikov's condition
- martingale representation theorem
- itô's lemma (general SDE chain rule)
- time-dependent itô / 2D itô
- SDE existence/uniqueness
- local martingales / semimartingales
- quadratic variation as a process (we have it as a one-shot at fixed `t`)
- stochastic vol models (heston, SABR)
- jump-diffusion models (merton, kou)
- local volatility (dupire)
- barrier options requiring first-passage time distributions for BM
- quanto / multi-currency options requiring measure change

if mathlib lands an itô integral or degenne extends the brownian-motion library with one, revisit this list.

## stretch goals (technically possible, ergonomically painful)

- **margrabe formula** for exchange options. the rigorous derivation requires a change of numéraire (girsanov). but a "given the right pricing measure, derive the formula" version is achievable using existing gaussian machinery. would need careful scope statement.
- **constant-elasticity-of-variance (CEV) model closed forms**. some special cases have closed forms involving non-central chi-squared distributions. mathlib doesn't have non-central chi-squared yet, so this is gated.

## sequencing recommendation

phases 1 + 2 + phase 3 (basic framework) all landed in a single session on 2026-05-18. remaining work:

1. **CRR convergence to BS** (phase 3 continuation) — **DONE**: `binomialPrice_call_tendsto_bs` and the closed-form `…_closed` (characteristic functions + Lévy + put-call parity; no triangular-array CLT needed).
2. **upstream PRs** (phase 4). the 3 already-drafted items are ready to submit. the `Real.erf` PR would be a fresh multi-day drafting effort.

## what done looks like (achieved)

end of 2026-05-18 session:
- **79 total theorems** (was 65 — 14 new in `benchmarks/mathematical_finance.json`)
- **63 delivery-ready** (was 49)
  - **39 `full`** (was 25 — +14 from `mathematical_finance.json`)
  - **24 `library_wrapper`** (unchanged)
- **16 `reduced_core`** (unchanged; itô-gated)
- **0 `placeholders`** (unchanged)

the project now contains the most thoroughly formalized treatment of static vanilla derivatives pricing in lean 4 known to the author. it's still niche; the audience is still small. but it's a coherent, complete artifact for the "static" world of black-scholes — call, put, parity, both digitals, forward, vega, rho (delta + gamma + theta were already there), bachelier, implied-vol uniqueness, black-76, and the single-period binomial replication theorem.

## the leaps (2026-05-23) — beyond the static world

three "big leaps" pushed past the static ceiling. full narrative in
[`leaps.md`](leaps.md); per-theorem audit in [`coverage.md`](coverage.md).

- **leap 1 — static Girsanov.** the risk-neutral measure is now *derived* from
  the physical measure via an Esscher density (`GaussianGirsanov.lean`,
  `BSCallHyp.exists_of_physical`). `BSCallHyp` — assumed by 14 pricing files —
  is a theorem. axioms-clean.
- **leap 2 — genesis cascade.** `discounted_terminal_eq_S0_of_physical` proves
  the constructed `Q` is a genuine EMM; `bs_call_formula_of_physical` runs the
  full physical→price chain. additive bridges, `GaussianGirsanov` load-bearing.
- **leap 3 — multivariate (Margrabe).** the exchange option, first multivariate
  result: effective vol, `GarmanNormalForm` slot-in, parity, and the
  price-level reduction (`margrabe_price_via_call`: exchange = `bs_call_formula`
  on the ratio). `ExchangeOption.lean`.

all build-enforced axioms-clean via `MathFin/AxiomAudit.lean`.

### leap 4 — the adapted Itô isometry (done, discrete) + the continuous frontier

the increment-independence this was long said to wait on is **not** WIP: it is
`IsPreBrownian.hasIndepIncrements` / `IsPreBrownian.indepFun_shift`, fully
proven in Degenne's package. Building directly on it:

- **leap 4 (discrete) — done.** `Foundations/ItoIsometryAdapted.lean`: the Itô
  isometry for *adapted random* simple integrands,
  `E[(Σ φₖ·ΔBₖ)²] = Σ E[φₖ²]·(t_{k+1}−t_k)` (`ito_isometry_discrete`). the
  cross-terms vanish by the weak Markov property (`ΔBₖ ⊥ 𝓕_{tₖ}`), **not** by
  deterministic covariance — that distinction *is* what separates the Itô
  integral from the Wiener integral (`WienerIntegralL2.lean`, deterministic
  integrands). capstone: the fully-discharged `∫₀ᵀ B dB` Riemann-sum isometry
  `ito_isometry_brownian_self`. build-enforced axioms-clean.
- **continuous integral — done on `[0,T]`.** the L²(adapted) Cauchy completion
  over adapted processes (density of adapted simple integrands in the adapted
  L²) is **built**: `itoIntegralCLM_T` (`ItoIntegralCLM.lean`), with
  `∫₀ᵀ B dB = ½(B_T²−B₀²−T)` as its first consumer. what remains is the
  downstream pathwise Itô / Lévy / SDE layer (the infinite-horizon
  `L2Predictable` variant is now done — `itoIntegralL2`,
  `ito-integral-clm-deferred.md`).
- **Margrabe `BSCallHyp`-grounding — done.** `MargrabeGrounding.lean`: the
  ratio's risk-neutral lognormality is *derived* from a joint two-GBM gaussian
  model (`normalizedSpread_hasLaw_std` + `margrabe_bsCallHyp_of_gaussian`),
  reducing to leap-1 Girsanov on the single effective driver. closes leap 3
  end-to-end; makes `Foundations/BivariateGaussian` load-bearing.

these are honest dedicated builds, not bolt-ons. a hypothesis-form Itô isometry
was drafted and **reverted** earlier precisely because its orthogonality
hypothesis had no available discharge; leap 4 (discrete) is now the genuine
discharge of exactly that orthogonality, via the weak Markov property — the
no-slop line, held.

## the continuous L²(adapted) Itô integral on `[0,T]` — DONE

**Built (2026-05-30):** `itoIntegralCLM_T` (`Foundations/ItoIntegralCLM.lean`),
the continuous linear isometry on `[0,T]`, axioms-clean and AxiomAudit-pinned,
with `∫₀ᵀ B dB = ½(B_T²−B₀²−T)` (`ItoIntegralBrownian.lean`) as its first
consumer. The construction sketch below is kept as a reference record of how it
was built; the still-open downstream layer is the pathwise Itô / Lévy / SDE
results (the infinite-horizon `L2Predictable` variant is now done —
`itoIntegralL2`, `ito-integral-clm-deferred.md`).

**Goal.** A continuous linear isometry
`itoIntegralL2 : {adapted L²(Ω×[0,T])} →L[ℝ] Lp ℝ 2 μ` extending the discrete
`ito_isometry_discrete`, with `‖itoIntegralL2 φ‖² = ∫₀ᵀ E[φ_t²] dt`.

**Construction (mirror the Wiener case, but the integrand space is adapted).**
1. Space of *adapted simple processes*: `φ = Σₖ Hₖ · 𝟙_{(tₖ,tₖ₊₁]}` with each
   `Hₖ` `𝓕_{tₖ}`-measurable + `L²` (reuse `AdaptedAt` / `pastProcess`).
2. The isometry on simple processes **is** `ito_isometry_discrete` (already
   built) — that is the algebraic core, done.
3. **The genuinely new work**: density of adapted simple processes in the
   adapted `L²` space `L²_𝓕(Ω×[0,T])`. The Wiener proof's orthogonal-complement
   route (`stepAssembly_denseRange`) does **not** transfer directly — the
   integrand is jointly measurable in `(ω,t)` and the simple processes must be
   *adapted*, so the dense-subspace argument runs in the closed subspace of
   progressively-measurable `L²` functions, not all of `L²`. This is the crux
   and the bulk of the effort.
4. `LinearMap.extendOfNorm` then yields the CLM, exactly as `wienerIntegralLp`.

**Prerequisite to check first**: whether Degenne's `StochasticIntegral/`
tree (predictable processes, `BrownianMotion/StochasticIntegral/`) already
supplies the adapted-`L²` density or the progressive-measurability scaffolding
— if so, this reduces to a wrapper + the discrete isometry and is much smaller.
Reconnoitre that tree before building from scratch.

**Unblocks**: the ~12 itô-gated `reduced_core`s (Itô's lemma path-wise form,
time-dependent Itô, SDE existence/uniqueness, the general Girsanov entries) —
each becomes a real consumer of `itoIntegralL2`, finally making the Itô layer
load-bearing into the pricing modules rather than a standalone cornerstone.

**Out of scope / still genuinely gated** (do not conflate with the above):
continuous-time Poisson processes (Cox/Credit), BM reflection principle,
nowhere-differentiability, and the law of iterated logarithm — none are
unblocked by the Itô integral; they need their own upstream Mathlib
infrastructure. (CRR→BS distributional convergence is **done** — via
characteristic functions + put-call parity, sidestepping the triangular-array
CLT.)

## phase: the 100%-full push — Poisson cluster + Itô QV (2026-06-05)

The remaining gap to 100% full is 22 reduced cores in four clusters
(Poisson 4, Markov 6, Itô/Girsanov tower 9, BM path machinery 3). This
phase took the Poisson cluster and the bounded half of the Itô pair.

**Poisson cluster (4 entries) — landed:**

- `pp-thm-3.3.9` (superposition) → **full**. New
  `Foundations/PoissonSuperposition.lean`: the Poisson convolution identity
  `poissonMeasure a ∗ poissonMeasure b = poissonMeasure (a+b)` (absent from
  Mathlib; singleton-ext + binomial collapse of the Cauchy product) + the
  independent-sum bridge mirroring `gaussianReal_conv_gaussianReal`'s
  pattern.
- `pp-thm-3.3.10` (thinning) → **full**. New
  `Foundations/PoissonThinning.lean`: the binomial-marking factorisation
  `markedPoissonMeasure r p = Poisson(pr) ×ₘ Poisson((1−p)r)` — marginals
  AND independence of the thinned streams derived from the marking
  mechanism (`C(j+k,j)/(j+k)! = 1/(j!k!)` + `e^{−r} = e^{−pr}e^{−qr}`).
- `pp-thm-3.3.5` (marginal law) → **full**, via the route coverage.md
  recorded as re-earnable. New `Foundations/PoissonCounting.lean`: marginal
  derived from the arrival construction — Erlang law of arrival times
  (`ErlangSum`, generalized from `Fin n` to arbitrary index) composed with
  the new **Gamma-CDF difference identity**
  `∫₀ᵗ γ_k − ∫₀ᵗ γ_{k+1} = e^{−rt}(rt)ᵏ/k!` (FTC telescope on
  `Φ_k(u) = (ru)ᵏe^{−ru}/k!`).
- `pp-prop-3.3.6` (interarrivals iid Exp) → stays **reduced_core,
  honestly**, but with a real derived core. New
  `Foundations/PoissonInterarrival.lean`: the FIRST interarrival is PROVED
  exponential from the counting axioms (survival law + CDF identification
  against `cdf_expMeasure_eq`), and the memoryless survival factorisation
  is PROVED from independent increments. The full-sequence iid claim needs
  the strong Markov property — upstream-gated.

**Itô bounded pair:**

- `sc-thm-7.4.5` (QV of an Itô process) → **full** in the constant-σ /
  Lipschitz-drift regime. New `Foundations/ItoProcessQV.lean`: equipartition
  QV sums of `X = X₀ + A + σB` converge in L² to `σ²T` with explicit `1/n`
  rates — the drift-immunity content derived (pathwise squeeze + Cauchy–
  Schwarz cross-term + `QuadraticVariationL2`). General σ(s,ω) = Summit B.
- `sc-thm-7.1.2` (time-dependent Itô) → **full** (2026-06-07, Summit A′
  DONE). The assessed mini-campaign executed as scoped: the three Summit-A
  limit arguments redone with `(t,x)`-dependence. `tendsto_weighted_qv_process`
  (WeightedQuadraticVariation generalized to bounded *adapted weight
  processes* — the fluctuation engine never cared the weight was `g(B_s)`;
  `tendsto_riemann_L2_process` exported standalone for the drift term),
  `tendsto_ito_remainder_td` (2D Taylor remainder, `O(1/n)` under
  `E[ΔB⁶] = 15Δt³`), `itoIntegralCLM_T_of_bdd_cont_td` (TD Riemann↔CLM
  bridge), assembled in `Foundations/ItoFormulaTD.lean`:
  `ito_formula_td_L2_bddDeriv` = the classical
  `f(T,B_T) − f(0,B₀) = ∫f_x dB + ∫(f_t + ½f_xx) ds` a.e., with `f_t`'s
  joint continuity *derived* from its bounded partials. Unbounded
  coefficients stay the named gap (as in 7.1.1).

**Markov cluster note:** `Kernel.traj` (Ionescu–Tulcea) is now IN the
Mathlib pin — re-cost the path-space entries (`mc-thm-1.1.2`,
`mc-thm-1.4.32`) before assuming they are gated.

**Follow-up (small): adopt `formalization.yaml`** — the mathlib-initiative
formalization-provenance manifest (scope / sources / sorry count / axiom
boundary / paper↔Lean alignment / production record). The repo already
maintains every ingredient (formalization_status, coverage.md, AxiomAudit,
verification ledger); a stdlib generator emitting one repo-level manifest
from the benchmark JSONs would make it legible to the emerging standard.

## phase: the finance layer over the Poisson/QV track (2026-06-06)

The 2026-06-05 round derived the Poisson/QV foundations; this phase answers
"what, in finance, did that free" by making them load-bearing in the
pricing layer. Six new `full` entries (corpus 261 → 267, **231 full + 18
wrappers = 249/267 delivery-ready**), four new modules, recon-first (two
Explore agents + daemon name-probes before any Lean was written; three of
four modules green on first daemon check, the fourth needed two mechanical
fixes — a `Phi_nonneg` name collision and a needless `Summable.congr`).

- **Variance-swap drift immunity** (`mf-variance-swap-drift-immunity`,
  `Foundations/VarianceSwapDriftImmunity.lean`): realized variance of GBM
  log-returns → `σ²T` in **L²** for ANY drift — the fair strike is a QV
  functional; physical-vs-risk-neutral drift is irrelevant to what the
  swap settles on. First pricing consumer of `ItoProcessQV`; strengthens
  phase 34 (expectation-level, risk-neutral-drift-only) on both axes.
- **First-to-default additivity** (`mf-first-to-default-spread`,
  `FixedIncome/FirstToDefault.lean`): FtD basket spread = Σ single-name
  hazards under independence. Pure de-orphaning bridge:
  `ExpMin.minimum_survival` (previously consumed only by `dist-exp-min`)
  rewritten in `Credit.lean` vocabulary; spread reading via the existing
  `creditSpread_eq_hazard`. No new measure theory.
- **Poisson pgf** (`dist-poisson-pgf`, `Foundations/PoissonPgf.lean`):
  `E[x^N] = e^{r(x−1)}` for every real `x`, absent from Mathlib —
  exponential series at `r·x` rescaled by `e^{−r}`, the same
  `NormedSpace.expSeries_div_hasSum_exp` route Mathlib uses for the pmf
  normalisation.
- **Merton (1976) jump-diffusion** (`mf-merton-call-series` /
  `mf-merton-spot-recombination` / `mf-merton-put-call-parity`,
  `BlackScholes/MertonJumpDiffusion.lean`): the price is *defined* as
  `∫ n, C_BS(spot_n, vol_n) ∂(poissonMeasure Λ)` — an honest expectation
  over the jump count (the pin's `integral_poissonMeasure` makes the
  textbook series a theorem, not a definition). Compensation identity
  `E[spot_N] = S₀` via the pgf at `1+k`; parity through the mixture via
  sandwich-bound integrability (`0 ≤ C_n ≤ spot_n`, `0 ≤ P_n ≤ Ke^{−rT}`)
  + term-wise `Φ(x)+Φ(−x)=1` algebra. Every term separately grounded as a
  discounted conditional expected payoff (`bs_call_formula` instantiated
  on `(ℝ, gaussianReal 0 1)` with `HasLaw.id`). Honest scope: terminal
  mixture law only, exactly parallel to `BSCallHyp`; the compound-Poisson
  jump *SDE* stays upstream-gated.

**Deliberately skipped:** Cramér–Lundberg ruin bound (needs
compound-Poisson process machinery + optional stopping we don't have —
only the algebraic MGF identity exists in `Actuarial/Mortality.lean`);
jump-diffusion QV with compound-Poisson jumps (same gating).

**Next candidates from here:** Merton Greeks / monotonicity-in-Λ
(formula-level, cheap); re-pointing the λ′ = Λ(1+k) classic display as a
series-rearrangement lemma; the Markov cluster re-cost (`Kernel.traj`);
Summit B decision.

## phase: merton dominance + classic display + markov path law (2026-06-06, second round)

the "next candidates" above, executed, plus the markov re-cost verdict.

- **merton dominance** (`mf-merton-dominance`,
  `BlackScholes/MertonDominance.lean` + `BlackScholes/SpotConvexity.lean`):
  `C_BS(S₀,σ) ≤ C_Merton(S₀,σ,k,δ,Λ)` for every `Λ`, `δ`, `k > −1` — the
  "Merton Greeks" item reframed to its substantive content. a literal
  delta-as-series theorem needs differentiation under the tsum, whose
  global derivative bounds the junk region `s ≤ 0` cannot honestly supply
  (`hasDerivAt_tsum` requires them) — skipped as ceremony. the dominance
  bound prices the two jump channels separately: per-term vol-monotonicity
  (vega, `bsV_strictMonoOn_sigma`) reduces to `δ = 0`; there the **new
  spot-direction convexity** `bsV_spot_convexOn` (gamma ≥ 0
  second-derivative test — the S-direction dual of `bsV_strike_convexOn`,
  so convexity is now visible in both coordinates of the price surface)
  gives the supporting tangent at `S₀`, whose linear term integrates to
  zero by the compensation identity `integral_mertonSpot`.
- **classic display** (`mf-merton-classic-display`,
  `BlackScholes/MertonClassicDisplay.lean`): the textbook `Λ′ = Λ(1+k)`
  series with shifted rates `r_n = r − kΛ/T + n·log(1+k)/T`, driven by one
  structural identity — the rate-shift invariance
  `bsV K r σ (S·e^{cτ}) τ = e^{cτ}·bsV K (r+c) σ S τ`
  (`bsV_spot_exp_rate_shift`) — plus Poisson-weight absorption.
- **markov re-cost verdict** (`Kernel.traj` now in the pin): only
  `mc-thm-1.1.2` was genuinely unlocked, and it is now **full**
  (`Foundations/MarkovPathMeasure.lean`): the chain's law is constructed
  via `Kernel.trajMeasure` from kernels that read only the last history
  coordinate, and the path factorization is derived by induction through
  the comp-product recursion of the marginals. the other five Markov
  reduced cores stay honestly gated — recurrence needs renewal theory /
  fundamental-matrix algebra, convergence to stationarity needs
  Perron–Frobenius, the ergodic theorem needs both plus aperiodicity,
  stationary uniqueness needs recurrence + communicating classes, and the
  strong Markov property needs stopping-time kernels (a design-level
  extension, not a gap-fill). a markov campaign is a 4–6 week
  renewal+spectral build, upstream-quality material — record, don't drift
  into it. *re-confirmed 2026-06-06 (third round), with one new datum:
  the pin now carries `Matrix.IsIrreducible` / `Matrix.IsPrimitive`
  **definitions** (`LinearAlgebra/Matrix/Irreducible/Defs.lean`,
  quiver-path formulation + `isIrreducible_iff_exists_pow_pos`) but no
  Perron–Frobenius eigenvalue theorem, and `Dynamics/BirkhoffSum` is the
  von-Neumann normed-space flavor, not the pointwise ergodic theorem. the
  re-cost trigger for 1.4.25/1.4.40 is therefore concrete: when Mathlib
  lands the PF theorem over these definitions, both become tractable
  matrix-level builds.*

**Next candidates from here:** Summit B decision (integral-as-process /
general `σ(s,ω)`); hammer re-pilot at the rc2→stable toolchain bump; the
Markov renewal/spectral layers if that cluster is ever prioritized.
(`sc-thm-7.1.2` time-dependent Itô: DONE 2026-06-07 — Summit A′ landed, see
the Itô bounded pair above.)

## phase: Feynman–Kac → Black–Scholes PDE keystone (2026-06-08)

the second, **Itô-independent** derivation that the discounted risk-neutral
price solves the Black–Scholes PDE — closing the "two-tower" gap (the deep
Itô tower had no pricing consumer; the heat-flow `feynmanU` was an orphan).
this is the direction recorded as "deferred — not needed ever" in
`docs/feynman-kac-growth-deferred.md`, now **revived and completed** (that
note carries a superseded banner).

- **the heat-flow engine** (`Foundations/FeynmanKacHeatEquation.lean`): the
  heat kernel `K(t,y) = (√(2πt))⁻¹ e^{−y²/2t}` is **jointly Fréchet-
  differentiable** (`hasFDerivAt_heatKernel`) — the one genuinely-2D
  ingredient, so a single curve chain rule serves all three partials.
  `hasDerivAt_feynmanU_{t,x,xx}` differentiate `feynmanU g t x = ∫ z, g z ·
  K(t, z−x) dz` under the integral (dominated convergence, routed through the
  parametric skeleton `hasDerivAt_integral_mul_kernelFamily`; `g` need only be
  continuous + growth-controlled, so the call's kink is sidestepped). the
  kernel identity `feynmanU_heat_equation` is `∂_t K = ½ ∂_xx K`.
- **the keystone** (`BlackScholes/PDEFromFeynmanKac.lean`,
  `bsV_satisfies_bs_pde_via_feynmanKac`): the BS Greeks
  `hasDerivAt_bsV_{tau,S,SS}_fk` follow from the heat flow by the log-
  transform `S = eˣ` + discount `e^{−r(T−t)}`; the BS PDE assembles by exact
  drift cancellation (`U_x` coeff `−(r−σ²/2)−½σ²+r = 0`, `U_xx` coeff
  `−½σ²+½σ²=0`). the ∂_τ wall (the uniform-domination `nlinarith`/200k-
  heartbeat blow-up that defeated several earlier attempts) fell by isolating
  the polynomial bracket bounds as standalone lemmas with the moving
  denominator replaced by the constant `v₀`, and dominating by a **sum of two
  Gaussian-moment envelopes** (one per kernel-derivative term) rather than a
  single mega-constant.
- **wired**: corpus entry `sc-bs-pde-feynman-kac` (`full`); the
  `sc-thm-9.2.1` scope note de-staled (its "~300–500 lines upstream" claim
  was false — the infra is built and consumed). bridge row "FK" in
  `bridges.md`. counts: corpus 269→**270**, full 235→**236**, delivery-ready
  **254**/270.

**scope honesty:** this is the **constant-coefficient** (closed-form) case.
the genuinely-open FK work is **variable-coefficient** (`σ(S,t)` local vol,
Heston) on the general-Itô/SDE layer — a different, much harder theorem — plus
the fully-general continuous-`g` PDE + uniqueness.

**Next candidates from here:** ✅ the round-5 deferred cleanup was executed
same-day (orphan wiring + blueprint spine + the `sc-thm-8.2.5` rewrite,
`3a25518`/`bde8f24`; values round 6 then found that rewrite's uniqueness
clause uninhabitable and repaired it with an opaque integral-*operator*
encoding + an in-snippet inhabitant guard). Remaining: P1 the explicit
CRR→BS error-constant paper.

## phase: Summit B / B1b — the general-integrand Itô integral (2026-06-12)

B1a built the elementary (simple-integrand) Itô integral as a process; B1b
extends it to a **general** predictable integrand `φ ∈ L2Predictable[0,T]` (=
Degenne's predictable-L² on `[0,T]`), delivering the general Itô integral
`(φ●B)_t = ∫₀ᵗ φ dB` as a **continuous L² martingale on `[0,T]`**
(`Foundations/ItoIntegralProcessGeneral.lean`).

- **Architecture (direct extension).** `itoProcessCLM := itoProcessLM.extendOfNorm
  simpleAssembly_T` — extend B1a's t-process linear map along the *same* dense
  embedding that builds the terminal CLM `itoIntegralCLM_T`. The bridge to B1a is
  then **definitional** (`extendOfNorm_eq`); the one new analytic input is the
  contraction bound `‖(V●B)_t‖ ≤ ‖V‖`, from B1a's martingale + the condExp L²
  contraction.
- **The key identity** `itoProcessCLM_eq_condExpL2`: `(φ●B)_t = condExpL2 𝓕_t
  (∫₀ᵀ φ dB)` (the integral is the conditional-expectation projection of its
  terminal value). From it: the **martingale property** (condExp tower
  `condExp_condExp_of_le`), **a.e.-adaptedness** (`condExpL2` lands in `lpMeas`),
  the **contraction** `‖(φ●B)_t‖ ≤ ‖φ‖`, and the **terminal isometry**
  `‖(φ●B)_T‖ = ‖φ‖` (`itoProcessCLM T T = itoIntegralCLM_T T`). **L²-continuity**
  is uniform approximation: the t-free contraction makes the simple-process
  processes converge uniformly in `t`, so the limit is continuous
  (`TendstoUniformly.continuous`).
- **Coherence (the bump's payoff).** Pure consumption of upstream (Degenne's
  `L2Predictable`/`SimpleProcess`, Mathlib's `condExpL2`/`extendOfNorm`/condExp
  tower) + the repo's B1a + `itoIntegralCLM_T`. Nothing reproved.
- **Wired:** 3 new `full` entries (`sc-ito-general-martingale` /
  `-terminal-isometry` / `-l2-continuity`); corpus 277 → **280**, 242 → **245
  full**; lake build 8723 jobs green, axioms-clean; values panel PASS (one
  docstring-honesty blocker fixed).

**Honest scope:** finite-horizon `[0,T]`, L² sense.

**Isometry round (2026-06-12) — DONE.** The explicit **time-indexed isometry**
`E[(φ●B)_t²] = ∫₀ᵗ E[φ²] ds` (B1b's deferred refinement) is now **proved**
(`itoProcessCLM_norm_sq`, `Foundations/ItoIntegralProcessIsometry.lean`, entry
`sc-ito-general-time-isometry`). The band-over-trimmed-measure computation
(`restrict`∘`trim`∘`prod` rectTerm integral mirroring `simpleProcessL2_norm_sq`)
gives the band-restricted **simple-process** isometry; the per-endpoint-`∧t`-truncated
double sum (B1a's `itoSimpleProcess_isometry_time`) equals the joint-overlap-`∩(0,t]`
double sum by a pure-ℝ interval-length identity (`band_overlap_real`). It transfers to
all predictable `φ` by `DenseRange.equalizer`: both `‖(φ●B)_t‖²` and
`∫_{(0,t]}φ² = ‖truncCLM φ‖²` (the band-truncation CLM, hand-built — Mathlib has only
the *constant*-indicator `indicatorConstLp`, not variable-`φ` multiplication) are
continuous and agree on the dense simple processes. The generic `lp_two_norm_sq` was
de-privatised in `ItoIntegralL2` and reused. corpus 280 → **281**, 245 → **246 full**;
lake build 8724 jobs green, axioms-clean. **B2 (infinite-horizon `[0,∞)` via
σ-finite predictable exhaustion) DONE 2026-06-13** — `itoIntegralL2` /
`itoIntegralL2_norm` in `Foundations/ItoIntegralL2Dense.lean`, corpus entry
`sc-ito-infinite-horizon-isometry`, by reducing each finite frame to the
finite-horizon `setIntegral_eq_zero_of_orthogonal_pred` via
`trimMeasure_T_eq_restrict` and patching over the `{0}×univ`-null complement;
build 8725 jobs green, axioms-clean, corpus 281 → **282**, 246 → **247 full**.

**B3 (localization) DONE 2026-06-13** — the elementary Itô integral as a
**continuous local martingale** (`itoSimpleProcess_isLocalMartingale` +
`itoSimpleProcess_pathContinuous`, `Foundations/ItoIntegralProcessLocalMartingale.lean`,
entry `sc-ito-simple-process-local-martingale`). The first sample-path
regularity result in the tower: given continuous Brownian paths, `t ↦ (V●B)_t ω`
is continuous (finite sum of continuous clamped increments via
`itoSimpleProcess_apply`), hence càdlàg, so B1a's true `L²` martingale lands in
Degenne's sorry-free `IsLocalMartingale` class (`Martingale.IsLocalMartingale`).
Pure consumption; the genuinely new content is the pathwise continuity. Honest
scope: simple integrands, continuity assumed (the standard pathwise setting;
`IsPreBrownian` fixes only finite-dim laws, a continuous version exists by
Kolmogorov–Chentsov). build 8726 jobs green, axioms-clean, corpus 282 →
**283**, 247 → **248 full**.

**D1 (covariation / bilinear Itô isometry) DONE 2026-06-23** — the polarized
companion of the Itô isometry. `Foundations/ItoIntegralCovariation.lean`, entry
`sc-ito-covariation-bilinear-isometry`. The `[0,T]` Itô CLM is bundled as a
`LinearIsometry` (`itoIsometry_T`, from the norm isometry `itoIntegralCLM_T_norm`);
a real linear norm-isometry preserves the inner product (polarization), so
`LinearIsometry.inner_map_map` gives `⟪∫φ dB, ∫ψ dB⟫ = ⟪φ, ψ⟫`
(`inner_itoIntegralCLM_T`), and `L2.inner_def` unfolds the μ-side to the
expectation `𝔼[(∫φ dB)(∫ψ dB)] = ⟪φ, ψ⟫` (`covariation_itoIntegralCLM_T`); the
diagonal `φ = ψ` recovers the isometry (`variance_itoIntegralCLM_T`). Pure
polarization of B1's norm isometry — the covariance backbone for
covariance/correlation-swap pricing. build 8727 jobs green, axioms-clean, corpus
→ **285**, **250 full** + 18 = 268/285 delivery-ready, 17 reduced.

**Next — D2 (general-integrand local martingale), scoped multi-session.** Recon
this round showed the natural "extend B3 to general integrands" step is GATED:
B1b's general integral exists only as `Lp`/L²-objects (martingale = conditional-
expectation equalities, continuity = L²-continuity into `Lp 2 μ`), with no
pathwise-continuous representative — but Degenne's `IsLocalMartingale` needs
pathwise càdlàg paths (exactly why B3 worked only for the *simple* process and its
explicit continuous clamped-sum). So D2 first needs a **continuous modification**
of the general integral (Doob L²-maximal inequality → a.s.-uniform limit of the
simple approximants → pathwise-continuous process), after which the local-
martingale property is B3's one-liner. That continuous modification is the load-
bearing prerequisite for localizing the Itô formula
(`ItoFormulaTD.ito_formula_td_L2_bddDeriv`, presently bounded-derivative only) to
unbounded/GBM coefficients — the bridge from the analytic Itô tower to the
drift-algebra pricing tower (`ItoLemma2D`, `PDEFromIto`, `VasicekSDE`).

## phase: FTAP tower (2026-06-24 through 2026-06-26, corpus 285→289)

Three FTAP rungs, each built to `full` standard, ascending from finite to infinite
state space and from scalar to vector excess returns.

- **Rung 1 (finite-Ω multi-period, Harrison–Pliska), corpus 285→287.** `ftap_discrete`
  (`mf-ftap-discrete-complete`, `Foundations/FTAPDiscrete.lean`): for a full-support
  finite probability space and a scalar discounted excess return, no-arbitrage ⟺ ∃ EMM,
  multi-period, finite filtration. Forward: EMM ⟹ NA by martingale-transform telescoping.
  Backward: global geometric Hahn–Banach separation of the attainable-gains subspace from
  the standard simplex, via a reusable kernel `Foundations/ConvexSeparation.lean` (Mazur +
  `Finset` relative-interior certificate). The multi-state single-period biconditional
  `hasEMM_multi_iff_not_hasArbitrage` (`mf-ftap-single-period-complete`) was wired at the
  same time. build 8808 jobs green, axioms-clean, corpus → **287**, **252 full** + 18 =
  270/287 delivery-ready, 17 reduced.

- **Rung 2 (general-Ω one-period scalar, Föllmer–Schied 1.55), corpus 287→288.**
  `ftap_one_period` (`mf-ftap-one-period-general`, `Foundations/FTAPOnePeriod.lean`): for
  an arbitrary probability space and a single scalar `L⁰` excess return `Y`, no-arbitrage
  ⟺ ∃ equivalent martingale measure `Q ~ P` with `E_Q[Y] = 0`. Forward: EMM ⟹ NA
  immediately. Backward: bounded-density reduction (clamp `Y` to `L¹`), scalar NA
  dichotomy (sign analysis on `E_P[Y·1_A]` for each event `A`), two-region balancing
  `withDensity` construction of the EMM density. No Hahn–Banach, no Kreps–Yan — the
  general-Ω step beyond Harrison–Pliska is purely measure-theoretic.
  `isEquivProbMeasure_withDensity` extracted into `Foundations/EquivMeasure.lean` to
  avoid duplication with the d-asset rung. values panel 8/8 PASS. corpus → **288**,
  **253 full** + 18 = 271/288 delivery-ready.

- **Rung 3 (d-asset one-period, Föllmer–Schied 1.6), corpus 288→289.** `ftap_one_period_vector`
  (`mf-ftap-one-period-vector`, `Foundations/FTAPOnePeriodVector.lean`): for any
  finite-dimensional inner-product space `F` (the `ℝᵈ` market is `F = EuclideanSpace ℝ
  (Fin d)`) and an `F`-valued excess return `Y`, no-arbitrage ⟺ ∃ EMM. The explicit
  **Esscher/minimal-divergence** EMM is the minimiser of the convex softplus potential
  `θ ↦ ∫ log(1 + exp⟪θ,Y⟫)`: coercive on `Nᗮ` (the orthogonal complement of the gains
  kernel `N = {θ : ⟪θ,Y⟫ = 0 a.e.}`), so a minimiser on `Nᗮ` is automatically global
  (redundant directions absorbed); the first-order condition (differentiation under the
  integral) yields the strictly-positive bounded density `σ⟨θ₀,Y⟩`. Drops the
  earlier non-redundancy hypothesis. No Hahn–Banach, no L⁰-closedness, no measurable
  selection. values panel 8/8 PASS. build 8817 jobs green, axioms-clean, corpus → **289**,
  **254 full** + 18 = 272/289 delivery-ready, 17 reduced.

**Open rung:** general-Ω multi-period DMW (Dalang–Morton–Willinger). Requires
L⁰-closedness of the attainable-gains set and measurable selection — neither in the
current Mathlib/BrownianMotion pin. This is the M2 crown (see `docs/roadmap.md`
strategy framing); the d-asset one-period case is now closed in full.

## phase: Itô pathwise regularity arc (2026-06-25 through 2026-06-26, corpus 289→292)

The D2 gate identified in the B1b/D1 phase — continuous modification of the
general-integrand Itô integral — is now fully built, and extended to the whole
half-line.

- **Continuous modification on `[0,T]`** (`sc-ito-general-continuous-modification`,
  `exists_continuous_modification_itoProcess`,
  `Foundations/ItoIntegralProcessContinuousModification.lean`, corpus 289→290).
  The L²-valued process `t ↦ (φ●B)_t` admits an a.s.-continuous representative.
  Route: Degenne's continuous-time Doob maximal inequality (applied to the approximating
  simple-process martingales `(V_n●B)_t`) → Chebyshev on the maximal deviation
  → Borel–Cantelli on a fast geometric subsequence → pathwise uniform convergence to a
  continuous limit `itoContinuousMod`. The running-max keystone
  (`itoContinuousMod_sup_le`) bounds the pathwise norm under the supremum over `[0,T]`.
  This is the first sample-path result for the *general* integrand; the bounded-derivative
  Itô formula localization to unbounded coefficients follows from here.
  values panel PASS. build green, axioms-clean, corpus → **290**, **255 full** + 18 =
  273/290 delivery-ready.

- **Continuous local martingale on `[0,T]`** (`sc-ito-general-local-martingale`,
  `exists_continuous_localMartingale_modification`,
  `Foundations/ItoIntegralProcessLocalMartingaleGeneral.lean`, corpus 290→291).
  The continuous modification is upgraded to Degenne's `IsLocalMartingale` interface,
  adapted to the **null-augmented** Brownian filtration `𝓕ᴮ ⊔ 𝓝`. The
  measure-theoretic core is `condExp_sup_nulls`: conditioning on the null augmentation
  agrees a.e. with conditioning on `𝓕ᴮ` (its σ-algebra crux consuming Mathlib's
  `eventuallyMeasurableSpace`); every `(𝓕 ⊔ 𝓝)`-measurable set is a.e. a `𝓕`-set.
  Non-redundant with Degenne's sorry-backed general càdlàg modification (different
  objects: his is a BM modification, ours is an integral-process modification).
  corpus → **291**, **256 full** + 18 = 274/291 delivery-ready.

- **Continuous local martingale on `[0,∞)`** (`sc-ito-infinite-local-martingale`,
  `exists_continuous_localMartingale_modification_infinite`,
  `Foundations/ItoIntegralProcessLocalMartingaleInfinite.lean`, corpus 291→292).
  The per-horizon `[0,T=n]` continuous local martingales are **glued** into one path
  continuous on all of `ℝ≥0`. The key steps: horizon consistency
  (`itoProcessL2Inf_eq_itoProcessCLM`) resting on the band-restriction CLM
  `restrictToBand` and a hand-built `[0,T]` clamp of Degenne's `SimpleProcess`
  (`simpleProcessL2_T`); `indistinguishable_of_modification_on` agrees the
  per-horizon modifications on overlapping windows; with no horizon clamp the
  martingale property is the global `itoProcessL2Inf_isMartingale` via
  `condExp_sup_nulls`. This is the Itô integral as a continuous local martingale on
  the entire time domain `ℝ≥0`. values panel 8/8 PASS. build green, axioms-clean,
  corpus → **292**, **257 full** + 18 = 275/292 delivery-ready, 17 reduced, 0 placeholders.

## phase: Itô tower → pricing bridge — Vasicek terminal law derived (2026-06-27)

The deepest analytic Itô tower (complete through the `[0,∞)` continuous local
martingale) had **no pricing consumer**; pricing modules touched it only at the
*drift-algebra* level (`ItoLemma`/`ItoLemma2D`). This phase makes the
deterministic-integrand layer load-bearing in a pricing module for the first time.

- **The deterministic-integrand Wiener integral is Gaussian**
  (`sc-wiener-integral-gaussian`, `wienerIntegralLp_map_eq_gaussianReal`,
  `Foundations/WienerIntegralGaussian.lean`). `WienerIntegralL2` built the integral
  as an isometry but pinned only its *norm*; this supplies the *law*:
  `μ.map (wienerIntegralLp B hB T f) = gaussianReal 0 ‖f‖²`. Characteristic-function
  route — simple-process Gaussianity (`IsGaussianProcess.of_isGaussianProcess` +
  `map_eq_gaussianReal`, mean 0 + the isometry as variance) lifted to all `L²` by a
  `|t|`-Lipschitz-charFun `DenseRange.induction_on` + `Measure.ext_of_charFun`.

- **Vasicek terminal law derived** (`mf-vasicek-sde-terminal-gaussian`,
  `vasicekShortRate_hasLaw_gaussian`, `FixedIncome/VasicekSDEGaussian.lean`). The SDE
  solution `r_T = mean + σ ∫₀ᵀ e^{−κ(T−s)} dB_s` has law
  `N(vasicekSDEMean, σ²(1−e^{−2κT})/(2κ))` — the closed form `VasicekSDE.lean` posited
  is now a theorem. Variance via the FTC integral `∫₀ᵀ e^{−2κ(T−s)} ds`; affine
  transport via `gaussianReal_const_mul`/`gaussianReal_const_add`. **First Itô-tower
  consumer in FixedIncome.** corpus 292 → **294**, 257 → **259 full**.

## phase: localized (exponential-growth) Itô formula — the rung-3 unlock to GBM (2026-06-28)

- **Localized time-dependent Itô formula** (`sc-ito-formula-localized`,
  `ito_formula_td_localized`, `Foundations/ItoFormulaLocalized.lean`). Lifts the
  bounded-derivative `ito_formula_td_L2_bddDeriv` (six *global* derivative bounds) to `f` of
  **at-most-exponential growth** `|f_• t x| ≤ C·exp(λ|x|)` — so it reaches the GBM/Black–Scholes
  value function `f(t,x)=S₀ exp((r−σ²/2)t+σx)`, the named out-of-scope gap of 7.1.1/7.1.2.
  Same conclusion shape, a drop-in. The proof is an **L²-cutoff localization that consumes the
  bounded engine**: smooth truncation `SmoothTrunc` = a `ContDiffBump` antiderivative (every
  derivative + bound from Mathlib, no explicit calculus); `cutoff_bddDeriv` applies the bounded
  formula to each `fₙ=f(t,φₙ(x))` via the chain rule; then `n→∞` — boundary (`boundary_tendsto_L2`)
  and drift (`drift_tendsto_L2`) converge in `L²(μ)` by dominated convergence, the dominators
  integrable because Brownian marginals have **every exponential moment** (`BrownianExpMoment`,
  Mathlib's Gaussian MGF transferred along `B_s~N(0,s)`) and the drift dominator is the new
  reusable base stone `pathIntegral_expGrowth_memLp` (exp-growth path integral in `L²`, Fatou
  over Riemann sums + discrete Cauchy–Schwarz, no Tonelli). Hence `aₙ=itoIntegralCLM_T gfxₙ` is
  Cauchy; the Itô **isometry** transfers Cauchy-ness to the integrands `gfxₙ`, completeness gives
  the witness, CLM **continuity** identifies its image with the limit. The deep Itô tower (QV,
  isometry, CLM) carries the pricing weight with zero new analytic machinery beyond the cutoff.
  corpus 294 → **295**, 259 → **260 full**.

- **The Itô tower reaches pricing — GBM decomposed by the Itô integral**
  (`Foundations/ItoFormulaGBM.lean`, entries `sc-ito-formula-gbm`, `sc-discounted-gbm-ito`, both
  `full`). The **first pricing-ward consumer of the analytic Itô tower**, which until now had
  *none*: GBM/BS pricing ran via separate algebraic towers (`ItoLemma`/`PDEFromIto`, Feynman–Kac)
  and `discountedGBM_isMartingale` was proved via the Wald exponential, never the Itô integral.
  `ito_formula_gbm` gives `Ŝ(T) − Ŝ(0) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ m·Ŝ ds` for the GBM value
  `Ŝ(t)=S₀ exp((m−σ²/2)t+σ B_t)`, the stochastic term the *genuine* continuous Itô integral. The
  route is the **classic one — localization in time**: the GBM value is `t`-exponential and fails
  the localized formula's `t`-uniform growth, so the localized formula is applied to the
  time-localized exponent `S₀ exp((m−σ²/2)·φₙ(t)+σx)` (`φₙ=SmoothTrunc.cut n`, `n=⌈T⌉₊`), the
  identity on `[0,T]` yet globally bounded so the exp-growth hypotheses hold uniformly in time;
  on `[0,T]` `φₙ=id`, `φₙ'=1`, so the localization drift `(m−σ²/2)·Ŝ` and the Itô correction
  `½σ²·Ŝ` collapse to `m·Ŝ`. Setting `m=0` (`discountedGBM_eq_itoIntegral`) makes the drift
  vanish — the Itô-integral content of the discounted-GBM martingale (no new analytic machinery
  beyond the `phi'_eq_one_of_lt` plateau-slope lemma). corpus 295 → **297**, 260 → **262 full**.

- **The Itô formula reaches a general (constant-coefficient) Itô process**
  (`Foundations/ItoFormulaItoProcess.lean`, entry `sc-ito-formula-ito-process`, `full`). The
  natural successor to GBM: `ito_formula_itoProcess` decomposes `f(X)` for an *arbitrary* `C³`
  exponential-growth `f` against `X_t = X₀ + b·t + σ B_t`, giving
  `f(X_T) − f(X₀) =ᵐ itoIntegralCLM_T gfx + ∫₀ᵀ (f'(X)·b + ½f''(X)·σ²) ds` — i.e.
  `∫ f'(X) dX + ½∫ f''(X)σ² ds`, the diffusion the genuine continuous Itô integral. It generalizes
  `ito_formula_gbm` (the `f = S₀·exp` case) by the *same* time-localization of the inner exponent
  `b·t`; constant coefficients keep the diffusion integrand `σ f'(X_s)` a function of `B_s`. The
  shared `SmoothTrunc` plateau lemmas (`cut_eq_id_of_abs_le`, `cutD1_eq_one_of_abs_lt`,
  `phi'_eq_one_of_lt`) were lifted into `ItoFormulaLocalized.lean` so both formulas consume them
  (the values-panel coherence follow-up, now done). corpus 297 → **298**, 262 → **263 full**.

- **Itô's lemma as a process — the semimartingale decomposition**
  (`Foundations/ItoFormulaProcess.lean`, entry `sc-ito-formula-td-process`, `full`). Lifts the
  terminal time-dependent formula (a single fixed-`T` `Lp` statement) to a **process identity**
  holding for *every* `t ≤ T` simultaneously:
  `f(t,B_t) − f(0,B_0) =ᵐ (itoProcessL2Inf t F) + ∫₀ᵗ (f_t + ½f_xx) ds`, the stochastic term the
  genuine Itô-integral **process** `(f_x(·,B) ● B)_t` — a continuous `L²` martingale with an
  everywhere-continuous **local-martingale** modification on the null-augmented filtration, so the
  compensated process `f(t,B_t)−f(0,B_0)−∫₀ᵗ drift` is (a modification of) a continuous local
  martingale. This makes the `[0,∞)` continuous-local-martingale arc (corpus 289→292)
  **load-bearing as an Itô-formula consumer** for the first time, and is the chosen prerequisite for
  the unrestricted-`C²` (stopping-time localization) Itô formula — **Summit C**, now scoped next.
  The build is entirely inside the Itô tower (**no Markov property, no PDE**): the terminal formula's
  witness is now canonical (`ito_formula_td_L2_bddDeriv_explicit` exposes `gfx =ᵐ [f_x(·,B)]`),
  zero-extended to a `[0,∞)` integrand (`exists_fullHorizon_extension`) and matched to each horizon
  by the existing consistency `itoProcessL2Inf_eq_itoProcessCLM`. corpus 298 → **299**,
  263 → **264 full**.

- **The Brownian exit times as a localizing sequence — the localization engine**
  (`Foundations/ExitTime.lean`, entry `sc-exit-times-localizing-sequence`, `full`). The exit times
  `τ_N = inf {t : N ≤ |B_t|}` of the **closed** exterior `{x : N ≤ |x|}` form the repo's **first
  genuine `IsLocalizingSequence`** (`isLocalizingSequence_exitTime`) for the null-augmented Brownian
  filtration: each `τ_N` is a stopping time for the **raw** filtration (`isStoppingTime_exitTime`),
  the sequence is a.s. monotone (`exitTime_monotone`), and it escapes to `⊤` a.s.
  (`exitTime_tendsto_top`). The **closed** exterior is the decisive design choice — it makes
  `{τ_N ≤ i}` the *attained*-`sInf` event (continuity of paths + `IsClosed.csInf_mem`), hence the
  rational `⋂ₘ ⋃_{q≤i} {N−1/(m+1) ≤ |B_q|}` event, measurable in `𝓕_i` with **no right-continuity**.
  (The open-exterior `{N < |x|}` route only characterizes `{τ_N < i}`, which lands in the
  right-continuous `𝓕_{i⁺}` the natural Brownian filtration does not provide — Blumenthal.) This is
  **Stage 1 of Summit C**: the localization machinery that lifts the bounded-derivative Itô formula
  toward unbounded coefficients. corpus 299 → **300**, 264 → **265 full**.

- **The unrestricted-`C³` Itô formula via stopping-time localization — Summit C**
  (`Foundations/ItoFormulaUnrestricted.lean`, entry `sc-ito-formula-unrestricted-local`, `full`).
  For a general `C³` `f` (six partials, all jointly continuous, **no** growth/boundedness), the
  residual `M_t = f(t,B_t) − f(0,B_0) − ∫₀ᵗ(f_t+½f_xx)ds` is everywhere-continuous, satisfies the
  Itô identity by construction, and is a continuous local martingale in **explicit form**
  (`ito_formula_unrestricted_local`): a localizing sequence `σ_N = min(τ_N, N) ↑ ⊤`
  (`isLocalizingSequence_sigma`, the exit times capped in time) plus per-`N` continuous **true**
  martingales `Mₙ` (`exists_continuous_martingale_modification_infinite` of the truncated integrand)
  agreeing with `M` on `{t ≤ σ_N}`. Stage 2 is the **double cutoff** `fTrunc N = f(φₙ·, φₙ·)`
  (time *and* space — a general `C³` `f` has `t`-derivatives unbounded over `t ∈ ℝ`, so the time cut
  is essential), whose globally-bounded derivatives feed `ito_formula_td_process`; Stage 3 the
  exit-time confinement (`abs_le_N_of_le_exitTime`) + cut-inactivity collapsing `fTrunc → f`; the
  all-time agreement crux `indistinguishable_on_stochInterval` (dense-rational agreement +
  `Set.EqOn.closure` + boundary left-continuity) is proved and axioms-clean. corpus 300 → **301**,
  265 → **266 full**.

- **Summit C in Degenne's `IsLocalMartingale` typeclass — the wrapper completed**
  (`Foundations/ItoFormulaUnrestrictedLocMart.lean`, entry
  `sc-ito-formula-unrestricted-islocalmartingale`, `full`). The unrestricted-`C³` residual `M` is now
  a genuine **`IsLocalMartingale`** (`ito_formula_unrestricted`). The one ingredient beyond the
  explicit form — adaptedness of `M` (`residual_stronglyMeasurable`), reducing to the drift primitive
  `D_t = ∫₀ᵗ drift` being `𝓕_t`-measurable (`driftPrimitive_stronglyMeasurable`: time-clamp the
  integrand so every slice is `𝓕_t`-measurable, then Carathéodory
  `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable` + `StronglyMeasurable.integral_prod_right`,
  worked under a `letI` sub-σ-algebra) — is discharged; then `StronglyAdapted.stoppedProcess_indicator`
  + the all-time agreement `indistinguishable_on_stochInterval` assemble `Locally (Martingale ∧ cadlag)`
  with the exit-time localizer `σ_N`. corpus 301 → **302**, 266 → **267 full**. *Summit C is now
  complete in both the explicit and the typeclass forms.*

**Open frontier:** the Itô formula against a general Itô
process with **adapted** coefficients
(the random-integrand semimartingale form — a new tower layer beyond the constant-coefficient case
just landed); re-ground `discountedGBM_isMartingale` at the *process* level (all `t`, on the
Brownian filtration) on the Itô integral, completing the GBM/BS pricing-tower migration the
terminal-time `discountedGBM_eq_itoIntegral` opens; unrestricted C² Itô formula via localization
(Summit C); the Itô formula *against a general Itô process* `∫ f'(X) dX` (drift+diffusion `X`
beyond the GBM closed form); general-Ω multi-period DMW FTAP; SDE existence and uniqueness
(Itô–Picard iteration); Lévy's martingale characterization of Brownian motion.

## phase: continuous first-FTAP frame — meaning 1 (2026-07-12, corpus 326→330)

The model-agnostic continuous-market EMM frame + the discounted-GBM instance. Four `full` entries
(`gir-continuous-emm-forward`, `gir-discounted-gbm-emm`, `gir-discounted-gbm-no-arbitrage`,
`gir-martingale-reindex`). `isEMM_noArbitrageSimple`: an equivalent martingale measure precludes
arbitrage against SIMPLE (piecewise-constant, predictable, bounded) strategies — a direct term-by-term
proof via the bilinear `condExp` pull-out, sharing the vanishing primitive
`ae_zero_of_nonneg_of_integral_zero` with the discrete FTAP. Instance at `F = ℝ` via
`discountedGBM_isEMM` (`Q = P`).

**Honest scope:** meaning-1. The physical-measure Girsanov EMM `Q ≠ P` is intrinsically bounded-horizon
(`Q = withDensity Z_T` is a martingale measure only on `[0,T]`) → a horizon-aware EMM is the meaning-1.5
backlog. General admissible strategies / NFLVR / the converse (Delbaen–Schachermayer) are meaning-2.
`IsEMM`-on-a-process is DS-shaped, so meaning 2 is additive.

**Next:** (1) horizon-aware EMM for the Girsanov `Q ≠ P` instance; (2) the discrete general-Ω
multi-period DMW crown (the nearer FTAP summit); (3) meaning-2 Delbaen–Schachermayer proper.

## phase: jump/Lévy axis opened — the Itô–Lévy isometry, simple integrands (2026-07-17, corpus 335→336)

The first rung of stochastic integration against a compensated Poisson random measure. One `full`
entry `sc-levy-isometry-compensated-simple`: the Itô–Lévy `L²` isometry for a simple predictable
integrand over a time×mark grid,
`𝔼[(∑ⱼ∑ₗ φⱼₗ·Ñ((tⱼ,tⱼ₊₁]×Aₗ))²] = ∑ⱼ∑ₗ 𝔼[φⱼₗ²]·(tⱼ₊₁−tⱼ)·ν(Aₗ)`. Three new Foundations modules:
`PoissonRandomMeasure` (the PRM as a hypothesis-bundling structure + the Poisson moments `𝔼[N]=r`,
`𝔼[N²]=r²+r` gap-filled by a pmf index-shift `(n+1)·c_r(n+1)=r·c_r(n)`, since Mathlib carries the
Poisson law but not its variance), `PoissonCompensatedIsometryAdapted` (the energy kernel), and
`PoissonCompensatedIntegralL2` (the grid double-sum). The design mirrors our continuous
`ito_isometry_discrete` 1:1 but is hand-rolled: Mathlib/Degenne have no marked simple-process object,
so the `time×mark` double sum is built from scratch.

**The honesty differentiator.** We *prove* what `cgarryZA/LevyStochCalc` (Apache-2.0, cited) states as
its axiom #6. The PRM independence is one faithful structure field `indep_of_disjoint_region`
(independent scattering: `N` on any region disjoint from `D` is independent of `N(·,D)`), which
subsumes disjoint-box and past/future independence and closes *every* cross-term uniformly —
including the same-time / different-mark pairs a marked integrand produces, which neither a pure
disjoint-count nor a pure past/future field would.

**Honest scope:** the isometry is proved for SIMPLE integrands (LevyStochCalc's axiom is over general
`L²` integrands). Deferred, declared: (1) B2 — the dense `L²` extension to a continuous-integral CLM
(mirroring `ItoIntegralL2Dense`, with the extra mark-dimension π-system), i.e. axiom #6 in full; (2)
PRM *existence* (their axiom #2) — Mathlib has no PRM substrate, a separate Summit.

**Update (2026-07-17, B2 norm-form isometry):** `sc-levy-isometry-normform`
(`Foundations/PoissonCompensatedIntegralL2Dense`) recasts the simple isometry into norm-preserving
form `𝔼[(∫ H dÑ)²] = ‖H‖²_{L²(dP⊗dt⊗dν)}` — the integrand's own `L²(P⊗ν̂)`-norm equals the integral's
`L²(P)`-norm (the usual statement, and the identity `LinearMap.extendOfNorm` completes the CLM from).
The integrand-norm computation `∫ H² d(P⊗ν̂) = ∑ⱼ∑ₗ 𝔼[φⱼₗ²]·(tⱼ₊₁−tⱼ)·ν(Aₗ)` mirrors our continuous
`simpleProcessL2_norm_sq` but is *simpler* (disjoint grid boxes ⇒ cross terms vanish by `ν̂(∩)=0`, no
interval-overlap formula). What remains for the full CLM: the integral **operator** over the
*characterised* predictable `L²` needs (a) the overlapping-box bilinear kernel (general integrands,
mirroring `rect_increment_pairing`) and (b) a from-scratch marked-predictable `σ`-algebra + density
for the PRM filtration — a genuine Summit, since Degenne's Brownian `ItoIntegralCLM` machinery is not
reusable for the PRM's own filtration.

**Next:** (1) the CLM operator (overlapping-box kernel + marked-predictable density); (2) the
Itô–Lévy *formula* and a jump-FTAP once the operator exists; (3) upstream the Poisson variance to
Mathlib.

## phase: the Itô–Lévy integral CLM — axiom #6 in full generality (2026-07-18, corpus 336→339)

The compensated-Poisson stochastic integral is now a **continuous linear operator on its full `L²`
closure**, an isometry — `cgarryZA/LevyStochCalc`'s cited **axiom #6 in full generality**, closing the
dense-extension Summit the simple-integrand rungs declared. Three new `full` entries land the two
rungs the prior *Next* called for.

**Rung 2 — the overlapping-box bilinear kernel** (`sc-levy-bilinear-pairing`,
`Foundations/PoissonCompensatedBilinear`): `𝔼[(φa·Ñ(boxa))(φb·Ñ(boxb))] = 𝔼[φa·φb]·ν̂(boxa∩boxb)` for
past-adapted bounded weights over general overlapping space-time boxes — the jump analogue of the
Brownian `rect_increment_pairing`, the inner-product core an isometry sums over. Built on a master
weighted-future pairing that generalizes the `φ≡1` covariance (`Ñ` is an orthogonal martingale
measure). **Design win**: the whole pairing rests on the *single* `indep_of_disjoint_region` field —
no past⟂future `σ`-algebra — and that same independence *buys* the triple-product integrability, so
bounded / `L²` weights suffice.

**Rung 3 — the operator and its isometry** (`sc-levy-integral-clm-isometry`,
`Foundations/PoissonCompensatedSimpleIntegrand` + `PoissonCompensatedIntegralOperator`). The source is
`levySimpleModule`, the marked simple integrands `∑_b φ_b·𝟙_{(s,t]×A}` encoded as a `Finsupp`
**submodule** — adaptedness / finite-mark / boundedness are `+`/`•`/`0`-closed, so no bespoke `Module`
boilerplate (Degenne hand-built the Brownian `SimpleProcess` instances). Two `L²` embeddings
`intAssembly` (into `L²(P)`) and `emb` (into `L²(dP⊗dν̂)`) have equal norm (`assembly_isometry`) —
both squared norms expand into the *same* box-family double sum, equated term-by-term by the rung-2
pairing (compensated side) and Fubini (integrand side). Then `itoLevyIntegralL2 : levyClosure N →L[ℝ]
L²(P)` via `LinearMap.extendOfNorm`, and `‖itoLevyIntegralL2 H‖ = ‖H‖` on the whole closure.

**The Summit dissolved, not climbed.** The prior *Next* flagged a *from-scratch marked-predictable
`σ`-algebra + density* as "a genuine Summit". We sidestepped it: define the operator's domain **as**
`topologicalClosure(range emb)`, so density is a soft `Topology.IsInducing.subtypeVal.dense_iff` fact
(the range's ambient closure *is* the target by construction). The continuous Itô CLM paid for a
bespoke trimmed measure to get a *characterised* predictable `L²`; the isometry-extension needs only
the closure, and gets it for free.

**Two engineering notes worth the record.** (a) `extendOfNorm` into a submodule codomain hits a
`Submodule.addCommMonoid` vs seminormed-group `AddCommMonoid` instance diamond; bridge the `def` with
`refine LinearMap.extendOfNorm (E:=)(F:=) f ?_; exact e` (the CLM goal type pre-pins the normed
instances so `exact` is one cheap `isDefEq`) and the norm theorem with `unfold` + a raised
`maxHeartbeats` (see `docs/patterns.md`). (b) The generic isometry kernel
`norm_extendOfNorm_eq_of_isometry` was lifted out of `WienerIntegral.lean` into a `Mathlib`-only leaf
`Foundations/ExtendOfNormIsometry.lean` (now shared by the Wiener, Itô, and Lévy towers) — a clean
single home whose one-time cost was restaling the whole Itô-chain ledger (its transitive importers).

**Next:** PRM *existence* (LevyStochCalc's axiom #2 — Mathlib has no PRM substrate) is the remaining
Summit; then the Itô–Lévy *formula* and a jump-FTAP become reachable; upstream the Poisson variance to
Mathlib.

## program: HJM interest-rate models — ratified, keystone = a cross-tower stochastic Fubini (2026-07-18)

The next depth axis is the **Heath–Jarrow–Morton drift condition**: the discounted zero-coupon bond
`P(·,T)/B(·)` is a `Q`-martingale for every maturity iff `α(t,T) = σ(t,T) ∫_t^T σ(t,u) du` — the forward-rate
drift pinned entirely by its own volatility. Ambition is the **full landmark**: the bond dynamics are
*derived*, nothing assumed. Design ratified in `docs/hjm-program.md`; tracked in #138 (children #139–#158).

**The axis is not HJM, it is a shared primitive.** The interchange the whole result rests on —
`∫_t^T (∫₀ᵗ σ(s,u) dW_s) du = ∫₀ᵗ (∫_t^T σ(s,u) du) dW_s` — is "an integral-CLM commutes with a Bochner
parameter-integral", i.e. Mathlib's `ContinuousLinearMap.integral_comp_comm` instantiated at each tower's
integral CLM (`wienerIntegralLp`, `itoIntegralCLM_T`, `itoLevyIntegralL2`). The shared `extendOfNorm`/CLM
abstraction that already unified the Wiener, Itô, and Lévy towers is exactly what makes Fubini cheap — the
same *"the Summit dissolved, not climbed"* move as the Lévy CLM. Built once, it also unblocks the Lévy
term-structure (#132, #133) and a Vasicek integrated-rate refactor. One genuinely analytic leaf remains: the
L²-representative lemma (#141).

**Atomic path (19 open issues, 6 tiers):** stochastic Fubini (#141–#145) → log-bond dynamics (#146–#148) →
bond / discounted-bond dynamics (#149–#150) → the drift condition #152 (crown) and #154 (iff) → the bridges,
Ho–Lee #156 and the Vasicek/Hull–White seam #157. Musiela (#158) is a deferred SPDE summit (placeholder).

**Next:** the keystone `stochFubini_ofCLM` (#141, the tower-agnostic primitive) then its Itô instance (#142)
— every downstream tier waits on it; its one hard step is the L²-representative fact (maybe already in Mathlib).
#140 (a would-be `integral_comp_comm` wrapper) was dissolved into #141 as an anti-wrapper cleanup.
