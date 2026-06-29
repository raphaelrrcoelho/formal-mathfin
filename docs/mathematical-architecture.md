# The mathematical architecture — the field's spine

Companion to [`architecture.md`](architecture.md), which documents the **engineering** architecture
(the three honesty tiers, the principle modules, the bridge methodology). **This** document is the
**mathematical** architecture: the unifying spine of mathematical finance, how the library's towers map
onto it, where the seams are coherent versus open, and the higher-level unification opportunities. It
exists because a top-notch formalization is not "all the theorems proved" — it is *the theorems organized
around the field's actual organizing principles, with the deep connections made load-bearing.*

Written 2026-06-29 from a whole-program architectural validation (grounded in code at every seam).

## The spine: four pillars + connective tissue

Mathematical finance is a few deep principles whose *consequences* are the models. The library has the
pillars; the question is whether the **connective tissue** that makes them one architecture is realized.

### Pillar I — No-arbitrage as convex duality (the separating hyperplane)
The FTAP: *no-arbitrage ⟺ ∃ equivalent martingale measure.* Mathematically this **is** the
separating-hyperplane theorem — the attainable-gains cone misses the positive orthant ⟺ a
strictly-positive functional (the EMM) separates them; price `= ⟨EMM, payoff⟩`.
- **Root:** `Foundations/ConvexSeparation.exists_pos_dual_of_disjoint_stdSimplex` — its own docstring:
  *"the separating hyperplane **is** the equivalent martingale measure."*
- **Instances:** `FTAPOnePeriod`/`FTAPOnePeriodVector`/`FTAPDiscrete`/`FTAPMultiState`/`FTAPTwoState`,
  `StatePrices`, `ConvexPricingFunctional` (the EMM as a convexity-preserving positive operator).

### Pillar II — Stochastic calculus (Itô semimartingales)
The engine of continuous-time models: every model is `dX = b dt + σ dB`, and Itô's formula + the
stochastic integral make functionals of `X` computable.
- **Library:** the Itô tower — `ItoIntegralCLM` (+ isometry), `QuadraticVariationL2`,
  `ItoFormulaUnrestricted` (general C³ as a continuous local martingale), `ItoFormulaGBM`.

### Pillar III — The probabilistic ⟷ analytic duality (generator / Feynman–Kac / PDE)
The same price is a risk-neutral **expectation** (probabilistic) and a **PDE solution** (analytic); the
bridge is the infinitesimal generator: Itô ⟹ Kolmogorov backward equation ⟹ Feynman–Kac.
- **Library:** `FeynmanKacHeatEquation` + `BlackScholes/PDEFromFeynmanKac` (the BS-PDE keystone, built);
  `BlackScholes/PDEFromIto` (the Itô-drift route).

### Pillar IV — Intensity & exponential families (the tractability backbone)
Closed forms come from Gaussian/lognormal/exponential structure; and a single *"exponential of an
integrated intensity"* unifies discounting, mortality, credit hazard, and the Poisson rate.
- **Library:** `StandardNormal`/`GaussianMoments` (Gaussian closed forms), `ExponentialDiscount`
  (the shared root), `Bridges/SurvivalUnification` (mortality ≡ credit hazard, *certified*),
  `GaussianGirsanov` (the Esscher exponential tilt).

## The connective tissue — what would make it ONE architecture

| Bridge | Connects | Status |
|---|---|---|
| **Girsanov / Esscher** (change of measure) | I (EMM) ↔ II (Itô) ↔ IV (exp tilt) | **OPEN at I↔II.** `ContinuousFTAP.discountedGBM_isMartingale` is proved via the **Wald-exponential shortcut**, not an Itô–Girsanov change of measure; `ItoFormulaGBM` carries a *second*, separate discounted-GBM fact. The d-asset Esscher FTAP (IV) is a *discrete* Girsanov, unlinked to the continuous one. `reduced_core gir/sc-thm-9.1.8` is the missing continuous Girsanov. |
| **Feynman–Kac** (generator) | II ↔ III | **WIRED** (BS-PDE keystone). Not yet abstracted to a general generator / Kolmogorov-backward framework. |
| **Convex duality** (separation / Legendre–Fenchel) | I (pricing) ↔ IV (risk) | **ABSENT.** `CoherentAxioms` (the ADEH axioms) and `RockafellarUryasev` (CVaR as a variational `min`) carry **no** dual representation and **no** link to the FTAP's separating functional — though they are the *same* sup-over-measures duality. |
| **The numéraire** (log-optimal portfolio) | IV (Kelly/portfolio) ↔ I (EMM) | **ABSENT.** `Performance/Kelly` and `BlackScholes/StockNumeraire` exist; the numéraire-portfolio ⟷ EMM identity is unstated. |
| **Donsker / CLT** (discrete → continuous) | Binomial ↔ Black–Scholes | **WIRED** (`CRRConvergence.binomialPrice_call_tendsto_bs`). |

## Coherence verdict

Individually the towers are coherent and the *engineering* architecture is documented. But the
**mathematical spine is latent, not realized**: two of the four bridges are open (Girsanov I↔II,
convex-duality I↔IV), and the field's single organizing principle — *the FTAP separating functional =
the coherent-risk-measure representation = the superhedging dual* — is split across five files that never
name it. **The library is a set of coherent towers, not yet a unified theory.**

## The higher-math unification roadmap (apparently-disconnected fields that connect)

Ranked by leverage × tractability:

1. **The convex-duality unification (I↔IV) — HIGHEST LEVERAGE; the pieces already exist.**
   Extract the shared root (a positive separating functional / Legendre–Fenchel dual) and make
   `{FTAP, ConvexPricingFunctional, coherent-risk representation, CVaR robust form, superhedging bounds}`
   instances of it. It connects the two *most-disconnected* towers (pricing ↔ risk), and it is
   *finite-dimensional convex analysis* — Mathlib-strong, **more tractable than Girsanov.** The deep
   truth: **the FTAP and the coherent-risk-measure representation are the same Hahn–Banach theorem**;
   `CVaR_α(L) = sup_{Q∈Q_α} E_Q[L]` is literally pricing under a set of measures.

2. **Girsanov as the I↔II connective tissue.** Reframes the crown-jewel conversion: not "convert a stub,"
   but *derive the continuous EMM from the Itô tower* — retiring the Wald shortcut, unifying the two
   discounted-GBM facts, and making the discrete Esscher FTAP and continuous Girsanov *one* change-of-measure
   principle. (First brick: the adapted Doléans–Dade exponential — see `roadmap.md`.)

3. **The generator / Kolmogorov abstraction (II↔III).** Abstract Feynman–Kac into the infinitesimal
   generator → backward equation, of which the BS-PDE, the heat equation, and Vasicek are instances.

4. **The intensity / Cox extension (IV).** Extend the built `ExponentialDiscount`/`SurvivalUnification`
   root to *stochastic* intensity (Cox / doubly-stochastic Poisson), unifying credit, mortality, and the
   Poisson tower; the Esscher tilt = minimal-relative-entropy change ties IV back to I and to information
   theory.

5. **The numéraire / log-optimal connection (IV↔I).** The Kelly/log-optimal portfolio is the numéraire
   under which the EMM is the physical measure — connecting portfolio choice to pricing.

## What "top-notch" means at this level

Not more theorems, not polish — **realizing the architecture**: naming the shared roots and wiring the
open seams, so the library becomes a *formal theory of mathematical finance organized around its actual
spine.* That is the roadmap's elusive "tier 3": original not as a new theorem, but as a coherent formal
**architecture** of the field that no one has built.
