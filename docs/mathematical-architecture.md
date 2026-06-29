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
| **Convex duality** (separation / Legendre–Fenchel) | I (pricing) ↔ IV (risk) | **WIRED (Phase 1, 2026-06-29).** The shared root `Foundations/ConvexDuality.exists_pos_separating_of_cone_disjoint_simplex` (cone↔simplex) + its companion `exists_separating_of_not_mem_cone` (point↔cone) now carry **both** towers: the FTAP kernel `exists_pos_dual_of_disjoint_stdSimplex` is *re-derived* from the root (pricing side), and the coherent-risk ADEH representation `RiskMeasures/AcceptanceSet.coherentRisk_isLUB` is its risk-side instance (`WorstCaseRisk.worstCase_isLUB` a concrete case). Superhedging is wired as the `SuperhedgingDuality.emm_le_superReplication` bound; the strong-duality *equality* awaits a finite-dim Farkas (Mathlib gap). |
| **The numéraire** (log-optimal portfolio) | IV (Kelly/portfolio) ↔ I (EMM) | **ABSENT.** `Performance/Kelly` and `BlackScholes/StockNumeraire` exist; the numéraire-portfolio ⟷ EMM identity is unstated. |
| **Donsker / CLT** (discrete → continuous) | Binomial ↔ Black–Scholes | **WIRED** (`CRRConvergence.binomialPrice_call_tendsto_bs`). |

## Coherence verdict

Individually the towers are coherent and the *engineering* architecture is documented. **Phase 1
(2026-06-29) realized the spine's #1 unification**: the convex-duality bridge (I↔IV) is now WIRED — the
FTAP separating functional and the coherent-risk-measure representation are *proved* to be the same
Hahn–Banach root (`Foundations/ConvexDuality`), no longer split across files that never name it. Of the
four bridges, Feynman–Kac (II↔III), Donsker (discrete↔continuous), and now convex-duality (I↔IV) are
WIRED; Girsanov (I↔II) and the numéraire (IV↔I) remain open. **The library's pricing↔risk spine is
realized; the continuous-time (Girsanov) and portfolio (numéraire) seams are the next bridges.**

## The higher-math unification roadmap (apparently-disconnected fields that connect)

Ranked by leverage × tractability:

1. **The convex-duality unification (I↔IV) — ✅ REALIZED (Phase 1, 2026-06-29).** The shared root is
   extracted (`Foundations/ConvexDuality`: the cone↔simplex separation + the point↔cone companion, sharing
   two named atoms), and the FTAP kernel (re-derived from it), the coherent-risk ADEH representation
   (`coherentRisk_isLUB`), a concrete instance (`worstCase_isLUB`), and the superhedging bound
   (`emm_le_superReplication`) are all instances/consumers of it. **Proved: the FTAP and the
   coherent-risk-measure representation are the same Hahn–Banach theorem.** Remaining as backlog: the
   superhedging strong-duality *equality* (needs a finite-dim Farkas — a Mathlib gap), and the Gaussian
   `CVaR_α(L) = sup_{Q∈Q_α} E_Q[L]` robust form (the continuous instance, off the finite-state spine).

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
