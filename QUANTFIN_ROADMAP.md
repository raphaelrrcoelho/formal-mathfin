# quant-finance roadmap (unblocked path)

the 16 remaining `reduced_core` theorems in `FORMALIZATION_STATUS.md` are upstream-gated on the itô integral, measure-change machinery, and continuous-time poisson processes. this document captures what can be built **without** waiting on upstream mathlib or degenne work, framed as a quant-finance project rather than a textbook audit.

all of it either (a) reuses the existing `bsd1`/`bsd2`/`Phi`/`bs_identity`/`hasDerivAt_Phi`/`bsV` infrastructure, (b) is a parallel construction to black-scholes using the same gaussian machinery, or (c) is discrete-time / classical-analysis material that doesn't touch the itô integral.

## phase 1: complete the static black-scholes world (~1 week)

quick wins, mostly direct extensions of `lean/HybridVerify/BlackScholesPDE.lean` and `BlackScholesCall.lean`.

- [ ] **black-scholes put formula** via put-call parity `C − P = S − K · e^{-rT}`. pure algebra from the existing call formula. ~50 lines.
- [ ] **vega**: `∂V/∂σ` for the BS call. uses chain rule on `bsd1` w.r.t. σ, then magic identity. ~100-150 lines.
- [ ] **rho**: `∂V/∂r` for the BS call. similar machinery. ~100 lines.
- [ ] **cash-or-nothing digital option**: `V = e^{-rT} · Φ(d_2)`. trivial wrapper over existing `Phi` + `bsd2`. ~75 lines.
- [ ] **asset-or-nothing digital option**: `V = S · Φ(d_1)`. ~75 lines.
- [ ] **forward and futures pricing** under no-arbitrage replication. `F = S_0 · e^{rT}`. pure discrete-time algebra. ~100 lines.

milestone at end of phase 1: complete BS sensitivities (delta, gamma, vega, theta, rho) plus the full vanilla european product set (call, put, 2 digitals, forward).

## phase 2: vanilla derivatives theory complete (~2 weeks)

- [ ] **bachelier model option pricing** (arithmetic BM, no lognormal). the simpler 19th-century counterpart to black-scholes, closed form involves `Φ` but no log-transform. parallel structure to the existing call formula, different price dynamics. ~300 lines.
- [ ] **implied volatility uniqueness via vega-positivity**. proves BS is monotone in σ, hence its inverse is well-defined as a function of price. uses the vega formula from phase 1. practically useful (calibration uses implied vol inversion). ~200 lines.
- [ ] **black formula** for options on futures. variant of BS with zero drift in the underlying. ~150 lines.

milestone: a "rigorous theory of vanilla derivatives" claim. covers the standard closed-form option pricing models taught in a quant program.

## phase 3: discrete-continuous bridge (multi-session)

- [ ] **discrete-time binomial tree pricing framework**. european + american option pricing on a CRR tree via dynamic programming. uses the existing FTAP scaffolding (`lean/HybridVerify/FTAP.lean`) for no-arbitrage. doesn't touch itô. ~500-800 lines.
- [ ] **CRR convergence theorem**: binomial pricing converges to black-scholes as `Δt → 0`. classic limit theorem using the CLT (already have it) plus careful drift correction (`u_n, d_n, p_n` chosen so the binomial mean and variance match the GBM mean and variance to first order). ~500-800 lines.

milestone: "discrete and continuous pricing models, formally linked." closes the loop between the binomial pedagogy and the BS continuous-time limit.

## phase 4: upstream foundations

real upstream contributions that would land in mathlib or degenne. each is a separate PR.

- [ ] **`Real.erf` for mathlib**. mathlib has no error function. drafting it would unlock cleaner standard-normal-CDF APIs across this project and the broader probability ecosystem. ~300 lines plus the `Real.erfc`, `Real.erfinv` companions and basic identities. would also let us replace our local `Phi` definition with `(1 + erf(x/√2))/2`.
- [ ] **`gaussianReal_Iic_hasDerivAt` for mathlib**. our `hasDerivAt_Phi` upstreamed. ~50 lines once `Real.erf` lands (else ~100 lines via the FTC approach we used). this is the precise lemma `Φ' = ϕ` that mathlib is currently missing.
- [ ] **mathlib PR (already drafted in `staging/mathlib-pr/`)**: the 4 gaussian tail / completing-the-square lemmas. independent of the above.
- [ ] **degenne PR (already drafted in `staging/degenne-pr/`)**: the two BM martingales `IsFilteredPreBrownian.squareSubTime_isMartingale` and `IsFilteredPreBrownian.waldExponential_isMartingale`. independent.

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

if optimizing for the project's "compelling quant-finance artifact" framing:

1. **week 1**: phase 1 (put + greeks + digitals + forward pricing). doubles the finance-relevant `full` count, all from existing infrastructure.
2. **week 2-3**: phase 2 (bachelier + implied vol + black). adds parallel models and the implied-vol theory bridge.
3. **week 4+**: pick **either** phase 3 (binomial → BS convergence, big and pedagogical) **or** phase 4 (`Real.erf` for mathlib, real upstream contribution with broader impact). do not start both simultaneously.

each phase is independently shippable. the project's README + `FORMALIZATION_STATUS.md` should be updated at the end of each phase with the new `full` counts and the new theorems.

## what done looks like

end of phase 3: ~15-20 new `full` finance-specific theorems. the project becomes the most thoroughly formalized treatment of vanilla derivatives pricing in lean 4. coverage breakdown becomes:
- ~40-45 `full` (was 25)
- ~24 `library_wrapper` (unchanged)
- ~16 `reduced_core` (unchanged; itô-gated)

it's still niche. the audience is still small. but it's a coherent, complete artifact rather than a partial textbook audit.
