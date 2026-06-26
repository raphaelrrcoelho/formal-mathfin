/-
  MathFin (root module)

  Re-exports the submodules so `lake build` (default target) compiles the
  whole library. Benchmark theorems can `import MathFin` to pull
  everything in, or `import MathFin.<Section>.<Module>` for a
  specific submodule.

  Modules are organized by topic:

  * `Foundations/`   — probability primitives reused across finance.
  * `BlackScholes/`  — BS family (call, put, digitals, Greeks, PDE,
                       Asian / chooser / capped / power / lookback,
                       Breeden-Litzenberger, bisection IV, …).
  * `Futures/`       — Black-76 model.
  * `Binomial/`      — discrete-time tree, CRR convergence, Bermudan
                       sandwich, Merton 1973 American-call dominance.
  * `FixedIncome/`   — ZCB, coupon bonds, duration, convexity, YTM,
                       bootstrap, credit (constant + time-varying hazard),
                       forward-rate non-flat, Vasicek deterministic,
                       Macaulay-vs-modified discrete.
  * `Portfolio/`     — Markowitz, CAPM, two-fund separation, risk parity,
                       Black-Litterman, tangent portfolio FOC.
  * `Performance/`   — Sharpe / Sortino / Treynor / IR / Kelly.
  * `RiskMeasures/`  — VaR/CVaR + coherent-risk axioms, Rockafellar-Uryasev,
                       spectral risk, Herfindahl concentration.
  * `Actuarial/`     — net premium, Gompertz force of mortality.
  * `DeFi/`          — Decentralized-finance market microstructure:
                       constant-product AMMs (Uniswap v2-style), swap
                       output, invariant preservation, internal price.
-/

-- Foundations
import MathFin.Foundations.StandardNormal
import MathFin.Foundations.DoobDecomposition
import MathFin.Foundations.L2MartingaleConvergence
import MathFin.Foundations.BrownianMarkov
-- Markov-chain path law derived from the pin's Ionescu–Tulcea trajectory
-- kernels (Saporito 1.1.2)
import MathFin.Foundations.MarkovPathMeasure
import MathFin.Foundations.ErlangSum
-- Poisson-process theory: superposition, thinning, marginal-from-arrivals,
-- first-interarrival law (Saporito 3.3.5/3.3.6/3.3.9/3.3.10)
import MathFin.Foundations.PoissonSuperposition
import MathFin.Foundations.PoissonThinning
import MathFin.Foundations.PoissonCounting
import MathFin.Foundations.PoissonInterarrival
-- Poisson probability generating function E[x^N] = e^{r(x−1)} (absent from
-- Mathlib); the engine behind Merton-mixture compensation identities
import MathFin.Foundations.PoissonPgf
-- QV of an Itô process: drift contributes nothing (Saporito 7.4.5)
import MathFin.Foundations.ItoProcessQV
import MathFin.Foundations.GaussianMoments
import MathFin.Foundations.BivariateGaussian
import MathFin.Foundations.GaussianCDFDeriv
import MathFin.Foundations.GaussianGirsanov
import MathFin.Foundations.FeynmanKacHeatEquation
import MathFin.Foundations.BrownianMartingale
-- Continuous-time first FTAP: discounted GBM price is a Q-martingale (Wald exponential)
import MathFin.Foundations.ContinuousFTAP
import MathFin.Foundations.BrownianQuadraticVariation
import MathFin.Foundations.QuadraticVariationL2
import MathFin.Foundations.ExpMin
import MathFin.Foundations.FTAP
import MathFin.Foundations.OptionalSamplingInequality
import MathFin.Foundations.LpContinuousMartingaleConvergence
import MathFin.Foundations.MartingaleTransform
import MathFin.Foundations.DoobLpMaximalInequality
import MathFin.Foundations.WienerIntegral
import MathFin.Foundations.WienerIntegralL2
-- Structural / principle modules:
import MathFin.Foundations.StandardGaussianMGF
import MathFin.Foundations.ExponentialDiscount
-- Phase 13 additions:
import MathFin.Foundations.StatePrices
import MathFin.Foundations.TriangleArbitrage
import MathFin.Foundations.CarrMadan
import MathFin.Foundations.AlmgrenChriss
import MathFin.Foundations.ConvexPricingFunctional
import MathFin.Foundations.ConvexSeparation
-- Phase 30 (Bridge A): BSCallHyp / BachelierHyp from IsPreBrownian
import MathFin.Foundations.BSCallHypFromBrownian
-- Phase 31: Pricing entry points from IsPreBrownian (composite corollaries)
import MathFin.Foundations.PricingFromBrownian
-- Phase 32: Variance-swap log-price squared-increment from BrownianQuadraticVariation
import MathFin.Foundations.VarianceSwapFromQV
-- Phase 33: Variance-swap equipartition sum from BrownianQuadraticVariation
import MathFin.Foundations.VarianceSwapEquipartition
-- Phase 34: Variance-swap QV limit theorem (realised-variance → σ²T as n → ∞)
import MathFin.Foundations.VarianceSwapLimit
-- Variance-swap drift immunity: realized variance → σ²T in L² for ANY drift
-- (consumes ItoProcessQV; strengthens phase 34 from expectation-level to L²)
import MathFin.Foundations.VarianceSwapDriftImmunity
-- Phase 35: Discrete Itô formula (adapted from Nagy 2026, SSRN 6336503)
import MathFin.Foundations.DiscreteIto
-- The adapted Itô isometry (increment-independence cornerstone)
import MathFin.Foundations.ItoIsometryAdapted
-- Continuous L²-adapted Itô integral (construction, anchored on Degenne SimpleProcess)
import MathFin.Foundations.ItoIntegralL2
-- The Itô integral as a continuous linear isometry `Lp 2 trim_T → Lp 2 μ` on `[0,T]`
import MathFin.Foundations.ItoIntegralCLM
-- The unbounded-horizon `[0,∞)` Itô integral CLM `Lp 2 trim_full → Lp 2 μ` (Summit B / B2)
import MathFin.Foundations.ItoIntegralL2Dense
-- Covariation of Itô integrals: the bilinear Itô isometry ⟪∫φdB,∫ψdB⟫=⟪φ,ψ⟫ (D1)
import MathFin.Foundations.ItoIntegralCovariation
-- The elementary Itô integral as a process `t ↦ (V●B)_t`, with genuine `L²` content
import MathFin.Foundations.ItoIntegralProcess
-- The Itô integral process is an adapted L² martingale (Summit B / B1a)
import MathFin.Foundations.ItoIntegralProcessMartingale
-- The elementary Itô integral as a continuous local martingale (Summit B / B3)
import MathFin.Foundations.ItoIntegralProcessLocalMartingale
-- The general-integrand Itô integral as an L² martingale on [0,T] (Summit B / B1b)
import MathFin.Foundations.ItoIntegralProcessGeneral
-- The deferred time-indexed Itô isometry E[(φ●B)_t²] = ∫₀ᵗ E[φ²] ds (B1b refinement)
import MathFin.Foundations.ItoIntegralProcessIsometry
-- Pathwise discrete Itô identity for `f(x) = x²` (the squaring keystone)
import MathFin.Foundations.ItoSquaringIdentity
-- Polynomial Itô remainders (x³, x⁴) + the pathwise discrete cubing identity
import MathFin.Foundations.DiscreteItoPolynomial
-- Continuous-time L² Itô formula for `f(x) = x²`: `∑ B ΔB → ½(B_T² − B_0² − T)`
import MathFin.Foundations.ItoFormulaSquaredL2
-- Keystone: `∫₀ᵀ B dB = ½(B_T² − B₀² − T)` as a genuine `itoIntegralCLM_T` identity
-- (the continuous Itô integral's first real consumer)
import MathFin.Foundations.ItoIntegralBrownian
-- Summit A: bounded-derivative continuous-time Itô formula in L² (CLM-identified)
import MathFin.Foundations.WeightedQuadraticVariation
import MathFin.Foundations.ItoFormulaRemainder
import MathFin.Foundations.ItoFormulaC2
import MathFin.Foundations.ItoIntegralRiemannBridge
import MathFin.Foundations.ItoFormulaCLM
-- Summit A′: time-dependent Itô formula in L² — TD Taylor remainder vanishes,
-- TD Riemann↔CLM bridge, and the assembly f(T,B_T) = f(0,B₀) + ∫f_x dB + ∫(f_t+½f_xx)ds
import MathFin.Foundations.ItoFormulaTDRemainder
import MathFin.Foundations.ItoIntegralRiemannBridgeTD
import MathFin.Foundations.ItoFormulaTD
-- Phase 37: FTAP both directions, two-state market (adapted from Nagy 2026)
import MathFin.Foundations.FTAPTwoState
-- Phase 38: Constant-product AMM (adapted from Pusceddu-Bartoletti FMBC 2024)
import MathFin.DeFi.ConstantProductAMM
-- Phase 39: Itô structural drift formula + GBM log-drift (after Nagy 2026)
import MathFin.Foundations.ItoLemma
-- Time-dependent (2D) Itô formula + GBM-as-SDE-solution (genuine exp partials)
import MathFin.Foundations.ItoLemma2D
-- Phase 45: Variance swap log-payoff and QV-limit form equivalence
import MathFin.Foundations.VarianceSwapEquivalence
-- Phase 53: Pricing kernel from two-state FTAP (state-prices composition)
import MathFin.Foundations.PricingKernel
-- Phase 42: Multi-state FTAP backward (hypothesis-form, forward direction proved)
import MathFin.Foundations.FTAPMultiState
import MathFin.Foundations.FTAPDiscrete
-- General-Ω one-period FTAP (Föllmer–Schied 1.55 / one-period DMW, scalar)
import MathFin.Foundations.FTAPOnePeriod
-- General-Ω one-period FTAP, d assets (Esscher minimal-divergence EMM, non-redundant)
import MathFin.Foundations.FTAPOnePeriodVector
-- BlackScholes
import MathFin.BlackScholes.Call
import MathFin.BlackScholes.Put
import MathFin.BlackScholes.PDE
import MathFin.BlackScholes.PutGreeks
import MathFin.BlackScholes.Digital
import MathFin.BlackScholes.DigitalGreeks
import MathFin.BlackScholes.Dividends
import MathFin.BlackScholes.DividendsGreeks
import MathFin.BlackScholes.Forward
import MathFin.BlackScholes.HigherGreeks
import MathFin.BlackScholes.StrikeGreeks
import MathFin.BlackScholes.PutStrikeConvexity
import MathFin.BlackScholes.StaticBounds
import MathFin.BlackScholes.AsianInequality
import MathFin.BlackScholes.ImpliedVolatility
import MathFin.BlackScholes.LognormalMoments
import MathFin.BlackScholes.VarianceSwap
-- Merton (1976) jump-diffusion: Poisson-mixture price, compensation
-- identity, parity (consumes Foundations.PoissonPgf + Call/Put formulas)
import MathFin.BlackScholes.MertonJumpDiffusion
-- Merton dominance (jump risk is never free: vega + gamma/Jensen channels)
-- and the classic Λ′ = Λ(1+k) display (rate-shift identity)
import MathFin.BlackScholes.MertonDominance
import MathFin.BlackScholes.MertonClassicDisplay
import MathFin.BlackScholes.Bachelier
import MathFin.BlackScholes.BachelierGreeks
import MathFin.BlackScholes.Chooser
import MathFin.BlackScholes.CappedCall
import MathFin.BlackScholes.Spreads
import MathFin.BlackScholes.Lookback
import MathFin.BlackScholes.PowerOption
import MathFin.BlackScholes.BreedenLitzenberger
import MathFin.BlackScholes.BisectionIV
-- Structural / principle modules:
import MathFin.BlackScholes.StrikeConvexity
import MathFin.BlackScholes.SpotConvexity
import MathFin.BlackScholes.PriceBounds
-- Phase 13 additions:
import MathFin.BlackScholes.Quanto
import MathFin.BlackScholes.NewtonConvergence
import MathFin.BlackScholes.NewtonRaphsonIV
import MathFin.BlackScholes.LognormalCOV

-- Futures
import MathFin.Futures.Black76
import MathFin.Futures.Black76Greeks
-- Phase 13 additions:
import MathFin.Futures.Swaption

-- Binomial
import MathFin.Binomial.Model
import MathFin.Binomial.American
import MathFin.Binomial.CRRConvergence
import MathFin.Binomial.DriftLimit
import MathFin.Binomial.Bermudan
import MathFin.Binomial.MartingaleRepresentation
import MathFin.Binomial.AmericanCallNoDividend
-- Phase 13 additions:
import MathFin.Binomial.Girsanov
import MathFin.Binomial.SecondFTAP
-- Phase 14: real new theorems
import MathFin.Binomial.MertonAmericanCallTree
import MathFin.Binomial.ReplicatingUniqueness
import MathFin.BlackScholes.GreekSigns
-- Phase 16: reflection-principle algebraic core (André 1887)
import MathFin.Binomial.PathReflection
-- Phase 19: Snell envelope characterization of americanPrice
import MathFin.Binomial.SnellEnvelope
-- Phase 43: Binomial up-probability as two-state FTAP EMM
import MathFin.Binomial.BinomialFromFTAP
-- Phase 44: CRR binomial scheme as discrete-Itô process (drift + QV limits)
import MathFin.Binomial.CRRDiscreteIto
-- CRR → BS characteristic-function convergence (the distributional CLT heart)
import MathFin.Binomial.CRRCharFun
-- CRR → BS in literal closed form `S₀Φ(d₁) − Ke^{−rT}Φ(d₂)` (Φ-landing corollary)
import MathFin.Binomial.CRRClosedForm
-- Phase 20: first-principles core derivations
import MathFin.Foundations.NoArbitrageDerivations
import MathFin.BlackScholes.RiskNeutralProbabilities
-- Phase 22: delta as stock-numeraire probability (Φ(d_1) = Q^(S)(S_T > K))
import MathFin.BlackScholes.StockNumeraire
-- Phase 24: powered call closed form via reduction to BS-call (effective spot/vol)
import MathFin.BlackScholes.PowerCall
-- BS-family Garman normal form (`V = A·Φ(d_1) − K·DF·Φ(d_2)`): the single
-- numéraire-parameterised template consumed by ExchangeOption, Black-76, KMVMerton
import MathFin.BlackScholes.GarmanNormalForm
import MathFin.BlackScholes.ExchangeOption
-- Margrabe BSCallHyp grounding from a joint two-GBM gaussian model (leap-3 closure)
import MathFin.BlackScholes.MargrabeGrounding
-- Phase 25: chooser option as call + put portfolio via PCP at chooser date
import MathFin.BlackScholes.ChooserComposition
-- Phase 46: BS PDE derived from Itô drift + no-arbitrage
import MathFin.BlackScholes.PDEFromIto
-- Feynman–Kac → BS PDE keystone (step 2: the FK price representation)
import MathFin.BlackScholes.PDEFromFeynmanKac
-- Phase 40: Itô lemma L¹-expectation form applied to GBM log (mean + variance)
import MathFin.BlackScholes.GBMLogMoments

-- FixedIncome
import MathFin.FixedIncome.ZCB
import MathFin.FixedIncome.CouponBonds
import MathFin.FixedIncome.Immunization
import MathFin.FixedIncome.ConvexityImmunization
import MathFin.FixedIncome.YieldCurve
import MathFin.FixedIncome.Credit
-- First-to-default: basket intensity = Σ single-name intensities
-- (bridges Foundations.ExpMin into the Credit vocabulary)
import MathFin.FixedIncome.FirstToDefault
import MathFin.FixedIncome.MacaulayModified
import MathFin.FixedIncome.HazardCurve
import MathFin.FixedIncome.ForwardRate
import MathFin.FixedIncome.Vasicek
-- Phase 13 additions:
import MathFin.FixedIncome.KMVMerton
import MathFin.FixedIncome.MeanReversionHalfLife
import MathFin.FixedIncome.CDS
-- Phase 21: first-principles duration-as-price-sensitivity
import MathFin.FixedIncome.DurationSensitivity
-- Phase 22: first-principles convexity-as-second-derivative
import MathFin.FixedIncome.ConvexitySensitivity
-- Phase 27: KMV-Merton structural derivation (probabilistic content of `kmvPD`)
import MathFin.FixedIncome.KMVMertonStructural
-- Phase 28: CDS fair spread under time-varying hazard (cash-flow balance)
import MathFin.FixedIncome.CDSTimeVarying
-- Phase 41: Vasicek SDE closed-form (full SDE, mean + variance)
import MathFin.FixedIncome.VasicekSDE

-- Portfolio
import MathFin.Portfolio.Markowitz
import MathFin.Portfolio.CovariancePSD
import MathFin.Portfolio.MarkowitzNAsset
import MathFin.Portfolio.CAPM
import MathFin.Portfolio.TwoFundSeparation
import MathFin.Portfolio.RiskParity
import MathFin.Portfolio.BlackLitterman
import MathFin.Portfolio.TangentPortfolio
-- Phase 13 additions:
import MathFin.Portfolio.TangentPortfolioN
-- Phase 21: first-principles Sharpe-FOC and CAPM-equilibrium derivations
import MathFin.Portfolio.SharpeFOCDerivation
import MathFin.Portfolio.CAPMEquilibrium
-- Phase 23: N-asset Markowitz Lagrangian FOC (forward direction)
import MathFin.Portfolio.MarkowitzLagrangian
-- Phase 26: N-asset risk parity from log-barrier Lagrangian FOC
import MathFin.Portfolio.RiskParityFOC
-- Phase 29: N-dim Black-Litterman posterior (matrix form)
import MathFin.Portfolio.BlackLittermanND

-- Performance
import MathFin.Performance.Ratios
import MathFin.Performance.RatiosExtended
import MathFin.Performance.Kelly

-- RiskMeasures
import MathFin.RiskMeasures.Gaussian
import MathFin.RiskMeasures.CoherentAxioms
import MathFin.RiskMeasures.Additivity
import MathFin.RiskMeasures.RockafellarUryasev
import MathFin.RiskMeasures.Spectral
import MathFin.RiskMeasures.Concentration
-- Phase 21: first-principles coherent-axiom derivation from concave utility
import MathFin.RiskMeasures.UtilityDerivation

-- Bridges (certified cross-domain unifications)
import MathFin.Bridges.ConcentrationVariance
import MathFin.Bridges.SurvivalUnification

-- Actuarial
import MathFin.Actuarial.Insurance
import MathFin.Actuarial.Mortality
-- Phase 13 additions:
import MathFin.Actuarial.CompoundPoisson

-- Upstream (Degenne BrownianMotion) modules consumed ONLY by benchmark
-- wrappers, imported here so `lake build` puts them in the build graph —
-- nothing else in MathFin/ imports them, and a snippet import of an unbuilt
-- module fails with a silently-empty environment (found 2026-06-05 via
-- cm-thm-4.3.7; its sibling cm-thm-4.3.9 works only because
-- Foundations/LpContinuousMartingaleConvergence imports Degenne's DoobLp).
import BrownianMotion.StochasticIntegral.LocalMartingale
