/-
  HybridVerify (root module)

  Re-exports the submodules so `lake build` (default target) compiles the
  whole library. Benchmark theorems can `import HybridVerify` to pull
  everything in, or `import HybridVerify.<Section>.<Module>` for a
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
-/

-- Foundations
import HybridVerify.Foundations.Basic
import HybridVerify.Foundations.BivariateGaussian
import HybridVerify.Foundations.GaussianCDFDeriv
import HybridVerify.Foundations.FeynmanKacHeatEquation
import HybridVerify.Foundations.BrownianMartingale
import HybridVerify.Foundations.BrownianQuadraticVariation
import HybridVerify.Foundations.CondExpJensen
import HybridVerify.Foundations.ExpMin
import HybridVerify.Foundations.FTAP
import HybridVerify.Foundations.LpContinuousMartingaleConvergence
import HybridVerify.Foundations.MartingaleTransform
import HybridVerify.Foundations.MathlibLp
import HybridVerify.Foundations.WienerIntegral
import HybridVerify.Foundations.WienerIntegralL2

-- BlackScholes
import HybridVerify.BlackScholes.Call
import HybridVerify.BlackScholes.Put
import HybridVerify.BlackScholes.PDE
import HybridVerify.BlackScholes.PutGreeks
import HybridVerify.BlackScholes.Digital
import HybridVerify.BlackScholes.DigitalGreeks
import HybridVerify.BlackScholes.Dividends
import HybridVerify.BlackScholes.DividendsGreeks
import HybridVerify.BlackScholes.Forward
import HybridVerify.BlackScholes.HigherGreeks
import HybridVerify.BlackScholes.StrikeGreeks
import HybridVerify.BlackScholes.PutStrikeConvexity
import HybridVerify.BlackScholes.StaticBounds
import HybridVerify.BlackScholes.AsianInequality
import HybridVerify.BlackScholes.ImpliedVolatility
import HybridVerify.BlackScholes.LognormalMoments
import HybridVerify.BlackScholes.VarianceSwap
import HybridVerify.BlackScholes.Bachelier
import HybridVerify.BlackScholes.BachelierGreeks
import HybridVerify.BlackScholes.Chooser
import HybridVerify.BlackScholes.CappedCall
import HybridVerify.BlackScholes.Spreads
import HybridVerify.BlackScholes.Lookback
import HybridVerify.BlackScholes.PowerOption
import HybridVerify.BlackScholes.BreedenLitzenberger
import HybridVerify.BlackScholes.BisectionIV

-- Futures
import HybridVerify.Futures.Black76
import HybridVerify.Futures.Black76Greeks

-- Binomial
import HybridVerify.Binomial.Model
import HybridVerify.Binomial.American
import HybridVerify.Binomial.CRRConvergence
import HybridVerify.Binomial.DriftLimit
import HybridVerify.Binomial.Bermudan
import HybridVerify.Binomial.AmericanCallNoDividend

-- FixedIncome
import HybridVerify.FixedIncome.ZCB
import HybridVerify.FixedIncome.CouponBonds
import HybridVerify.FixedIncome.Immunization
import HybridVerify.FixedIncome.ConvexityImmunization
import HybridVerify.FixedIncome.YieldCurve
import HybridVerify.FixedIncome.Credit
import HybridVerify.FixedIncome.MacaulayModified
import HybridVerify.FixedIncome.HazardCurve
import HybridVerify.FixedIncome.ForwardRate
import HybridVerify.FixedIncome.Vasicek

-- Portfolio
import HybridVerify.Portfolio.Markowitz
import HybridVerify.Portfolio.MarkowitzNAsset
import HybridVerify.Portfolio.CAPM
import HybridVerify.Portfolio.TwoFundSeparation
import HybridVerify.Portfolio.RiskParity
import HybridVerify.Portfolio.BlackLitterman
import HybridVerify.Portfolio.TangentPortfolio

-- Performance
import HybridVerify.Performance.Ratios
import HybridVerify.Performance.RatiosExtended
import HybridVerify.Performance.Kelly

-- RiskMeasures
import HybridVerify.RiskMeasures.Gaussian
import HybridVerify.RiskMeasures.CoherentAxioms
import HybridVerify.RiskMeasures.Additivity
import HybridVerify.RiskMeasures.RockafellarUryasev
import HybridVerify.RiskMeasures.Spectral
import HybridVerify.RiskMeasures.Concentration

-- Actuarial
import HybridVerify.Actuarial.Insurance
import HybridVerify.Actuarial.Mortality
