/-
  HybridVerify (root module)

  Re-exports the submodules so `lake build` (default target) compiles the
  whole library. Benchmark theorems can `import HybridVerify` to pull
  everything in, or `import HybridVerify.<Section>.<Module>` for a
  specific submodule.

  Modules are organized by topic:

  * `Foundations/`   — probability primitives reused across finance.
  * `BlackScholes/`  — BS family (call, put, digitals, Greeks, PDE, …).
  * `Futures/`       — Black-76 model.
  * `Binomial/`      — discrete-time tree model + CRR convergence.
  * `FixedIncome/`   — ZCB, coupon bonds, duration, convexity, YTM,
                       bootstrap, credit.
  * `Portfolio/`     — Markowitz, CAPM, two-fund separation.
  * `Performance/`   — Sharpe / Sortino / Treynor / IR / Kelly.
  * `RiskMeasures/`  — VaR/CVaR + coherent-risk axioms.
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

-- Futures
import HybridVerify.Futures.Black76
import HybridVerify.Futures.Black76Greeks

-- Binomial
import HybridVerify.Binomial.Model
import HybridVerify.Binomial.American
import HybridVerify.Binomial.CRRConvergence
import HybridVerify.Binomial.DriftLimit

-- FixedIncome
import HybridVerify.FixedIncome.ZCB
import HybridVerify.FixedIncome.CouponBonds
import HybridVerify.FixedIncome.Immunization
import HybridVerify.FixedIncome.ConvexityImmunization
import HybridVerify.FixedIncome.YieldCurve
import HybridVerify.FixedIncome.Credit

-- Portfolio
import HybridVerify.Portfolio.Markowitz
import HybridVerify.Portfolio.MarkowitzNAsset
import HybridVerify.Portfolio.CAPM
import HybridVerify.Portfolio.TwoFundSeparation

-- Performance
import HybridVerify.Performance.Ratios
import HybridVerify.Performance.RatiosExtended
import HybridVerify.Performance.Kelly

-- RiskMeasures
import HybridVerify.RiskMeasures.Gaussian
import HybridVerify.RiskMeasures.CoherentAxioms
import HybridVerify.RiskMeasures.Additivity
