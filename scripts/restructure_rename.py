#!/usr/bin/env python3
"""One-shot rewrite of module paths after the directory restructure."""
import os
import re
import sys

ROOT = "/home/rapha/code/automated_proofs_quantfin"

# Mapping: old fully-qualified module name -> new fully-qualified module name.
# Order matters: process longest prefixes first so e.g. `HybridVerify.BlackScholesCall`
# is rewritten before any partial match.
MAPPING = [
    # Foundations
    ("HybridVerify.BivariateGaussian", "HybridVerify.Foundations.BivariateGaussian"),
    ("HybridVerify.GaussianCDFDeriv", "HybridVerify.Foundations.GaussianCDFDeriv"),
    ("HybridVerify.FeynmanKacHeatEquation", "HybridVerify.Foundations.FeynmanKacHeatEquation"),
    ("HybridVerify.BrownianMartingale", "HybridVerify.Foundations.BrownianMartingale"),
    ("HybridVerify.BrownianQuadraticVariation", "HybridVerify.Foundations.BrownianQuadraticVariation"),
    ("HybridVerify.CondExpJensen", "HybridVerify.Foundations.CondExpJensen"),
    ("HybridVerify.ExpMin", "HybridVerify.Foundations.ExpMin"),
    ("HybridVerify.FTAP", "HybridVerify.Foundations.FTAP"),
    ("HybridVerify.LpContinuousMartingaleConvergence", "HybridVerify.Foundations.LpContinuousMartingaleConvergence"),
    ("HybridVerify.MartingaleTransform", "HybridVerify.Foundations.MartingaleTransform"),
    ("HybridVerify.MathlibLp", "HybridVerify.Foundations.MathlibLp"),
    ("HybridVerify.WienerIntegralL2", "HybridVerify.Foundations.WienerIntegralL2"),
    ("HybridVerify.WienerIntegral", "HybridVerify.Foundations.WienerIntegral"),
    ("HybridVerify.Basic", "HybridVerify.Foundations.Basic"),
    # BlackScholes (longest first)
    ("HybridVerify.BlackScholesDigitalGreeks", "HybridVerify.BlackScholes.DigitalGreeks"),
    ("HybridVerify.BlackScholesDividendsGreeks", "HybridVerify.BlackScholes.DividendsGreeks"),
    ("HybridVerify.BlackScholesHigherGreeks", "HybridVerify.BlackScholes.HigherGreeks"),
    ("HybridVerify.BlackScholesPutGreeks", "HybridVerify.BlackScholes.PutGreeks"),
    ("HybridVerify.BlackScholesDigital", "HybridVerify.BlackScholes.Digital"),
    ("HybridVerify.BlackScholesDividends", "HybridVerify.BlackScholes.Dividends"),
    ("HybridVerify.BlackScholesForward", "HybridVerify.BlackScholes.Forward"),
    ("HybridVerify.BlackScholesCall", "HybridVerify.BlackScholes.Call"),
    ("HybridVerify.BlackScholesPDE", "HybridVerify.BlackScholes.PDE"),
    ("HybridVerify.BlackScholesPut", "HybridVerify.BlackScholes.Put"),
    ("HybridVerify.OptionStrikeProperties", "HybridVerify.BlackScholes.StrikeGreeks"),
    ("HybridVerify.StaticOptionBounds", "HybridVerify.BlackScholes.StaticBounds"),
    ("HybridVerify.AsianOptionInequality", "HybridVerify.BlackScholes.AsianInequality"),
    ("HybridVerify.ImpliedVolatility", "HybridVerify.BlackScholes.ImpliedVolatility"),
    ("HybridVerify.LognormalSecondMoment", "HybridVerify.BlackScholes.LognormalMoments"),
    ("HybridVerify.VarianceSwap", "HybridVerify.BlackScholes.VarianceSwap"),
    ("HybridVerify.BachelierGreeks", "HybridVerify.BlackScholes.BachelierGreeks"),
    ("HybridVerify.BachelierModel", "HybridVerify.BlackScholes.Bachelier"),
    # Futures (Black-76)
    ("HybridVerify.BlackFuturesGreeks", "HybridVerify.Futures.Black76Greeks"),
    ("HybridVerify.BlackFutures", "HybridVerify.Futures.Black76"),
    # Binomial
    ("HybridVerify.AmericanBinomial", "HybridVerify.Binomial.American"),
    ("HybridVerify.BinomialCRRConvergence", "HybridVerify.Binomial.CRRConvergence"),
    ("HybridVerify.BinomialDriftLimit", "HybridVerify.Binomial.DriftLimit"),
    ("HybridVerify.BinomialModel", "HybridVerify.Binomial.Model"),
    # FixedIncome (do FixedIncome itself last among this group)
    ("HybridVerify.CouponBondsAndAnnuities", "HybridVerify.FixedIncome.CouponBonds"),
    ("HybridVerify.BondConvexityImmunization", "HybridVerify.FixedIncome.ConvexityImmunization"),
    ("HybridVerify.BondImmunization", "HybridVerify.FixedIncome.Immunization"),
    ("HybridVerify.YieldCurveBootstrap", "HybridVerify.FixedIncome.YieldCurve"),
    ("HybridVerify.CreditSpread", "HybridVerify.FixedIncome.Credit"),
    ("HybridVerify.FixedIncome", "HybridVerify.FixedIncome.ZCB"),
    # Portfolio
    ("HybridVerify.MarkowitzNAsset", "HybridVerify.Portfolio.MarkowitzNAsset"),
    ("HybridVerify.Markowitz", "HybridVerify.Portfolio.Markowitz"),
    ("HybridVerify.CAPM", "HybridVerify.Portfolio.CAPM"),
    ("HybridVerify.TwoFundSeparation", "HybridVerify.Portfolio.TwoFundSeparation"),
    # Performance
    ("HybridVerify.PerformanceRatiosExtended", "HybridVerify.Performance.RatiosExtended"),
    ("HybridVerify.PerformanceRatios", "HybridVerify.Performance.Ratios"),
    ("HybridVerify.MultiPeriodKelly", "HybridVerify.Performance.Kelly"),
    # RiskMeasures
    ("HybridVerify.GaussianRiskMeasures", "HybridVerify.RiskMeasures.Gaussian"),
    ("HybridVerify.RiskMeasureAxioms", "HybridVerify.RiskMeasures.CoherentAxioms"),
]

# StrikeConvexityAndRiskAdditivity is split; map per lemma later in the JSON.
# For .lean files (no external imports of it expected), do nothing here.

# Bench-JSON-specific: rewrite split file references based on the imported lemma
JSON_BENCHMARK_SPLITS = {
    "mf-gaussianPDF-symmetry": "HybridVerify.BlackScholes.PutStrikeConvexity",
    "mf-bsP-KK-deriv": "HybridVerify.BlackScholes.PutStrikeConvexity",
    "mf-gaussian-var-additive-rho-one": "HybridVerify.RiskMeasures.Additivity",
    "mf-gaussian-cvar-additive-rho-one": "HybridVerify.RiskMeasures.Additivity",
}

def compile_pattern(old):
    # Match the old name only when not followed by a word char or dot.
    return re.compile(re.escape(old) + r"(?![\w.])")


def apply_mapping(text):
    for old, new in MAPPING:
        text = compile_pattern(old).sub(new, text)
    # Handle the split — assume the .lean files don't import the old file
    # but the JSON might. For JSON, replace based on the lemma id; for .lean,
    # just replace the old name with PutStrikeConvexity (the BS half).
    old_split = "HybridVerify.StrikeConvexityAndRiskAdditivity"
    text = compile_pattern(old_split).sub("HybridVerify.BlackScholes.PutStrikeConvexity", text)
    return text


def process_lean_files():
    base = os.path.join(ROOT, "lean", "HybridVerify")
    changed = 0
    for root, _dirs, files in os.walk(base):
        for f in files:
            if not f.endswith(".lean"):
                continue
            path = os.path.join(root, f)
            with open(path, "r") as fh:
                text = fh.read()
            new_text = apply_mapping(text)
            if new_text != text:
                with open(path, "w") as fh:
                    fh.write(new_text)
                changed += 1
    return changed


def process_json_files():
    base = os.path.join(ROOT, "benchmarks")
    changed = 0
    for f in os.listdir(base):
        if not f.endswith(".json"):
            continue
        path = os.path.join(base, f)
        with open(path, "r") as fh:
            text = fh.read()
        # Apply normal mapping first.
        new_text = apply_mapping(text)
        # Then handle the split entries: rewrite the (now BlackScholes.PutStrikeConvexity)
        # import to the correct half for each split benchmark entry.
        for theorem_id, target in JSON_BENCHMARK_SPLITS.items():
            # Pattern: find the entry by id, then within that entry's "code" string,
            # rewrite the BlackScholes.PutStrikeConvexity import to the target.
            # Simpler approach: only adjust entries whose id matches.
            # Use a regex to find the entry block.
            entry_pat = re.compile(
                r'(\{\s*"id":\s*"' + re.escape(theorem_id) + r'".*?\})',
                re.DOTALL,
            )
            def repl_entry(m):
                block = m.group(1)
                block_new = block.replace(
                    "HybridVerify.BlackScholes.PutStrikeConvexity",
                    target,
                )
                return block_new
            new_text = entry_pat.sub(repl_entry, new_text)
        if new_text != text:
            with open(path, "w") as fh:
                fh.write(new_text)
            changed += 1
    return changed


if __name__ == "__main__":
    n_lean = process_lean_files()
    n_json = process_json_files()
    print(f".lean files updated: {n_lean}")
    print(f".json files updated: {n_json}")
