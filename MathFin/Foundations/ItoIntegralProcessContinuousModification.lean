/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralProcessGeneral
public import MathFin.Foundations.ItoIntegralProcessLocalMartingale
public import BrownianMotion.StochasticIntegral.DoobLp

/-!
# Continuous modification of the general-integrand Itô process (the gate)

The first pathwise-regularity result for the **general** integrand: a continuous
modification of the `L²`-valued process `t ↦ itoProcessCLM T t φ` on a finite
horizon `[0,T]`, packaged as a continuous (hence local) martingale.

B1b (`ItoIntegralProcessGeneral`) built the general-integrand Itô integral as an
`Lp ℝ 2 μ`-valued process — adapted, an `L²` martingale, `L²`-continuous in `t`,
but with no honest sample paths. B3 (`ItoIntegralProcessLocalMartingale`) gave
pathwise continuity only for the **simple** integrand. This file closes the gap:
approximate `φ` by simple processes `Vₙ` (density, B1b); each `Vₙ ● B` has
continuous paths (B3); Degenne's continuous-time weak-type maximal inequality
(`maximal_ineq_norm`) + Borel–Cantelli on a fast subsequence make `(Vₙ ● B)`
a.s.-uniformly Cauchy on `[0,T]`, so the uniform limit is pathwise continuous,
equals `(φ ● B)_t` a.e. at every `t` (a **modification**), and is a continuous
`L²` martingale — hence an `IsLocalMartingale`, the localization gateway.

## Coherence

Pure consumption + assembly. Degenne's general càdlàg modification
(`exists_modification_isCadlag`) is `sorry`-backed, so this result is not a
duplicate; and the `L²`-continuity + Doob route yields a genuinely **continuous**
(not merely càdlàg) version. Nothing of the isometry, density, or martingale
property is reproved — the maximal inequality is Degenne's, the continuous
approximants are B3's, the density is B1b's.

See `docs/superpowers/specs/2026-06-26-ito-continuous-modification-design.md`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcessContinuousModification

open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-! ## Phase 1 — the maximal estimate -/

/-- **Continuous-time weak-type maximal bound** for the elementary Itô integral.
The process `t ↦ (V ● B)_t` is a continuous `L²` martingale (B1a's martingale
property + B3's path continuity), so Degenne's continuous-time maximal inequality
`maximal_ineq_norm` applies directly at `n := T`, where `⨆ i : Set.Iic T` is the
running supremum over the whole interval `[0,T]`. -/
theorem itoSimpleProcess_maximal_weak (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (T : ℝ≥0) (ε : ℝ) :
    ε • μ.real {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V i ω‖}
      ≤ ∫ ω in {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V i ω‖},
          ‖itoSimpleProcess hBmeas V T ω‖ ∂μ :=
  maximal_ineq_norm (itoSimpleProcess_isMartingale hB hBmeas V) ε T
    (fun ω _ => (itoSimpleProcess_pathContinuous hBmeas hBcont V ω).continuousWithinAt)

end ItoIntegralProcessContinuousModification
end MathFin
