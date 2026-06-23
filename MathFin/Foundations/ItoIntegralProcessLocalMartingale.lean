/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.ItoIntegralProcessMartingale
public import BrownianMotion.StochasticIntegral.LocalMartingale

/-!
# The elementary Itô integral as a continuous local martingale (Summit B / B3)

The genuinely new result here is **pathwise (sample-path) regularity** — the
first such result in the Itô tower, which so far is an `L²`/in-measure theory.
For a **continuous** Brownian motion `B` (the standard pathwise setting —
`IsPreBrownianReal` fixes only the finite-dimensional laws, and Degenne's
Kolmogorov–Chentsov machinery produces a continuous version):

* `itoSimpleProcess_pathContinuous` — for each `ω`, the path `t ↦ (V ● B)_t ω` is
  continuous. Via the explicit truncated increment-sum
  `(V ● B)_t ω = ∑_p V(p)ω·(B_{p.2∧t}ω − B_{p.1∧t}ω)` (`itoSimpleProcess_apply`),
  each summand is the continuous Brownian path `B(·)ω` composed with the
  continuous clamp `t ↦ min p.i t`, and a finite sum of continuous functions is
  continuous.

The continuity then unlocks the **localization** entry point — the bridge that
places the integral inside Degenne's local-martingale framework:

* `itoSimpleProcess_isLocalMartingale` — `(V ● B)` is a continuous **local
  martingale** (`IsLocalMartingale`). It is already a genuine `L²` martingale
  (`itoSimpleProcess_isMartingale`, B1a); with the continuous (hence càdlàg)
  paths this is exactly the hypothesis of Degenne's `Martingale.IsLocalMartingale`,
  so the integral lands in the upstream local-martingale class — the gateway
  object for the localized stochastic calculus (SDEs, Lévy's characterization,
  dynamic Girsanov).

## Coherence

Pure consumption: the martingale property is B1a, the path continuity is a
finite sum of continuous clamped Brownian increments, and the local-martingale
packaging is Degenne's sorry-free `Martingale.IsLocalMartingale`
(`Locally.of_prop` along the constant localizing sequence). Nothing is reproved.

## Scope

Honest scope: the **elementary** (simple-integrand) integral, under a continuous
Brownian motion. For these `L²`-bounded simple integrands the integral is in fact
a true martingale, so the local-martingale statement is the canonical *framing*
that connects to the localized theory; the genuinely new content here is the
pathwise continuity. The general-integrand pathwise local martingale needs a
continuous modification of the `L²` limit and remains the next gate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} [hB : IsPreBrownianReal B μ]

/-- A continuous function is càdlàg: right-continuity is `ContinuousWithinAt` on
each `Ioi`, and the left limit at `x` is `f x` (continuity gives the
`𝓝[<] x`-limit). -/
private lemma isCadlag_of_continuous {ι E : Type*} [TopologicalSpace ι] [PartialOrder ι]
    [TopologicalSpace E] {f : ι → E} (hf : Continuous f) : IsCadlag f where
  right_continuous := fun _ => hf.continuousWithinAt
  left_limit := fun x => ⟨f x, hf.continuousWithinAt.tendsto⟩

/-- **Pathwise continuity of the elementary Itô integral.** Given continuous
Brownian paths, for each `ω` the path `t ↦ (V ● B)_t ω` is continuous: it is the
finite sum `∑_p V(p)ω·(B_{p.2∧t}ω − B_{p.1∧t}ω)` (`itoSimpleProcess_apply`), each
summand the continuous path `B(·)ω` composed with the continuous clamp
`t ↦ min p.i t`. -/
theorem itoSimpleProcess_pathContinuous (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) (ω : Ω) :
    Continuous fun t : ℝ≥0 => itoSimpleProcess hBmeas V t ω := by
  simp_rw [fun t => itoSimpleProcess_apply hBmeas V t ω, Finsupp.sum]
  refine continuous_finsetSum _ fun p _ => ?_
  refine continuous_const.mul (Continuous.sub ?_ ?_)
  · exact (hBcont ω).comp (continuous_const.min continuous_id)
  · exact (hBcont ω).comp (continuous_const.min continuous_id)

/-- **The elementary Itô integral is a continuous local martingale.** Combining
B1a's martingale property (`itoSimpleProcess_isMartingale`) with the continuous
(hence càdlàg) paths gives the hypotheses of Degenne's
`Martingale.IsLocalMartingale`, so `(V ● B)` lands in the upstream
local-martingale class. -/
theorem itoSimpleProcess_isLocalMartingale (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 => B t ω)
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) :
    IsLocalMartingale (fun t ω => itoSimpleProcess hBmeas V t ω)
      (ItoIntegralL2.natFiltration hBmeas) μ :=
  Martingale.IsLocalMartingale (itoSimpleProcess_isMartingale hBmeas V)
    (fun ω => isCadlag_of_continuous (itoSimpleProcess_pathContinuous hBmeas hBcont V ω))

end ItoIntegralProcess
end MathFin
