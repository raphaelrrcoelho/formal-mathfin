/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.Foundations.ItoIntegralL2

/-! # The Itô integral as a process `t ↦ (V ● B)_t`

The terminal-time Itô integral (`ItoIntegralL2.itoSimple = (V ● B)_⊤`) lifted
to a **process** indexed by finite time `t : ℝ≥0`. At each `t`,

  `(V ● B)_t ω = ∑_p V(p)(ω) · (B_{p.2 ∧ t}(ω) − B_{p.1 ∧ t}(ω))`,

so intervals `(p.1, p.2]` past `t` are truncated to their `t`-prefix, and
intervals starting after `t` contribute zero.

**STATUS — staging only, no current consumer.** This file is a structural
scaffold: a single `noncomputable def` fixing the multiplication-CLM and the
finite-time `(t : WithTop ℝ≥0)` projection of upstream `SimpleProcess.integral`,
plus its `V`-linearity lemmas. All substantive analytic content — `L²` at each
`t`, adaptedness to `𝓕_t`, pathwise continuity, the martingale property, the
time-indexed Itô isometry — is **deferred**.

Honesty note (portfolio review 2026-05-29): nothing in the library currently
consumes `itoSimpleProcess`. The L²-Itô-squared formula
(`ItoFormulaSquaredL2`) is built on the *partition / quadratic-variation*
track (`QuadraticVariationL2.tendsto_qv`), **not** on this process-form
integral. Per the project's own rule — "Foundations machinery becomes
load-bearing only when downstream modules can consume it"
(`docs/architecture.md`) — this file is *premature* until the continuous
Itô-integral-as-process is built against the CLM (`ItoIntegralCLM`) with real
analytic content. It is retained as a deliberate landing-pad for that work;
if the next continuation builds the process integral directly against the CLM
instead, this scaffold should be deleted rather than grown.
-/

namespace QuantFin
namespace ItoIntegralProcess

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- **Process-level Itô integral** of a simple `V` against Brownian motion `B`,
indexed by finite time `t : ℝ≥0`. Built on Degenne's `SimpleProcess.integral`
at the finite stopping time `(t : WithTop ℝ≥0)`. -/
noncomputable def itoSimpleProcess (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas))
    (t : ℝ≥0) : Ω → ℝ :=
  SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ) V B (t : WithTop ℝ≥0)

/-- The elementary process Itô integral is **additive** in the simple process. -/
lemma itoSimpleProcess_add (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas))
    (t : ℝ≥0) :
    itoSimpleProcess hBmeas (V + W) t = itoSimpleProcess hBmeas V t
      + itoSimpleProcess hBmeas W t := by
  funext ω
  simp only [itoSimpleProcess, SimpleProcess.integral_add_left, Pi.add_apply]

/-- The elementary process Itô integral is **homogeneous** in the simple process. -/
lemma itoSimpleProcess_smul (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) (t : ℝ≥0) :
    itoSimpleProcess hBmeas (c • V) t = c • itoSimpleProcess hBmeas V t := by
  funext ω
  simp only [itoSimpleProcess, SimpleProcess.integral_smul_left, Pi.smul_apply]

/-- The elementary process Itô integral on the **zero** simple process is `0`. -/
@[simp] lemma itoSimpleProcess_zero_input (hBmeas : ∀ t, Measurable (B t))
    (t : ℝ≥0) :
    itoSimpleProcess (B := B) hBmeas
      (0 : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) t = 0 := by
  funext ω
  simp [itoSimpleProcess, SimpleProcess.integral_zero_left]

/-- The elementary process Itô integral on `-V` flips sign. -/
lemma itoSimpleProcess_neg (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas))
    (t : ℝ≥0) :
    itoSimpleProcess hBmeas (-V) t = -itoSimpleProcess hBmeas V t := by
  funext ω
  simp only [itoSimpleProcess, SimpleProcess.integral_neg_left, Pi.neg_apply]

/-- **At time `⊤`**, the process recovers the terminal-time Itô integral
`itoSimple V` (definitional unfolding of `SimpleProcess.integral`). -/
@[simp] lemma itoSimpleProcess_top (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) :
    SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ) V B ⊤
      = ItoIntegralL2.itoSimple hBmeas V := rfl

end ItoIntegralProcess
end QuantFin
