/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import QuantFin.Foundations.ItoIntegralL2

/-! # The Itô integral as a process `t ↦ (V ● B)_t`, with genuine `L²` content

The elementary Itô integral of a simple process `V`, viewed as a **process**
indexed by finite time `t : ℝ≥0` — the value of `∫₀ᵗ V dB` truncated at `t`.
Built on Degenne's `SimpleProcess.integral` at the finite (deterministic)
stopping time `(t : WithTop ℝ≥0)`, so it is coherent with the upstream
elementary-integral algebra (linearity is inherited for free).

Unlike a bare scaffold, this file proves the **genuine analytic content** the
process layer rests on:

* `itoSimpleProcess_apply` — the explicit truncated increment-sum
  `(V ● B)_t ω = ∑_p V(p)(ω)·(B_{p.2∧t}(ω) − B_{p.1∧t}(ω))` (the deterministic
  stopped process at `t` collapses to `B(· ∧ t)`).
* `memLp_itoSimpleProcess` — `(V ● B)_t ∈ L²(μ)` at **every** time `t`. This is
  the real work: each summand is, after truncation, either `0` (interval past
  `t`) or an adapted coefficient times a Brownian increment (`p.1 ≤ t`), so the
  adapted-increment `L²` lemma applies; the finite sum is `L²`. (Same engine as
  `ItoIntegralL2.memLp_itoSimple`, with the truncation case-split.)
* `itoSimpleProcessLp` — its `Lp ℝ 2 μ` class.
* `itoSimpleProcess_eq_itoSimple` — at any `t` past all interval right
  endpoints, the process equals the **terminal** `ItoIntegralL2.itoSimple V`,
  i.e. the object the continuous Itô CLM (`ItoIntegralCLM`) extends. This is the
  bridge tying the process view to the L²/CLM foundation.
* `itoSimpleProcess_zero_time` — `(V ● B)_0 = 0` (every increment collapses).
* `V`-linearity (`add`/`smul`/`neg`), inherited from `SimpleProcess.integral`.

What is still deferred (the *next* layer, which will consume this one):
adaptedness of `t ↦ (V●B)_t` to `𝓕_t`, pathwise continuity, the martingale
property, and the time-indexed Itô isometry. Those are genuine follow-ups built
on `memLp_itoSimpleProcess` here. -/

namespace QuantFin
namespace ItoIntegralProcess

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- **Process-level elementary Itô integral** of a simple `V` against Brownian
motion `B`, at finite time `t`. Degenne's `SimpleProcess.integral` against
multiplication, evaluated at the deterministic stopping time `(t : WithTop ℝ≥0)`. -/
noncomputable def itoSimpleProcess (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas))
    (t : ℝ≥0) : Ω → ℝ :=
  SimpleProcess.integral (ContinuousLinearMap.mul ℝ ℝ) V B (t : WithTop ℝ≥0)

/-- The deterministic stopped process at a constant time `u` collapses to
`B (· ∧ u)`: `stoppedProcess B (fun _ ↦ ↑u) s = B (min s u)` (the `WithTop`
`min`/`untopA` coercions). -/
private lemma stoppedProcess_const_coe (u s : ℝ≥0) (ω : Ω) :
    stoppedProcess B (fun _ : Ω => (u : WithTop ℝ≥0)) s ω = B (min s u) ω := by
  show B (min (s : WithTop ℝ≥0) (u : WithTop ℝ≥0)).untopA ω = B (min s u) ω
  rw [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]

/-- **Explicit truncated increment-sum**:
`(V ● B)_t ω = ∑_p V(p)(ω)·(B_{p.2∧t}(ω) − B_{p.1∧t}(ω))`. -/
lemma itoSimpleProcess_apply (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas))
    (t : ℝ≥0) (ω : Ω) :
    itoSimpleProcess hBmeas V t ω
      = V.value.sum fun p v => v ω * (B (min p.2 t) ω - B (min p.1 t) ω) := by
  simp only [itoSimpleProcess, SimpleProcess.integral, ContinuousLinearMap.mul_apply']
  refine Finsupp.sum_congr fun p _ => ?_
  rw [stoppedProcess_const_coe, stoppedProcess_const_coe]

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

/-- The elementary process Itô integral on `-V` flips sign. -/
lemma itoSimpleProcess_neg (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) (t : ℝ≥0) :
    itoSimpleProcess hBmeas (-V) t = -itoSimpleProcess hBmeas V t := by
  funext ω
  simp only [itoSimpleProcess, SimpleProcess.integral_neg_left, Pi.neg_apply]

/-- **At `t = 0`**, the process is `0`: every increment `B_{p.i∧0} = B_0`
collapses, so each term `V(p)·(B_0 − B_0) = 0`. -/
@[simp] lemma itoSimpleProcess_zero_time (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas)) :
    itoSimpleProcess hBmeas V 0 = 0 := by
  funext ω
  rw [itoSimpleProcess_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  have e1 : min p.1 (0 : ℝ≥0) = 0 := min_eq_right zero_le
  have e2 : min p.2 (0 : ℝ≥0) = 0 := min_eq_right zero_le
  rw [e1, e2, sub_self, mul_zero]

/-- **Terminal agreement with the CLM base object.** At any `t` past all
interval right endpoints, the process equals the terminal Itô integral
`ItoIntegralL2.itoSimple V` (which the continuous Itô CLM extends). -/
lemma itoSimpleProcess_eq_itoSimple (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas))
    {t : ℝ≥0} (ht : ∀ p ∈ V.value.support, p.2 ≤ t) :
    itoSimpleProcess hBmeas V t = ItoIntegralL2.itoSimple hBmeas V := by
  funext ω
  rw [itoSimpleProcess_apply, ItoIntegralL2.itoSimple_apply]
  refine Finsupp.sum_congr fun p hp => ?_
  have h2 : min p.2 t = p.2 := min_eq_left (ht p hp)
  have h1 : min p.1 t = p.1 := min_eq_left ((V.le_of_mem_support_value p hp).trans (ht p hp))
  rw [h1, h2]

variable [hB : IsPreBrownian B μ]

/-- **`L²` membership at every time `t`** — the genuine analytic content. After
truncation each summand is `0` (interval past `t`) or an adapted coefficient
times a Brownian increment (`p.1 ≤ t`); the finite sum is `L²(μ)`. -/
theorem memLp_itoSimpleProcess (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas))
    (t : ℝ≥0) :
    MemLp (itoSimpleProcess hBmeas V t) 2 μ := by
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rw [show itoSimpleProcess hBmeas V t
        = fun ω => ∑ p ∈ V.value.support, V.value p ω * (B (min p.2 t) ω - B (min p.1 t) ω)
      from funext fun ω => by rw [itoSimpleProcess_apply]; rfl]
  refine memLp_finsetSum _ fun p hp => ?_
  by_cases ht : p.1 ≤ t
  · -- active interval: adapted coefficient × increment over `[p.1, p.2 ∧ t]`
    rw [min_eq_left ht]
    refine ItoIsometryAdapted.memLp_adapted_mul_increment hBmeas
      (le_min (V.le_of_mem_support_value p hp) ht)
      (ItoIntegralL2.adaptedAt_of_measurable_natural hBmeas (V.measurable_value p)) ?_
    exact MemLp.of_bound
      ((V.measurable_value p).mono ((ItoIntegralL2.natFiltration hBmeas).le p.1) le_rfl).aestronglyMeasurable
      V.valueBound (ae_of_all _ (V.value_le_valueBound p))
  · -- interval entirely past `t`: both endpoints truncate to `t`, term is `0`
    push Not at ht
    have h1 : min p.1 t = t := min_eq_right ht.le
    have h2 : min p.2 t = t := min_eq_right (ht.le.trans (V.le_of_mem_support_value p hp))
    simp only [h1, h2, sub_self, mul_zero]
    exact memLp_const 0

/-- The process Itô integral at time `t` as an element of `Lp ℝ 2 μ`. -/
noncomputable def itoSimpleProcessLp (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas))
    (t : ℝ≥0) : Lp ℝ 2 μ :=
  (memLp_itoSimpleProcess hBmeas V t).toLp _

end ItoIntegralProcess
end QuantFin
