/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.PoissonCompensatedIsometryAdapted

/-!
# The compensated Poisson random measure is an orthogonal martingale measure

The diagonal second moment `𝔼[Ñ(B)²] = ν̂(B)` (`compensated_integral_sq`) is the `C = D` case of the
full **covariance** of the compensated Poisson random measure:

  `𝔼[Ñ(C)·Ñ(D)] = ν̂(C ∩ D)`   for measurable finite-intensity `C, D`.

`Ñ` is thus an *orthogonal martingale measure* with (deterministic) intensity `ν̂`: increments on
disjoint regions are uncorrelated, and the covariance of general increments is the intensity of their
overlap. The proof decomposes `C = (C∩D) ⊔ (C\D)` and `D = (C∩D) ⊔ (D\C)` into three disjoint pieces
whose counts are independent (the independent-scattering field `indep_of_disjoint_region`); the three
disjoint cross-pairs vanish (`integral_mul_compensated_eq_zero`) and the diagonal `𝔼[Ñ(C∩D)²]` is
`ν̂(C∩D)`.

This covariance is the bilinear core the compensated-integral isometry is built on (the jump analogue
of `WienerIntegralL2.covariance_increment_aux`), and the first rung of the Itô–Lévy integral
*operator* (the CLM over the characterised predictable `L²`).

## Provenance

Built on our own `PoissonRandomMeasure` / `PoissonCompensatedIsometryAdapted` (PRM field shape
consulted from `cgarryZA/LevyStochCalc`, Apache-2.0, cited — a rendering of Applebaum 2009 Def.
2.3.1; the proofs are ours). Reference: Applebaum, *Lévy Processes and Stochastic Calculus*, CUP
2009, Thm 4.2.3.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- **Counts are a.e. finite** on finite-intensity sets: `N(·, B)` has law `Poisson(ν̂ B)`, which is
supported on `ℕ ⊂ ℝ≥0∞`, so `⊤` is a null value. -/
theorem ae_count_ne_top (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    ∀ᵐ ω ∂P, N.N ω B ≠ ⊤ := by
  rw [ae_iff]
  have hset : {ω | ¬ N.N ω B ≠ ⊤} = (fun ω => N.N ω B) ⁻¹' {⊤} := by
    ext ω; simp [Set.mem_preimage]
  rw [hset, ← Measure.map_apply (N.measurable_eval hB) (measurableSet_singleton ⊤),
    N.poisson_law hB hfin]
  show poissonMeasureENN (referenceIntensity ν B).toNNReal {⊤} = 0
  unfold poissonMeasureENN
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton ⊤),
    show (fun n : ℕ => (n : ℝ≥0∞)) ⁻¹' {(⊤ : ℝ≥0∞)} = ∅ from by
      ext n
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact ENNReal.natCast_ne_top n]
  exact measure_empty

/-- **Additivity of the compensated increment** on disjoint finite-intensity sets:
`Ñ(X ∪ Y) = Ñ(X) + Ñ(Y)` a.e. (count additivity + a.e. finiteness). -/
theorem compensated_add_of_disjoint (N : PoissonRandomMeasure P ν) {X Y : Set (ℝ × E)}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hdisj : Disjoint X Y)
    (hXfin : referenceIntensity ν X ≠ ⊤) (hYfin : referenceIntensity ν Y ≠ ⊤) :
    ∀ᵐ ω ∂P, N.compensated (X ∪ Y) ω = N.compensated X ω + N.compensated Y ω := by
  filter_upwards [ae_count_ne_top N hX hXfin, ae_count_ne_top N hY hYfin] with ω hXω hYω
  simp only [PoissonRandomMeasure.compensated]
  rw [measure_union hdisj hY, ENNReal.toReal_add hXω hYω,
    show referenceIntensity ν (X ∪ Y) = referenceIntensity ν X + referenceIntensity ν Y from
      measure_union hdisj hY, ENNReal.toReal_add hXfin hYfin]
  ring

/-- **Uncorrelated on disjoint regions**: `𝔼[Ñ(X)·Ñ(Y)] = 0` for disjoint measurable `X, Y` (finite
`Y`). `Ñ(X)` lives on the region disjoint from `Y`, so `Ñ(X) ⟂ Ñ(Y)`; `Ñ(Y)` is mean-zero. -/
theorem compensated_mul_compensated_disjoint (N : PoissonRandomMeasure P ν) {X Y : Set (ℝ × E)}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hdisj : Disjoint X Y)
    (hYfin : referenceIntensity ν Y ≠ ⊤) :
    ∫ ω, N.compensated X ω * N.compensated Y ω ∂P = 0 := by
  refine integral_mul_compensated_eq_zero N hY hYfin ?_
  show Measurable[N.regionSigma Y] fun ω => (N.N ω X).toReal - (referenceIntensity ν X).toReal
  have hc : Measurable[N.regionSigma Y] fun ω => N.N ω X :=
    (measurable_iff_comap_le.mpr le_rfl).mono (le_iSup₂_of_le X ⟨hdisj, hX⟩ le_rfl) le_rfl
  exact hc.ennreal_toReal.sub measurable_const

/-- **The covariance of the compensated Poisson random measure**: `𝔼[Ñ(C)·Ñ(D)] = ν̂(C ∩ D)`. `Ñ` is
an orthogonal martingale measure with intensity `ν̂`. Decompose into the three disjoint pieces
`C∩D`, `C\D`, `D\C`; the three cross-pairs vanish and the diagonal `𝔼[Ñ(C∩D)²]` is `ν̂(C∩D)`. -/
theorem compensated_covariance (N : PoissonRandomMeasure P ν) {C D : Set (ℝ × E)}
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCfin : referenceIntensity ν C ≠ ⊤) (hDfin : referenceIntensity ν D ≠ ⊤) :
    ∫ ω, N.compensated C ω * N.compensated D ω ∂P = (referenceIntensity ν (C ∩ D)).toReal := by
  have hIms : MeasurableSet (C ∩ D) := hC.inter hD
  have hC'ms : MeasurableSet (C \ D) := hC.diff hD
  have hD'ms : MeasurableSet (D \ C) := hD.diff hC
  have hIfin : referenceIntensity ν (C ∩ D) ≠ ⊤ :=
    ne_top_of_le_ne_top hCfin (measure_mono Set.inter_subset_left)
  have hC'fin : referenceIntensity ν (C \ D) ≠ ⊤ :=
    ne_top_of_le_ne_top hCfin (measure_mono Set.sdiff_subset)
  have hD'fin : referenceIntensity ν (D \ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hDfin (measure_mono Set.sdiff_subset)
  have hIC' : Disjoint (C ∩ D) (C \ D) := Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.2 hx1.2
  have hID' : Disjoint (C ∩ D) (D \ C) := Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.2 hx1.1
  have hC'D' : Disjoint (C \ D) (D \ C) := Set.disjoint_left.mpr fun _ hx1 hx2 => hx2.2 hx1.1
  -- a.e. decompositions of the two increments
  have hdC : ∀ᵐ ω ∂P, N.compensated C ω
      = N.compensated (C ∩ D) ω + N.compensated (C \ D) ω := by
    have h := compensated_add_of_disjoint N hIms hC'ms hIC' hIfin hC'fin
    rwa [Set.inter_union_sdiff] at h
  have hdD : ∀ᵐ ω ∂P, N.compensated D ω
      = N.compensated (C ∩ D) ω + N.compensated (D \ C) ω := by
    have h := compensated_add_of_disjoint N hIms hD'ms hID' hIfin hD'fin
    rwa [show (C ∩ D) ∪ (D \ C) = D from by rw [Set.inter_comm]; exact Set.inter_union_sdiff D C] at h
  -- L² membership ⇒ integrability of every cross product
  have hL2 : ∀ {S : Set (ℝ × E)}, MeasurableSet S → referenceIntensity ν S ≠ ⊤ →
      MemLp (N.compensated S) 2 P := fun hS hSf => memLp_compensated N hS hSf
  -- expand the product into the four pieces
  have hprod : ∀ᵐ ω ∂P, N.compensated C ω * N.compensated D ω
      = (N.compensated (C ∩ D) ω) ^ 2
        + N.compensated (C ∩ D) ω * N.compensated (D \ C) ω
        + N.compensated (C \ D) ω * N.compensated (C ∩ D) ω
        + N.compensated (C \ D) ω * N.compensated (D \ C) ω := by
    filter_upwards [hdC, hdD] with ω hCω hDω
    rw [hCω, hDω]; ring
  rw [integral_congr_ae hprod]
  have hi1 : Integrable (fun ω => (N.compensated (C ∩ D) ω) ^ 2) P :=
    (hL2 hIms hIfin).integrable_sq
  have hi2 : Integrable (fun ω => N.compensated (C ∩ D) ω * N.compensated (D \ C) ω) P :=
    (hL2 hIms hIfin).integrable_mul (hL2 hD'ms hD'fin)
  have hi3 : Integrable (fun ω => N.compensated (C \ D) ω * N.compensated (C ∩ D) ω) P :=
    (hL2 hC'ms hC'fin).integrable_mul (hL2 hIms hIfin)
  have hi4 : Integrable (fun ω => N.compensated (C \ D) ω * N.compensated (D \ C) ω) P :=
    (hL2 hC'ms hC'fin).integrable_mul (hL2 hD'ms hD'fin)
  have hf12 : Integrable (fun ω => (N.compensated (C ∩ D) ω) ^ 2
      + N.compensated (C ∩ D) ω * N.compensated (D \ C) ω) P := hi1.add hi2
  have hf123 : Integrable (fun ω => (N.compensated (C ∩ D) ω) ^ 2
      + N.compensated (C ∩ D) ω * N.compensated (D \ C) ω
      + N.compensated (C \ D) ω * N.compensated (C ∩ D) ω) P := hf12.add hi3
  rw [integral_add hf123 hi4, integral_add hf12 hi3,
    integral_add hi1 hi2, compensated_integral_sq N hIms hIfin,
    compensated_mul_compensated_disjoint N hIms hD'ms hID' hD'fin,
    compensated_mul_compensated_disjoint N hC'ms hIms hIC'.symm hIfin,
    compensated_mul_compensated_disjoint N hC'ms hD'ms hC'D' hD'fin]
  ring

end MathFin
