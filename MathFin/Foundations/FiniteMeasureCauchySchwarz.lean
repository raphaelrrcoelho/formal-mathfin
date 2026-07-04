/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-! # Cauchy–Schwarz on a finite measure

The elementary `L²` inequality `(∫ f)² ≤ ν(univ)·∫ f²` for a finite measure `ν`, from Hölder at
exponents `2,2` against the constant `1`. Mathlib has no lemma of this exact shape (its `L²`
Cauchy–Schwarz is inner-product-space-valued; Jensen `ConvexOn.map_integral_le` gives only the
probability-measure `ν(univ)=1` case), so it is assembled once here on top of the right Mathlib
primitive `integral_mul_le_Lp_mul_Lq_of_nonneg`.

Consumed by the drift `L²` energy bound (`DriftProcessPredictable`, at `ν = timeMeasure.restrict`)
and by the SDE-uniqueness drift Cauchy–Schwarz (`SDEUniqueness`, at `ν = volume.restrict (Ioc 0 s)`)
— one proof, two interval specializations.
-/

@[expose] public section

open MeasureTheory

namespace MathFin

/-- **Cauchy–Schwarz on a finite measure**: `(∫ f)² ≤ ν(univ)·∫ f²`, via Hölder with `g ≡ 1` at
exponents `2,2`. -/
theorem sq_integral_le_measureReal_mul {α : Type*} {m : MeasurableSpace α} {ν : Measure α}
    [IsFiniteMeasure ν] {f : α → ℝ} (hf : MemLp f 2 ν) :
    (∫ a, f a ∂ν) ^ 2 ≤ (ν Set.univ).toReal * ∫ a, (f a) ^ 2 ∂ν := by
  have hp : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hint_nonneg : 0 ≤ ∫ a, (f a) ^ 2 ∂ν := integral_nonneg fun a => sq_nonneg _
  have hmeas_nonneg : 0 ≤ (ν Set.univ).toReal := ENNReal.toReal_nonneg
  have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ν) hp
    (f := |f|) (g := fun _ => (1 : ℝ))
    (ae_of_all ν fun a => abs_nonneg (f a)) (ae_of_all ν fun _ => zero_le_one)
    (by simpa [ENNReal.ofReal_ofNat] using hf.abs)
    (by simpa [ENNReal.ofReal_ofNat] using memLp_const (1 : ℝ))
  have hpow : ∫ a, |f| a ^ (2 : ℝ) ∂ν = ∫ a, (f a) ^ 2 ∂ν := by
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    show |f a| ^ (2 : ℝ) = (f a) ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [hpow, Real.one_rpow, MeasureTheory.integral_const, smul_eq_mul, mul_one, measureReal_def]
    at hhold
  have habs : |∫ a, f a ∂ν|
      ≤ (∫ a, (f a) ^ 2 ∂ν) ^ (1 / 2 : ℝ) * (ν Set.univ).toReal ^ (1 / 2 : ℝ) := by
    refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
    simpa only [Pi.abs_apply, mul_one] using hhold
  calc (∫ a, f a ∂ν) ^ 2 = |∫ a, f a ∂ν| ^ 2 := (sq_abs _).symm
    _ ≤ ((∫ a, (f a) ^ 2 ∂ν) ^ (1 / 2 : ℝ) * (ν Set.univ).toReal ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = (ν Set.univ).toReal * ∫ a, (f a) ^ 2 ∂ν := by
        rw [mul_pow, ← Real.rpow_natCast ((∫ a, (f a) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) 2,
          ← Real.rpow_natCast ((ν Set.univ).toReal ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hint_nonneg,
          ← Real.rpow_mul hmeas_nonneg]
        norm_num
        ring

end MathFin
