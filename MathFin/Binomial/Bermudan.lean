/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Binomial.Model
public import MathFin.Binomial.American

/-!
# Bermudan sandwich: European ≤ Bermudan ≤ American

A Bermudan option's exercise set sits between the European (only at maturity)
and American (any time) exercise sets. As a stopping problem its value is the
maximum over admissible exercise times of the discounted exercise value, and
the maximum is monotone in the exercise set.

The clean abstract statement: for a value function `v : ι → ℝ` and exercise
sets `Eur ⊆ Berm ⊆ Amer`, `sup_Eur v ≤ sup_Berm v ≤ sup_Amer v`. We give the
discrete-time finite version using `Finset.sup'`, which is what the binomial
tree directly produces.

Results:

* `bermudan_sandwich`: `Eur ⊆ Berm ⊆ Amer ⇒ sup_Eur ≤ sup_Berm ≤ sup_Amer`
  (both inequalities, via `Finset.sup'_mono`) — the abstract optimal-stopping form.
* `bermudanPrice`: the genuine CRR-tree Bermudan price over an early-exercise step
  set `E`, interpolating `binomialPrice` (European) and `americanPrice` (American).
* `binomialPrice_le_bermudanPrice_le_americanPrice`: the sandwich as an actual
  discounted-expectation price ordering (not an abstract `sup'` over a free value).
-/

@[expose] public section

namespace MathFin

open Finset
open Classical

variable {ι : Type*} {v : ι → ℝ}

/-- **Bermudan sandwich**: `Eur ⊆ Berm ⊆ Amer` ⇒ the optimal-stopping values
are ordered `European ≤ Bermudan ≤ American` — enlarging the exercise set never
lowers the value. The financial content is the monotonicity of `Finset.sup'`
over the exercise set (`Finset.sup'_mono`); we state the full two-step ordering
directly rather than via single-`sup'_mono` wrapper lemmas. -/
lemma bermudan_sandwich
    {Eur Berm Amer : Finset ι}
    (hEB : Eur ⊆ Berm) (hBA : Berm ⊆ Amer) (hEurNE : Eur.Nonempty)
    (v : ι → ℝ) :
    Eur.sup' hEurNE v ≤ Berm.sup' (hEurNE.mono hEB) v ∧
      Berm.sup' (hEurNE.mono hEB) v ≤ Amer.sup' (hEurNE.mono (hEB.trans hBA)) v :=
  ⟨sup'_mono v hEB hEurNE,
   sup'_mono v hBA (hEurNE.mono hEB)⟩

/-! ## The genuine price-tree Bermudan sandwich

`bermudan_sandwich` above is the abstract optimal-stopping monotonicity on a free
value function. Here is the honest CRR-tree instance: a `bermudanPrice` recursion
interpolating the European (`binomialPrice`) and American (`americanPrice`) Bellman
recursions over an admissible early-exercise step set `E ⊆ ℕ`, with the sandwich as
a genuine price ordering. -/

/-- **Bermudan option price** on the CRR tree with early-exercise steps `E ⊆ ℕ`
(steps-remaining at which early exercise is allowed): the Bellman recursion takes
`max(intrinsic, continuation)` exactly at steps in `E`, the bare discounted
continuation otherwise. `E = ∅` is the European price, `E = univ` the American. -/
noncomputable def bermudanPrice (E : Set ℕ) (u d r : ℝ) (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, S => g S
  | n + 1, S =>
      if (n + 1) ∈ E then
        max (g S) (binomialOptionPriceOnePeriod u d r
          (bermudanPrice E u d r g n (S * u)) (bermudanPrice E u d r g n (S * d)))
      else
        binomialOptionPriceOnePeriod u d r
          (bermudanPrice E u d r g n (S * u)) (bermudanPrice E u d r g n (S * d))

@[simp] lemma bermudanPrice_zero (E : Set ℕ) (u d r : ℝ) (g : ℝ → ℝ) (S : ℝ) :
    bermudanPrice E u d r g 0 S = g S := rfl

lemma bermudanPrice_succ (E : Set ℕ) (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    bermudanPrice E u d r g (n + 1) S =
      if (n + 1) ∈ E then
        max (g S) (binomialOptionPriceOnePeriod u d r
          (bermudanPrice E u d r g n (S * u)) (bermudanPrice E u d r g n (S * d)))
      else
        binomialOptionPriceOnePeriod u d r
          (bermudanPrice E u d r g n (S * u)) (bermudanPrice E u d r g n (S * d)) := rfl

/-- `bermudanPrice ∅ = binomialPrice`: never exercising early is the European price. -/
lemma bermudanPrice_empty (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    bermudanPrice ∅ u d r g n S = binomialPrice u d r g n S := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    rw [bermudanPrice_succ, if_neg (by simp), ih (S * u), ih (S * d),
        ← binomialPrice_succ_eq_onePeriod]

/-- `bermudanPrice univ = americanPrice`: always allowing exercise is the American price. -/
lemma bermudanPrice_univ (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    bermudanPrice Set.univ u d r g n S = americanPrice u d r g n S := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    rw [bermudanPrice_succ, if_pos (Set.mem_univ _), ih (S * u), ih (S * d),
        ← americanPrice_succ]

/-- **Monotone in the exercise set**: enlarging the admissible early-exercise set
never lowers the price (`BinomialNoArb` makes the continuation monotone). -/
lemma bermudanPrice_mono {u d r : ℝ} (h : BinomialNoArb u d r) (g : ℝ → ℝ)
    {E₁ E₂ : Set ℕ} (hE : E₁ ⊆ E₂) (n : ℕ) (S : ℝ) :
    bermudanPrice E₁ u d r g n S ≤ bermudanPrice E₂ u d r g n S := by
  induction n generalizing S with
  | zero => simp
  | succ n ih =>
    have hcont := binomialOptionPriceOnePeriod_mono h (ih (S * u)) (ih (S * d))
    rw [bermudanPrice_succ, bermudanPrice_succ]
    by_cases h1 : (n + 1) ∈ E₁
    · rw [if_pos h1, if_pos (hE h1)]; exact max_le_max le_rfl hcont
    · rw [if_neg h1]
      by_cases h2 : (n + 1) ∈ E₂
      · rw [if_pos h2]; exact le_trans hcont (le_max_right _ _)
      · rw [if_neg h2]; exact hcont

/-- **Bermudan sandwich (genuine price-tree form)**: `European ≤ Bermudan ≤
American` for any admissible early-exercise set `E`, at every step and spot —
the three legs are the actual discounted-expectation CRR recursions, not an
abstract `Finset.sup'` over a free value function. -/
theorem binomialPrice_le_bermudanPrice_le_americanPrice {u d r : ℝ}
    (h : BinomialNoArb u d r) (g : ℝ → ℝ) (E : Set ℕ) (n : ℕ) (S : ℝ) :
    binomialPrice u d r g n S ≤ bermudanPrice E u d r g n S ∧
      bermudanPrice E u d r g n S ≤ americanPrice u d r g n S :=
  ⟨(bermudanPrice_empty u d r g n S) ▸ bermudanPrice_mono h g (Set.empty_subset E) n S,
   (bermudanPrice_univ u d r g n S) ▸ bermudanPrice_mono h g (Set.subset_univ E) n S⟩

end MathFin
