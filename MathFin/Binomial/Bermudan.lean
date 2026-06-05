/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

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
  (both inequalities, via `Finset.sup'_mono`).
-/

@[expose] public section

namespace MathFin

open Finset

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

end MathFin
