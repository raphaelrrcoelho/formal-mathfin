/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import QuantFin.RiskMeasures.Gaussian

/-!
# Gaussian CVaR additive decomposition (the Rockafellar-Uryasev *form*)

**Scope (honest).** This file formalizes ONLY the *algebraic* additive
decomposition of the gaussian closed-form CVaR

  `CVaR_α = VaR_α + (σ / (1−α)) · ϕ(z)`,

written in the additive shape `VaR + (1/(1−α)) · tail-term`. It does **not**
formalize the Rockafellar-Uryasev *variational theorem*

  `CVaR_α(L) = inf_{c} {c + (1/(1−α)) · E[(L − c)⁺]}, attained at c* = VaR_α`,

which is the deep content of R-U (no `inf`, no `E[(L−c)⁺]`, no minimization is
proved here). The variational form is given as background motivation only; what
is machine-checked is the gaussian additive identity, equivalent to (a
rearrangement of) `RiskMeasures.Gaussian.gaussianCVaR_sub_VaR`.

Result:

* `gaussianCVaR_eq_VaR_plus_tail_term`: `CVaR = VaR + σ·(ϕ(z)/(1−α) − z)`, the
  additive (R-U-shaped) decomposition of the gaussian CVaR closed form.
-/

namespace QuantFin

open ProbabilityTheory Real

/-- **Gaussian CVaR additive decomposition** (the Rockafellar-Uryasev *shape*,
not the variational theorem — see module header). Rearranging the gaussian
closed forms,

`CVaR_α = VaR_α + (σ / (1 − α)) · [ϕ(z) − z · (1 − α)]
       = VaR_α + σ · [ϕ(z)/(1 − α) − z]`.

Pure algebraic rearrangement (`ring`) of the definitions `gaussianCVaR` and
`gaussianVaR` — the same content as `gaussianCVaR_sub_VaR`, in additive form.
It does not establish the R-U infimum characterization. -/
lemma gaussianCVaR_eq_VaR_plus_tail_term (μ σ z α : ℝ) :
    gaussianCVaR μ σ z α =
      gaussianVaR μ σ z +
        σ * (gaussianPDFReal 0 1 z / (1 - α) - z) := by
  unfold gaussianCVaR gaussianVaR
  ring

end QuantFin
