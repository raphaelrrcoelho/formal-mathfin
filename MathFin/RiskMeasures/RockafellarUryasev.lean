/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.RiskMeasures.Gaussian
public import MathFin.Foundations.StandardNormal
public import MathFin.BlackScholes.Bachelier

/-!
# The Rockafellar–Uryasev variational characterization of Gaussian CVaR

For a Gaussian loss `L = μ + σ·Z`, `Z ~ N(0,1)`, the Rockafellar–Uryasev (2000)
theorem characterizes CVaR as the *minimum* of the one-parameter objective

  `g(c) = c + E[(L − c)⁺] / (1 − α)`,

attained at `c = VaR_α(L)`. This file proves the full variational statement
(`gaussianCVaR_isLeast_ruObjective`) for the quantile-parametrized Gaussian
closed forms of `RiskMeasures/Gaussian.lean` (`z` with `Φ(z) = α`; the repo
carries no `Φ⁻¹` API because Mathlib has none at the pin). The file previously
recorded only the algebraic additive decomposition
(`gaussianCVaR_eq_VaR_plus_tail_term`, kept below) and explicitly deferred the
variational theorem; that debt is now discharged.

The minimality proof is the *pointwise certificate* argument, not calculus:
for every threshold `c`,

  `(L − c)⁺ ≥ (L − c) · 𝟙_{Z > z}`   pointwise,

and integrating against the Gaussian density turns the right side into
`(μ − c)(1 − α) + σ·ϕ(z)`, whence `g(c) ≥ μ + σ·ϕ(z)/(1−α) = CVaR_α`. At
`c = VaR_α` the certificate is *exact* — the positive part vanishes precisely
off the tail event — which is **why** the R-U minimum is attained at VaR: the
`α`-tail event itself certifies optimality.

The expected-shortfall integral is computed from two standard-normal
primitives: the truncated first moment `∫_{Ioi a} x·ϕ(x) dx = ϕ(a)`
(`Bachelier.lean`; a standard-normal fact that could hoist to
`Foundations/StandardNormal` in a future de-inversion pass) and the Gaussian
tail mass `∫_{Ioi a} ϕ(x) dx = 1 − Φ(a)` (derived below from
`gaussianReal_Ioi_toReal`).

## Results

* `integral_gaussianPDFReal_Ioi`: tail mass `∫_{Ioi a} ϕ = 1 − Φ(a)`.
* `integral_max_sub_mul_gaussianPDFReal`: standard-normal expected shortfall
  `E[(Z − z)⁺] = ϕ(z) − z(1 − Φ(z))`.
* `integral_shortfall_gaussian`: affine-loss expected shortfall closed form.
* `ruObjective_at_gaussianVaR`: `g(VaR_α) = CVaR_α` (the minimum value).
* `gaussianCVaR_le_ruObjective`: `g(c) ≥ CVaR_α` for every `c` (minimality).
* `gaussianCVaR_isLeast_ruObjective`: the packaged R-U theorem —
  `CVaR_α = min_c g(c)`, attained at `VaR_α`.
* `gaussianCVaR_eq_VaR_plus_tail_term`: the algebraic additive decomposition
  `CVaR = VaR + σ·(ϕ(z)/(1−α) − z)` (the original scope of this file).
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- The **Rockafellar–Uryasev objective** for a Gaussian loss `L = μ + σ·Z`:
`g(c) = c + E[(L − c)⁺]/(1 − α)`, the expectation written against the
standard-normal density. -/
noncomputable def ruObjective (μ σ α c : ℝ) : ℝ :=
  c + (∫ x, max (μ + σ * x - c) 0 * gaussianPDFReal 0 1 x) / (1 - α)

/-- **Gaussian tail mass in pdf form**: `∫_{Ioi a} ϕ(x) dx = 1 − Φ(a)`. -/
lemma integral_gaussianPDFReal_Ioi (a : ℝ) :
    ∫ x in Set.Ioi a, gaussianPDFReal 0 1 x = 1 - Phi a := by
  have h_meas : (gaussianReal (0 : ℝ) 1 (Set.Ioi a)).toReal
      = ∫ x in Set.Ioi a, gaussianPDFReal 0 1 x := by
    rw [gaussianReal_apply_eq_integral _ one_ne_zero]
    exact ENNReal.toReal_ofReal <| setIntegral_nonneg measurableSet_Ioi
      (fun _ _ => gaussianPDFReal_nonneg _ _ _)
  rw [← h_meas, gaussianReal_Ioi_toReal, Phi_neg]

/-- Integrability of the shortfall integrand `x ↦ max(μ + σx − c, 0)·ϕ(x)`:
dominated by `(|μ − c| + |σ|·|x|)·ϕ(x)`, whose pieces are the Gaussian mass and
the (absolute) first moment. -/
lemma integrable_shortfall (μ σ c : ℝ) :
    Integrable (fun x => max (μ + σ * x - c) 0 * gaussianPDFReal 0 1 x) volume := by
  have h_meas : AEStronglyMeasurable
      (fun x => max (μ + σ * x - c) 0 * gaussianPDFReal 0 1 x) volume :=
    ((((measurable_const.add (measurable_const.mul measurable_id)).sub
      measurable_const).max measurable_const).mul
      (measurable_gaussianPDFReal 0 1)).aestronglyMeasurable
  have h_dom : Integrable
      (fun x => |μ - c| * gaussianPDFReal 0 1 x + |σ| * |x * gaussianPDFReal 0 1 x|)
      volume :=
    ((integrable_gaussianPDFReal 0 1).const_mul _).add
      (integrable_id_mul_gaussianPDFReal_volume.abs.const_mul _)
  refine h_dom.mono' h_meas (Filter.Eventually.of_forall fun x => ?_)
  have h_pdf_nn : 0 ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
  have h_max_nn : 0 ≤ max (μ + σ * x - c) 0 := le_max_right _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h_max_nn h_pdf_nn)]
  have h_max_le : max (μ + σ * x - c) 0 ≤ |μ - c| + |σ| * |x| := by
    rcases max_cases (μ + σ * x - c) 0 with ⟨h_eq, _⟩ | ⟨h_eq, _⟩
    · rw [h_eq]
      calc μ + σ * x - c = (μ - c) + σ * x := by ring
        _ ≤ |μ - c| + |σ * x| := add_le_add (le_abs_self _) (le_abs_self _)
        _ = |μ - c| + |σ| * |x| := by rw [abs_mul]
    · rw [h_eq]; positivity
  calc max (μ + σ * x - c) 0 * gaussianPDFReal 0 1 x
      ≤ (|μ - c| + |σ| * |x|) * gaussianPDFReal 0 1 x :=
        mul_le_mul_of_nonneg_right h_max_le h_pdf_nn
    _ = |μ - c| * gaussianPDFReal 0 1 x + |σ| * (|x| * gaussianPDFReal 0 1 x) := by
        ring
    _ = |μ - c| * gaussianPDFReal 0 1 x + |σ| * |x * gaussianPDFReal 0 1 x| := by
        rw [abs_mul, abs_of_nonneg h_pdf_nn]

/-- **Standard-normal expected shortfall**: `E[(Z − z)⁺] = ϕ(z) − z·(1 − Φ(z))`.
The positive part localizes the integral to the tail `Ioi z`, where it splits
into the truncated first moment (`= ϕ(z)`) minus `z` times the tail mass. -/
lemma integral_max_sub_mul_gaussianPDFReal (z : ℝ) :
    ∫ x, max (x - z) 0 * gaussianPDFReal 0 1 x
      = gaussianPDFReal 0 1 z - z * (1 - Phi z) := by
  have h_eq : (fun x => max (x - z) 0 * gaussianPDFReal 0 1 x)
      = Set.indicator (Set.Ioi z) (fun x => (x - z) * gaussianPDFReal 0 1 x) := by
    funext x
    by_cases hx : x ∈ Set.Ioi z
    · rw [Set.indicator_of_mem hx, max_eq_left (sub_nonneg.2 (Set.mem_Ioi.1 hx).le)]
    · have hxz : x ≤ z := not_lt.1 (fun h => hx (Set.mem_Ioi.2 h))
      rw [Set.indicator_of_notMem hx, max_eq_right (sub_nonpos.2 hxz), zero_mul]
  rw [h_eq, integral_indicator measurableSet_Ioi]
  have h_int_x : IntegrableOn (fun x => x * gaussianPDFReal 0 1 x) (Set.Ioi z) volume :=
    integrable_id_mul_gaussianPDFReal_volume.integrableOn
  have h_int_pdf : IntegrableOn (fun x => z * gaussianPDFReal 0 1 x) (Set.Ioi z) volume :=
    ((integrable_gaussianPDFReal 0 1).const_mul z).integrableOn
  calc ∫ x in Set.Ioi z, (x - z) * gaussianPDFReal 0 1 x
      = ∫ x in Set.Ioi z,
          (x * gaussianPDFReal 0 1 x - z * gaussianPDFReal 0 1 x) := by
        congr 1; funext x; ring
    _ = (∫ x in Set.Ioi z, x * gaussianPDFReal 0 1 x)
          - ∫ x in Set.Ioi z, z * gaussianPDFReal 0 1 x :=
        integral_sub h_int_x h_int_pdf
    _ = gaussianPDFReal 0 1 z - z * (1 - Phi z) := by
        rw [integral_id_mul_gaussianPDFReal_Ioi, integral_const_mul,
          integral_gaussianPDFReal_Ioi]

/-- **Affine-loss expected shortfall closed form**: for `L = μ + σ·Z` with
`σ > 0` and `z_c = (c − μ)/σ`,

  `E[(L − c)⁺] = σ·(ϕ(z_c) − z_c·(1 − Φ(z_c)))`. -/
lemma integral_shortfall_gaussian (μ σ c : ℝ) (hσ : 0 < σ) :
    ∫ x, max (μ + σ * x - c) 0 * gaussianPDFReal 0 1 x
      = σ * (gaussianPDFReal 0 1 ((c - μ) / σ)
          - (c - μ) / σ * (1 - Phi ((c - μ) / σ))) := by
  have h_eq : (fun x => max (μ + σ * x - c) 0 * gaussianPDFReal 0 1 x)
      = fun x => σ * (max (x - (c - μ) / σ) 0 * gaussianPDFReal 0 1 x) := by
    funext x
    have h_arg : μ + σ * x - c = σ * (x - (c - μ) / σ) := by field_simp; ring
    have h_scale : max (σ * (x - (c - μ) / σ)) 0 = σ * max (x - (c - μ) / σ) 0 := by
      rw [mul_max_of_nonneg _ _ hσ.le, mul_zero]
    rw [h_arg, h_scale, mul_assoc]
  rw [h_eq, integral_const_mul, integral_max_sub_mul_gaussianPDFReal]

/-- **The R-U objective attains CVaR at VaR**: `g(VaR_α) = CVaR_α` when
`Φ(z) = α < 1`. At `c = VaR = μ + σz` the shortfall threshold is exactly the
quantile, so the certificate is tight and the `z·(1 − Φ(z))` terms cancel. -/
theorem ruObjective_at_gaussianVaR (μ σ z α : ℝ) (hσ : 0 < σ)
    (hzα : Phi z = α) (hα1 : α < 1) :
    ruObjective μ σ α (gaussianVaR μ σ z) = gaussianCVaR μ σ z α := by
  unfold ruObjective gaussianVaR gaussianCVaR
  rw [integral_shortfall_gaussian _ _ _ hσ,
    show (μ + σ * z - μ) / σ = z from by field_simp; ring, hzα]
  have h1α : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 hα1.ne'
  field_simp
  ring

/-- **The R-U inequality** — minimality of CVaR over the whole objective: for
every threshold `c`, `CVaR_α ≤ g(c)`.

The proof is the pointwise certificate `(L − c)⁺ ≥ (L − c)·𝟙_{Z > z}`:
integrating against `ϕ` gives `E[(L − c)⁺] ≥ (μ − c)(1 − α) + σ·ϕ(z)`, and the
right side reassembles to `CVaR` after dividing by `1 − α`. No calculus, no
convexity machinery — the `α`-tail event itself certifies the minimum. -/
theorem gaussianCVaR_le_ruObjective (μ σ z α c : ℝ)
    (hzα : Phi z = α) (hα1 : α < 1) :
    gaussianCVaR μ σ z α ≤ ruObjective μ σ α c := by
  have h1α : 0 < 1 - α := sub_pos.2 hα1
  have h_int_const : IntegrableOn (fun x => (μ - c) * gaussianPDFReal 0 1 x)
      (Set.Ioi z) volume :=
    ((integrable_gaussianPDFReal 0 1).const_mul _).integrableOn
  have h_int_lin : IntegrableOn (fun x => σ * (x * gaussianPDFReal 0 1 x))
      (Set.Ioi z) volume :=
    (integrable_id_mul_gaussianPDFReal_volume.const_mul _).integrableOn
  have h_tail_int : IntegrableOn
      (fun x => (μ + σ * x - c) * gaussianPDFReal 0 1 x) (Set.Ioi z) volume :=
    (h_int_const.add h_int_lin).congr_fun
      (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  -- the certificate, integrated: ∫_{Ioi z} (μ + σx − c)·ϕ ≤ E[(L−c)⁺]
  have h_cert : ∫ x in Set.Ioi z, (μ + σ * x - c) * gaussianPDFReal 0 1 x
      ≤ ∫ x, max (μ + σ * x - c) 0 * gaussianPDFReal 0 1 x := by
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_mono (h_tail_int.integrable_indicator measurableSet_Ioi)
      (integrable_shortfall μ σ c) (fun x => ?_)
    have h_pdf_nn : 0 ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
    by_cases hx : x ∈ Set.Ioi z
    · rw [Set.indicator_of_mem hx]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) h_pdf_nn
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (le_max_right _ _) h_pdf_nn
  -- the certificate's value: (μ − c)·(1 − α) + σ·ϕ(z)
  have h_tail_val : ∫ x in Set.Ioi z, (μ + σ * x - c) * gaussianPDFReal 0 1 x
      = (μ - c) * (1 - α) + σ * gaussianPDFReal 0 1 z := by
    calc ∫ x in Set.Ioi z, (μ + σ * x - c) * gaussianPDFReal 0 1 x
        = ∫ x in Set.Ioi z, ((μ - c) * gaussianPDFReal 0 1 x
            + σ * (x * gaussianPDFReal 0 1 x)) := by
          congr 1; funext x; ring
      _ = (∫ x in Set.Ioi z, (μ - c) * gaussianPDFReal 0 1 x)
            + ∫ x in Set.Ioi z, σ * (x * gaussianPDFReal 0 1 x) :=
          integral_add h_int_const h_int_lin
      _ = (μ - c) * (1 - α) + σ * gaussianPDFReal 0 1 z := by
          rw [integral_const_mul, integral_const_mul,
            integral_gaussianPDFReal_Ioi, integral_id_mul_gaussianPDFReal_Ioi, hzα]
  -- reassemble: c + E[(L−c)⁺]/(1−α) ≥ c + ((μ−c)(1−α) + σϕ(z))/(1−α) = CVaR
  unfold ruObjective gaussianCVaR
  have h_num : (μ - c) * (1 - α) + σ * gaussianPDFReal 0 1 z
      ≤ ∫ x, max (μ + σ * x - c) 0 * gaussianPDFReal 0 1 x :=
    h_tail_val ▸ h_cert
  have h_div : ((μ - c) * (1 - α) + σ * gaussianPDFReal 0 1 z) / (1 - α)
      ≤ (∫ x, max (μ + σ * x - c) 0 * gaussianPDFReal 0 1 x) / (1 - α) := by
    gcongr
  have h_id : μ + σ * (gaussianPDFReal 0 1 z / (1 - α))
      = c + ((μ - c) * (1 - α) + σ * gaussianPDFReal 0 1 z) / (1 - α) := by
    rw [add_div, mul_div_cancel_right₀ _ h1α.ne']
    ring
  linarith

/-- **The Rockafellar–Uryasev theorem for the Gaussian loss** (packaged):
`CVaR_α` is the *least value* of the objective `g(c) = c + E[(L − c)⁺]/(1−α)`
over all thresholds `c`, and the minimum is attained at `c = VaR_α`. -/
theorem gaussianCVaR_isLeast_ruObjective (μ σ z α : ℝ) (hσ : 0 < σ)
    (hzα : Phi z = α) (hα1 : α < 1) :
    IsLeast (Set.range (ruObjective μ σ α)) (gaussianCVaR μ σ z α) :=
  ⟨⟨gaussianVaR μ σ z, ruObjective_at_gaussianVaR μ σ z α hσ hzα hα1⟩,
    by rintro y ⟨c, rfl⟩; exact gaussianCVaR_le_ruObjective μ σ z α c hzα hα1⟩

/-- **Gaussian CVaR additive decomposition** (the original, purely algebraic
content of this file): rearranging the gaussian closed forms,

`CVaR_α = VaR_α + σ · [ϕ(z)/(1 − α) − z]`.

Pure `ring` rearrangement of the definitions — the same content as
`gaussianCVaR_sub_VaR`, in additive form. The variational theorem it used to
defer is now `gaussianCVaR_isLeast_ruObjective` above. -/
lemma gaussianCVaR_eq_VaR_plus_tail_term (μ σ z α : ℝ) :
    gaussianCVaR μ σ z α =
      gaussianVaR μ σ z +
        σ * (gaussianPDFReal 0 1 z / (1 - α) - z) := by
  unfold gaussianCVaR gaussianVaR
  ring

end MathFin
