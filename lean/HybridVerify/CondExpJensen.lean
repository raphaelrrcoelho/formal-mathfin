/-
  HybridVerify.CondExpJensen
  Proposition 2.1.11(9): conditional Jensen's inequality, parametrized by an
  explicit subgradient (Mathlib v4.30 has no general subgradient API for
  convex functions on ℝ; any convex `φ` has such a `g`, e.g. its right
  derivative).
-/
import Mathlib

namespace HybridVerify

open MeasureTheory

/-- Conditional Jensen's inequality, with the subgradient supplied explicitly.
    The textbook statement uses just convexity, but Mathlib has no general
    subgradient API for convex functions on ℝ; we therefore parametrize the
    inequality by an explicit subgradient function `g : ℝ → ℝ` together with
    the supporting-line property. Any convex `φ` on `ℝ` has such a `g` (e.g.
    its right derivative). -/
structure ConditionalJensen {α : Type*} {m₀ : MeasurableSpace α}
    (μ : Measure α) [IsFiniteMeasure μ] (m : MeasurableSpace α) (hm : m ≤ m₀)
    (φ : ℝ → ℝ) (X : α → ℝ) where
  phi_convex : ConvexOn ℝ Set.univ φ
  phi_measurable : Measurable φ
  X_integrable : Integrable X μ
  phi_X_integrable : Integrable (fun a => φ (X a)) μ
  /-- Explicit subgradient `g` of `φ`. -/
  subgrad : ℝ → ℝ
  subgrad_measurable : Measurable subgrad
  /-- Supporting-line property: `φ(y) + g(y)(x − y) ≤ φ(x)` for all `x, y`. -/
  subgrad_property : ∀ x y, φ y + subgrad y * (x - y) ≤ φ x
  /-- `g` is uniformly bounded (so `g(E[X|m]) (X − E[X|m])` is integrable). -/
  subgrad_bounded : ∃ K : ℝ, ∀ x, |subgrad x| ≤ K
  /-- `φ ∘ E[X|m]` is integrable. -/
  phi_condExp_integrable : Integrable (fun a => φ ((μ[X | m]) a)) μ

namespace ConditionalJensen

variable {α : Type*} {m₀ : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  {m : MeasurableSpace α} {hm : m ≤ m₀} {φ : ℝ → ℝ} {X : α → ℝ}

/-- **Proposition 2.1.11(9), conditional Jensen's inequality.** Given an
    explicit subgradient `g` of the convex function `φ`, the supporting-line
    property + integrability + boundedness hypotheses imply
    `φ(E[X|m]) ≤ᵐ E[φ(X)|m]`. -/
theorem conditional_jensen_inequality (h : ConditionalJensen μ m hm φ X) :
    (fun a => φ ((μ[X | m]) a)) ≤ᵐ[μ] (μ[fun a => φ (X a) | m]) := by
  obtain ⟨K, hK⟩ := h.subgrad_bounded
  set Y : α → ℝ := μ[X | m] with hY_def
  have hY_meas : StronglyMeasurable[m] Y :=
    (stronglyMeasurable_condExp : StronglyMeasurable[m] (μ[X | m]))
  have hY_int : Integrable Y μ := integrable_condExp
  have hgY_meas : StronglyMeasurable[m] (fun a => h.subgrad (Y a)) :=
    (h.subgrad_measurable.comp hY_meas.measurable).stronglyMeasurable
  have hgY_bound : ∀ᵐ a ∂μ, ‖h.subgrad (Y a)‖ ≤ K :=
    ae_of_all _ (fun a => by simpa [Real.norm_eq_abs] using hK (Y a))
  have hXmY_int : Integrable (X - Y) μ := h.X_integrable.sub hY_int
  have hgYmul_int : Integrable ((fun a => h.subgrad (Y a)) * (X - Y)) μ := by
    apply Integrable.bdd_mul hXmY_int
    · exact (hgY_meas.mono hm).aestronglyMeasurable
    · exact hgY_bound
  have hY_self_condExp : μ[Y | m] = Y :=
    condExp_of_stronglyMeasurable hm hY_meas hY_int
  have hXmY_condExp : μ[X - Y | m] =ᵐ[μ] (0 : α → ℝ) := by
    have h1 : μ[X - Y | m] =ᵐ[μ] μ[X | m] - μ[Y | m] :=
      condExp_sub h.X_integrable hY_int _
    filter_upwards [h1] with a ha
    have happ : (μ[X | m] - μ[Y | m]) a = (μ[X | m]) a - (μ[Y | m]) a := rfl
    rw [ha, happ, hY_self_condExp]
    simp [hY_def]
  have hpullout : μ[(fun a => h.subgrad (Y a)) * (X - Y) | m] =ᵐ[μ]
                  (fun a => h.subgrad (Y a)) * μ[X - Y | m] :=
    condExp_mul_of_stronglyMeasurable_left hgY_meas hgYmul_int hXmY_int
  have hgYmul_condExp : μ[(fun a => h.subgrad (Y a)) * (X - Y) | m] =ᵐ[μ] (0 : α → ℝ) := by
    refine hpullout.trans ?_
    filter_upwards [hXmY_condExp] with a ha
    show (fun a => h.subgrad (Y a)) a * (μ[X - Y | m]) a = (0 : α → ℝ) a
    rw [ha]; simp
  have hpw : (fun a => h.subgrad (Y a) * (X a - Y a)) ≤ᵐ[μ]
             (fun a => φ (X a) - φ (Y a)) := by
    refine ae_of_all _ (fun a => ?_)
    have hsg := h.subgrad_property (X a) (Y a)
    show h.subgrad (Y a) * (X a - Y a) ≤ φ (X a) - φ (Y a)
    linarith
  have hgYmul_eq : (fun a => h.subgrad (Y a) * (X a - Y a)) =
                   ((fun a => h.subgrad (Y a)) * (X - Y)) := rfl
  have hphi_diff_int : Integrable (fun a => φ (X a) - φ (Y a)) μ :=
    h.phi_X_integrable.sub h.phi_condExp_integrable
  have hgYmul_int' : Integrable (fun a => h.subgrad (Y a) * (X a - Y a)) μ := by
    rw [hgYmul_eq]; exact hgYmul_int
  have hcompare : μ[fun a => h.subgrad (Y a) * (X a - Y a) | m] ≤ᵐ[μ]
                  μ[fun a => φ (X a) - φ (Y a) | m] :=
    condExp_mono hgYmul_int' hphi_diff_int hpw
  have hLHS : μ[fun a => h.subgrad (Y a) * (X a - Y a) | m] =ᵐ[μ] (0 : α → ℝ) := by
    have heq : (fun a => h.subgrad (Y a) * (X a - Y a)) =
               ((fun a => h.subgrad (Y a)) * (X - Y)) := hgYmul_eq
    rw [heq]
    exact hgYmul_condExp
  have hphi_diff_eq : (fun a => φ (X a) - φ (Y a)) =
                     (fun a => φ (X a)) - (fun a => φ (Y a)) := rfl
  have hphiY_meas : StronglyMeasurable[m] (fun a => φ (Y a)) :=
    (h.phi_measurable.comp hY_meas.measurable).stronglyMeasurable
  have hphiY_self : μ[fun a => φ (Y a) | m] = (fun a => φ (Y a)) :=
    condExp_of_stronglyMeasurable hm hphiY_meas h.phi_condExp_integrable
  have hRHS : μ[fun a => φ (X a) - φ (Y a) | m] =ᵐ[μ]
              (fun a => (μ[fun a => φ (X a) | m]) a - φ (Y a)) := by
    have h1 : μ[fun a => φ (X a) - φ (Y a) | m] =ᵐ[μ]
              μ[fun a => φ (X a) | m] - μ[fun a => φ (Y a) | m] := by
      rw [hphi_diff_eq]
      exact condExp_sub h.phi_X_integrable h.phi_condExp_integrable _
    filter_upwards [h1] with a ha
    have hsub : (μ[fun a => φ (X a) | m] - μ[fun a => φ (Y a) | m]) a =
                (μ[fun a => φ (X a) | m]) a - (μ[fun a => φ (Y a) | m]) a := rfl
    rw [ha, hsub, hphiY_self]
  filter_upwards [hcompare, hLHS, hRHS] with a hcmp hL hR
  rw [hL, hR] at hcmp
  simp only [Pi.zero_apply] at hcmp
  linarith

end ConditionalJensen

end HybridVerify
