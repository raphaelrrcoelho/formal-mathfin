/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# The change of numéraire

A **numéraire** is a strictly positive traded asset taken as the unit of
account. Fix a pricing measure `Q` associated to a reference numéraire `B` (the
money market): the arbitrage-free price of a terminal claim `X` is

  `price(X) = B₀ · 𝔼^Q[X / B_T]`.

Given a second numéraire `N` — strictly positive, with `N/B` a `Q`-martingale
(the tradeability/normalization condition `𝔼^Q[N_T/B_T] = N₀/B₀`) — define the
**numéraire measure** `Q^N` by the Radon–Nikodym density

  `dQ^N/dQ := (N_T · B₀) / (N₀ · B_T)`.

The **change-of-numéraire theorem** (`changeOfNumeraire`) is that price is
numéraire-invariant:

  `N₀ · 𝔼^{Q^N}[X / N_T] = B₀ · 𝔼^Q[X / B_T]`.

The proof is a one-line cancellation: transporting the `Q^N`-expectation back to
`Q` multiplies the integrand `X/N_T` by the density `(N_T·B₀)/(N₀·B_T)`, and the
`N_T` cancels, leaving `(B₀/N₀)·(X/B_T)`; the leading `N₀` cancels the `1/N₀`.
Notably the identity needs **no integrability hypothesis** — it is a pure
measure-transport identity (`integral_withDensity_eq_integral_toReal_smul`)
followed by scalar algebra, so it holds verbatim whether or not the claim is
square-integrable.

This is the abstract backbone of every concrete numéraire change in the library.
The stock numéraire (`BlackScholes.StockNumeraire`: `Φ(d₁)` as the stock-measure
exercise probability) is the instance `B_T = e^{rT}`, `B₀ = 1`, `N = S`; the
second-asset numéraire of the exchange option (`BlackScholes.ExchangeOption`)
and the forward/annuity numéraires of the Garman normal form
(`BlackScholes.GarmanNormalForm`) are further instances — each recovered by
choosing `B`, `N` and reading off the density.

## Main results

* `MathFin.numeraireMeasure` — the tilted measure `Q^N = Q.withDensity(dQ^N/dQ)`.
* `MathFin.numeraireMeasure_isProbabilityMeasure` — `Q^N` is a probability
  measure, under the martingale/normalization condition `𝔼^Q[N_T/B_T] = N₀/B₀`.
* `MathFin.changeOfNumeraire` — price invariance
  `N₀·𝔼^{Q^N}[X/N_T] = B₀·𝔼^Q[X/B_T]`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*}

/-- **The numéraire-change density** `dQ^N/dQ = (N_T · B₀)/(N₀ · B_T)`, as a
`[0,∞]`-valued Radon–Nikodym derivative. Nonnegative whenever the numéraires are
positive. -/
noncomputable def numeraireDensity (BT NT : Ω → ℝ) (B0 N0 : ℝ) : Ω → ℝ≥0∞ :=
  fun ω => ENNReal.ofReal (NT ω * B0 / (N0 * BT ω))

/-- The numéraire density is a nonnegative real when both numéraires are
positive. -/
lemma numeraireDensity_toReal_nonneg {BT NT : Ω → ℝ} {B0 N0 : ℝ}
    (hNTpos : ∀ ω, 0 < NT ω) (hBTpos : ∀ ω, 0 < BT ω)
    (hB0 : 0 ≤ B0) (hN0 : 0 < N0) (ω : Ω) :
    0 ≤ NT ω * B0 / (N0 * BT ω) :=
  div_nonneg (mul_nonneg (hNTpos ω).le hB0) (mul_nonneg hN0.le (hBTpos ω).le)

/-- **The numéraire measure** `Q^N := Q.withDensity((N_T·B₀)/(N₀·B_T))`: the
pricing measure attached to numéraire `N`. -/
noncomputable def numeraireMeasure [MeasurableSpace Ω]
    (Q : Measure Ω) (BT NT : Ω → ℝ) (B0 N0 : ℝ) : Measure Ω :=
  Q.withDensity (numeraireDensity BT NT B0 N0)

section

variable [MeasurableSpace Ω] {Q : Measure Ω} {BT NT : Ω → ℝ} {B0 N0 : ℝ}

/-- **The numéraire measure is a probability measure.** Under the tradeability /
normalization condition `𝔼^Q[N_T/B_T] = N₀/B₀` (equivalently: `N/B` is a
`Q`-martingale), the total mass `∫ dQ^N/dQ ∂Q` equals `(B₀/N₀)·(N₀/B₀) = 1`. -/
theorem numeraireMeasure_isProbabilityMeasure
    (hNTpos : ∀ ω, 0 < NT ω) (hBTpos : ∀ ω, 0 < BT ω) (hB0 : 0 < B0) (hN0 : 0 < N0)
    (hint : Integrable (fun ω => NT ω / BT ω) Q)
    (hmart : ∫ ω, NT ω / BT ω ∂Q = N0 / B0) :
    IsProbabilityMeasure (numeraireMeasure Q BT NT B0 N0) := by
  constructor
  have hden : numeraireMeasure Q BT NT B0 N0
      = Q.withDensity (fun ω => ENNReal.ofReal (NT ω * B0 / (N0 * BT ω))) := rfl
  rw [hden, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hρnn : 0 ≤ᵐ[Q] fun ω => NT ω * B0 / (N0 * BT ω) :=
    ae_of_all _ (numeraireDensity_toReal_nonneg hNTpos hBTpos hB0.le hN0)
  have heq : (fun ω => NT ω * B0 / (N0 * BT ω)) = fun ω => (B0 / N0) * (NT ω / BT ω) := by
    funext ω; ring
  have hρint : Integrable (fun ω => NT ω * B0 / (N0 * BT ω)) Q := by
    rw [heq]; exact hint.const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hρint hρnn, heq, integral_const_mul, hmart]
  have hone : B0 / N0 * (N0 / B0) = 1 := by
    field_simp
  rw [hone, ENNReal.ofReal_one]

/-- **The change-of-numéraire theorem.** Price is numéraire-invariant:

  `N₀ · 𝔼^{Q^N}[X / N_T] = B₀ · 𝔼^Q[X / B_T]`,

where `Q^N = Q.withDensity((N_T·B₀)/(N₀·B_T))`. The proof transports the
`Q^N`-integral back to `Q` (multiplying by the density) and cancels `N_T`; no
integrability hypothesis is needed. -/
theorem changeOfNumeraire (X : Ω → ℝ)
    (hNTmeas : Measurable NT) (hBTmeas : Measurable BT)
    (hNTpos : ∀ ω, 0 < NT ω) (hBTpos : ∀ ω, 0 < BT ω) (hB0 : 0 ≤ B0) (hN0 : 0 < N0) :
    N0 * ∫ ω, X ω / NT ω ∂(numeraireMeasure Q BT NT B0 N0)
      = B0 * ∫ ω, X ω / BT ω ∂Q := by
  have hden : numeraireMeasure Q BT NT B0 N0
      = Q.withDensity (fun ω => ENNReal.ofReal (NT ω * B0 / (N0 * BT ω))) := rfl
  have hdmeas : Measurable fun ω => NT ω * B0 / (N0 * BT ω) :=
    (hNTmeas.mul measurable_const).div (measurable_const.mul hBTmeas)
  rw [hden, integral_withDensity_eq_integral_toReal_smul hdmeas.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hcongr : ∀ ω, (ENNReal.ofReal (NT ω * B0 / (N0 * BT ω))).toReal • (X ω / NT ω)
      = (B0 / N0) * (X ω / BT ω) := by
    intro ω
    rw [ENNReal.toReal_ofReal (numeraireDensity_toReal_nonneg hNTpos hBTpos hB0 hN0 ω),
      smul_eq_mul]
    field_simp [(hNTpos ω).ne', (hBTpos ω).ne', hN0.ne']
  simp_rw [hcongr, integral_const_mul]
  have hcancel : N0 * (B0 / N0 * ∫ ω, X ω / BT ω ∂Q) = B0 * ∫ ω, X ω / BT ω ∂Q := by
    field_simp [hN0.ne']
  exact hcancel

end

end MathFin
