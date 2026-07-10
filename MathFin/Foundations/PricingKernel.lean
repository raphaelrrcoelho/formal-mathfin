/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.StatePrices
public import MathFin.Foundations.FTAPTwoState
public import MathFin.Foundations.ConvexPricingFunctional

/-!
# Pricing kernel from state prices + FTAP (phase 53)

The pre-existing `Foundations/StatePrices.lean` defines the **linear
pricing functional** `V_0(X) = Σ q_i · X_i` from Arrow-Debreu state
prices `q_i`, and proves it satisfies the standard pricing axioms (zero,
linearity, monotonicity, risk-neutral-consistency).

`Foundations/FTAPTwoState.lean` (phase 37) gives the **backward FTAP**:
under sign data `z_up > 0, z_down < 0`, an EMM exists with the named
canonical weights `emmWeightUp = −z_down/(z_up − z_down)`,
`emmWeightDown = z_up/(z_up − z_down)` (`emm_of_signs`).

This file *composes* both — formally, not only in prose:

* `statePrices_two_state` is **defined** as `e^{−rT} · emmWeight{Up,Down}`,
  so the FTAP lineage of the discounted state prices is carried by the
  definition itself;
* `pricingKernel_two_state` is **defined** as the two-state instance of
  `statePricePricing`, so its linearity / bond / monotonicity lemmas are
  consumed from `StatePrices` rather than re-proved.

This is the **stochastic discount factor** / **pricing kernel**
framework instantiated in the simplest finite-state market: every claim's
no-arb price is a single linear functional, and that functional's weights
are derived from no-arbitrage (Phase 37 backward FTAP) without needing to
be assumed.

## Why this is a meaningful bridge

The two state-price properties — non-negativity and summing-to-bond-
price — are *consequences* of the FTAP EMM construction, not separate
assumptions. The state-price framework becomes self-contained: no-arb
in (z_up, z_down) market ⟹ explicit pricing kernel via Phase 37.

## Results

* `statePrices_two_state`: the discounted Phase-37 EMM weights
  `e^{−rT} · emmWeight{Up,Down}` as the two-state state-price vector.
* `statePrices_two_state_nonneg`: non-negativity from the FTAP sign data.
* `statePrices_two_state_sum_eq_bond`: the state prices sum to `e^{−rT}`
  (the zero-coupon bond price) — Π(`1` payoff) consistency.
* `pricingKernel_two_state` (+ `_linear`, `_bond`, `_nonneg`): the pricing
  functional as the two-state instance of `statePricePricing`, with
  linearity / bond pricing / monotonicity consumed from `StatePrices`.
* `stateprice_call_butterfly_nonneg` — the headline: the no-arbitrage
  butterfly constraint, wiring `ConvexPricingFunctional` to the FTAP
  state prices (corpus entry `mf-pricing-kernel-butterfly`).
-/

@[expose] public section

namespace MathFin

/-- **Two-state state-price vector**: the discounted Phase-37 EMM weights.
From `FTAPTwoState`'s backward-FTAP construction (`emm_of_signs`), the
state prices are the named EMM weights times the discount factor:

  `q_state_up = e^{−rT} · emmWeightUp`,
  `q_state_down = e^{−rT} · emmWeightDown`.

The FTAP lineage is carried by the definition: this *is* the discounted
EMM weight vector, not a separately postulated one. -/
noncomputable def statePrices_two_state (z_up z_down rT : ℝ) : Fin 2 → ℝ :=
  ![Real.exp (-rT) * emmWeightUp z_up z_down,
    Real.exp (-rT) * emmWeightDown z_up z_down]

/-- **State prices are non-negative** when the FTAP sign condition
holds (`z_up > 0, z_down < 0`): EMM-weight positivity (Phase 37 sign
data) times positivity of the discount factor `e^{−rT}`. -/
theorem statePrices_two_state_nonneg (z_up z_down rT : ℝ)
    (h_up : 0 < z_up) (h_down : z_down < 0) :
    ∀ i, 0 ≤ statePrices_two_state z_up z_down rT i := by
  intro i
  have h_diff_pos : 0 < z_up - z_down := by linarith
  have h_exp_pos : 0 < Real.exp (-rT) := Real.exp_pos _
  have hup : 0 ≤ Real.exp (-rT) * emmWeightUp z_up z_down :=
    mul_nonneg h_exp_pos.le (div_pos (neg_pos.mpr h_down) h_diff_pos).le
  have hdown : 0 ≤ Real.exp (-rT) * emmWeightDown z_up z_down :=
    mul_nonneg h_exp_pos.le (div_pos h_up h_diff_pos).le
  fin_cases i
  · exact hup
  · exact hdown

/-- **State prices sum to the bond price** `e^{−rT}` (the zero-coupon
bond pays `1` in both states; its no-arb price equals `Σ q_state_i · 1
= Σ q_state_i`). This is the *discount-consistency* condition. -/
theorem statePrices_two_state_sum_eq_bond (z_up z_down rT : ℝ)
    (h_up : 0 < z_up) (h_down : z_down < 0) :
    statePrices_two_state z_up z_down rT 0 +
      statePrices_two_state z_up z_down rT 1 = Real.exp (-rT) := by
  have h_diff_ne : z_up - z_down ≠ 0 := by
    have h : 0 < z_up - z_down := by linarith
    exact h.ne'
  show Real.exp (-rT) * emmWeightUp z_up z_down +
      Real.exp (-rT) * emmWeightDown z_up z_down = Real.exp (-rT)
  unfold emmWeightUp emmWeightDown
  field_simp
  ring

/-- **Pricing kernel for a two-state market** (FTAP-derived): the
two-state instance of the `StatePrices` linear pricing functional,

  `V_0(X) = statePricePricing univ q_state ![X_up, X_down]
          = q_state_up · X_up + q_state_down · X_down`,

with `q_state` the discounted Phase-37 EMM weights. -/
noncomputable def pricingKernel_two_state
    (z_up z_down rT : ℝ) (X_up X_down : ℝ) : ℝ :=
  statePricePricing Finset.univ (statePrices_two_state z_up z_down rT)
    ![X_up, X_down]

/-- **Linearity in payoff** of the two-state pricing kernel:
`V_0(α X + β Y) = α V_0(X) + β V_0(Y)`. Direct consequence of state-price
linearity (`statePricePricing_add` + `statePricePricing_smul`). -/
theorem pricingKernel_two_state_linear
    (z_up z_down rT : ℝ) (α β X_up X_down Y_up Y_down : ℝ) :
    pricingKernel_two_state z_up z_down rT
        (α * X_up + β * Y_up) (α * X_down + β * Y_down) =
      α * pricingKernel_two_state z_up z_down rT X_up X_down +
      β * pricingKernel_two_state z_up z_down rT Y_up Y_down := by
  unfold pricingKernel_two_state
  have h := statePricePricing_add Finset.univ
      (statePrices_two_state z_up z_down rT)
      (fun i ↦ α * (![X_up, X_down] : Fin 2 → ℝ) i)
      (fun i ↦ β * (![Y_up, Y_down] : Fin 2 → ℝ) i)
  have hα := statePricePricing_smul Finset.univ
      (statePrices_two_state z_up z_down rT) (![X_up, X_down] : Fin 2 → ℝ) α
  have hβ := statePricePricing_smul Finset.univ
      (statePrices_two_state z_up z_down rT) (![Y_up, Y_down] : Fin 2 → ℝ) β
  calc statePricePricing Finset.univ (statePrices_two_state z_up z_down rT)
        ![α * X_up + β * Y_up, α * X_down + β * Y_down]
      = statePricePricing Finset.univ (statePrices_two_state z_up z_down rT)
          (fun i ↦ α * (![X_up, X_down] : Fin 2 → ℝ) i +
            β * (![Y_up, Y_down] : Fin 2 → ℝ) i) := by
        congr 1
        funext i
        fin_cases i <;> simp
    _ = α * statePricePricing Finset.univ
            (statePrices_two_state z_up z_down rT) ![X_up, X_down] +
          β * statePricePricing Finset.univ
            (statePrices_two_state z_up z_down rT) ![Y_up, Y_down] := by
        rw [h, hα, hβ]

/-- **Bond pricing via the kernel**: the zero-coupon bond `(1, 1)` is
priced at `e^{−rT}` — the unit payoff through `statePricePricing_one`
plus the state-price sum (`statePrices_two_state_sum_eq_bond`). -/
theorem pricingKernel_two_state_bond
    (z_up z_down rT : ℝ) (h_up : 0 < z_up) (h_down : z_down < 0) :
    pricingKernel_two_state z_up z_down rT 1 1 = Real.exp (-rT) := by
  unfold pricingKernel_two_state
  rw [show (![(1 : ℝ), 1] : Fin 2 → ℝ) = fun _ ↦ (1 : ℝ) from by
    funext i; fin_cases i <;> rfl]
  rw [statePricePricing_one, Fin.sum_univ_two]
  exact statePrices_two_state_sum_eq_bond z_up z_down rT h_up h_down

/-- **No-arbitrage monotonicity** for the two-state pricing kernel:
non-negative payoffs ⟹ non-negative price, via
`statePricePricing_nonneg` + `statePrices_two_state_nonneg`. -/
theorem pricingKernel_two_state_nonneg
    (z_up z_down rT : ℝ) (X_up X_down : ℝ)
    (h_up : 0 < z_up) (h_down : z_down < 0)
    (hXu : 0 ≤ X_up) (hXd : 0 ≤ X_down) :
    0 ≤ pricingKernel_two_state z_up z_down rT X_up X_down := by
  unfold pricingKernel_two_state
  refine statePricePricing_nonneg _ _ _
      (fun i _ ↦ statePrices_two_state_nonneg z_up z_down rT h_up h_down i)
      (fun i _ ↦ ?_)
  fin_cases i
  · exact hXu
  · exact hXd

/-- **No-arbitrage ⟹ butterfly spreads cost ≥ 0** (FTAP + convex pricing).
The FTAP two-state state prices are non-negative
(`statePrices_two_state_nonneg`, a consequence of `z_up > 0 > z_down`), so
the finite-state call-price functional `K ↦ Σᵢ qᵢ · max(Sᵢ − K, 0)` is
convex in the strike and the butterfly combination
`C(K₁) − 2·C((K₁+K₃)/2) + C(K₃)` is non-negative
(`Foundations/ConvexPricingFunctional.callPrice_finiteState_butterfly_nonneg`).

This is the canonical static no-arbitrage constraint on observed option
prices — butterfly spreads cannot have negative cost — derived here from the
FTAP state-price construction rather than assumed. It is the first downstream
consumer of `ConvexPricingFunctional`, wiring the convex-pricing principle to
the FTAP / state-price framework. -/
theorem stateprice_call_butterfly_nonneg
    (z_up z_down rT : ℝ) (h_up : 0 < z_up) (h_down : z_down < 0)
    (S : Fin 2 → ℝ) (K₁ K₃ : ℝ) :
    0 ≤ (∑ i, statePrices_two_state z_up z_down rT i * max (S i - K₁) 0)
        - 2 * (∑ i, statePrices_two_state z_up z_down rT i *
              max (S i - (K₁ + K₃) / 2) 0)
        + (∑ i, statePrices_two_state z_up z_down rT i * max (S i - K₃) 0) :=
  callPrice_finiteState_butterfly_nonneg Finset.univ S
    (statePrices_two_state z_up z_down rT)
    (fun i _ ↦ statePrices_two_state_nonneg z_up z_down rT h_up h_down i) K₁ K₃

end MathFin
