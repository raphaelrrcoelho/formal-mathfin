/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Performance.Ratios

/-!
# The Kelly (growth-optimal) portfolio as numéraire ⟹ the risk-neutral measure

The growth-optimal (log-optimal) portfolio is the **numéraire portfolio**: deflating
the physical measure by the growth-optimal wealth turns it into the equivalent
martingale measure (Long 1990 / Platen's benchmark approach). This file realizes that
identity in the two-outcome Kelly market — the discrete, fully elementary shadow of the
continuous statement (which needs a state-price-density / market model absent from the
Itô tower).

Setup (`Performance/Ratios`): a binary bet at fraction `f` pays odds `b` (wealth
multiplier `1 + f·b`) with physical probability `p`, or loses the stake (multiplier
`1 - f`) with probability `1 - p`. The **Kelly fraction** `f* = kellyFraction p b`
maximizes the expected log-growth `kellyGrowth p b` — its first-order optimality is
`kellyGrowth_deriv_at_kelly`. The growth-optimal terminal wealths are

  `W*₊ = 1 + f*·b`   (winning state),   `W*₋ = 1 - f*`   (losing state).

**Deflating the physical measure by `W*`** (dividing each state's physical probability
by the growth-optimal wealth there) gives `q₊ = p/W*₊`, `q₋ = (1-p)/W*₋`. The punchline:

  `q₊ = 1/(b+1)`,   `q₋ = b/(b+1)`   — **independent of the physical `p`** —

the unique *fair-odds* (risk-neutral) probabilities for a bet paying `b`-to-`1`. They sum
to `1` (a probability measure) and price the bet as a martingale
(`q₊·b + q₋·(−1) = 0`, zero expected excess return): the GOP-deflated measure **is** the
EMM. The `p`-independence is exactly the content of the Kelly first-order condition —
`1 + f*·b = p·(b+1)`, so the physical `p` cancels in the deflation. Change the numéraire
to the growth-optimal portfolio and the physical measure becomes risk-neutral.

## Results
* `kellyGOPWealth_win`, `kellyGOPWealth_lose` — the growth-optimal terminal wealths
  `W*₊ = p(b+1)` and `W*₋ = (1-p)(b+1)/b` (the Kelly first-order condition made explicit).
* `kellyDeflatedProb_win`, `kellyDeflatedProb_lose` — the GOP-deflated probabilities
  `q₊ = 1/(b+1)`, `q₋ = b/(b+1)`.
* `kellyDeflatedProb_sum_one` — `q₊ + q₋ = 1` (a probability measure).
* `kellyNumeraire_isRiskNeutral` — `q₊·b + q₋·(−1) = 0`: the bet is a martingale under
  the GOP-deflated measure. The (discrete) numéraire-portfolio ⟹ EMM identity.
-/

@[expose] public section

namespace MathFin

open Real

variable {p b : ℝ}

/-- **Growth-optimal winning wealth** `W*₊ = 1 + f*·b = p·(b+1)`. This is the Kelly
first-order condition (`kellyGrowth_deriv_at_kelly`) made explicit: the physical `p`
appears as the whole factor, which is what lets it cancel in the deflation below. -/
lemma kellyGOPWealth_win (hb : b ≠ 0) :
    1 + kellyFraction p b * b = p * (b + 1) := by
  unfold kellyFraction; field_simp; ring

/-- **Growth-optimal losing wealth** `W*₋ = 1 - f* = (1-p)·(b+1)/b`. -/
lemma kellyGOPWealth_lose (hb : b ≠ 0) :
    1 - kellyFraction p b = (1 - p) * (b + 1) / b := by
  unfold kellyFraction; field_simp; ring

/-- **GOP-deflated winning probability** `q₊ = p / W*₊ = 1/(b+1)`: the physical `p`,
deflated by the growth-optimal wealth, is the fair-odds risk-neutral probability —
independent of `p`. -/
lemma kellyDeflatedProb_win (hp : 0 < p) (hb : 0 < b) :
    p / (1 + kellyFraction p b * b) = 1 / (b + 1) := by
  rw [kellyGOPWealth_win hb.ne']
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **GOP-deflated losing probability** `q₋ = (1-p) / W*₋ = b/(b+1)`. -/
lemma kellyDeflatedProb_lose (hp1 : p < 1) (hb : 0 < b) :
    (1 - p) / (1 - kellyFraction p b) = b / (b + 1) := by
  have hq : 0 < 1 - p := by linarith
  rw [kellyGOPWealth_lose hb.ne']
  rw [div_div_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **The GOP-deflated probabilities form a probability measure**: `q₊ + q₋ = 1`. -/
theorem kellyDeflatedProb_sum_one (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    p / (1 + kellyFraction p b * b) + (1 - p) / (1 - kellyFraction p b) = 1 := by
  rw [kellyDeflatedProb_win hp hb, kellyDeflatedProb_lose hp1 hb]
  have : (b : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- **The Kelly numéraire portfolio induces the risk-neutral measure.** Under the
GOP-deflated measure `q₊ = p/W*₊`, `q₋ = (1-p)/W*₋`, the bet's excess return has zero
mean:

  `q₊·b + q₋·(−1) = 0`,

i.e. the discounted asset is a `q`-martingale — `q` is the equivalent martingale
measure. This is the (discrete, two-outcome) **numéraire-portfolio ⟹ EMM** identity: the
growth-optimal portfolio is the numéraire whose deflator turns the physical measure into
the EMM, the risk-neutrality being exactly the vanishing of the Kelly first-order
condition (`kellyGrowth_deriv_at_kelly`). -/
theorem kellyNumeraire_isRiskNeutral (hp : 0 < p) (hp1 : p < 1) (hb : 0 < b) :
    p / (1 + kellyFraction p b * b) * b
      + (1 - p) / (1 - kellyFraction p b) * (-1) = 0 := by
  rw [kellyDeflatedProb_win hp hb, kellyDeflatedProb_lose hp1 hb]
  ring

end MathFin
