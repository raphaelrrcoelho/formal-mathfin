/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib
import MathFin.Binomial.American
import MathFin.Binomial.MartingaleRepresentation

/-!
# Snell envelope characterization of `americanPrice` — scalar and path-space

In the discrete-time binomial tree, the American option price is the **Snell
envelope** of the payoff `g`: the *smallest* process satisfying intrinsic
dominance and the one-step supermartingale property. This file proves the
characterization at **two levels**:

**Scalar (Markov) level.** The smallest function `V : ℕ → ℝ → ℝ` with

1. **Intrinsic dominance**: `V n S ≥ g S` at every step `n` and spot `S`;
2. **One-step supermartingale**: `V (n+1) S ≥ e^{-r}·(q·V n (uS) + (1−q)·V n (dS))`

is `americanPrice` (`americanPrice_is_snell_envelope`, with minimality from
`americanPrice_le_of_supermartingale_dominating`).

**Path-space level.** On coin-flip paths `ω : ℕ → Bool` — the same pathwise
language as `Binomial/MartingaleRepresentation.lean`, where the conditional
expectation w.r.t. the binomial filtration is the explicit node average
`E[X_{k+1} | ℱ_k](ω) = q·X_{k+1}(up child) + (1−q)·X_{k+1}(down child)` —
the envelope `snell q Z N k` of a payoff *process* `Z` is defined by the
backward Bellman recursion, and the four clauses of the Snell theorem are
each proved: payoff dominance (`snellAux_ge_payoff`), the supermartingale
property (`snellAux_supermartingale`), adaptedness — the filtration content
(`pathAdaptedAt_snellAux`) — and **minimality over arbitrary path-processes**
(`snellAux_le_of_supermartingale_of_ge`), a strictly larger competitor class
than the scalar form's Markov candidates.

The **identification theorem** (`snellAux_eq_discounted_americanPrice`)
closes the loop: for the discounted intrinsic payoff
`Z_k(ω) = e^{−rk}·g(S_k(ω))` along the spot path
`S_k(ω) = S₀·∏_{i<k}(u if ωᵢ else d)` and risk-neutral `q = crrUpProb`,

  `snell q Z N k ω = e^{−rk} · americanPrice u d r g (N−k) (S_k(ω))`.

The scalar Bellman recursion is thereby the Markov instance of the genuine
path-space Snell envelope, and the supermartingale / intrinsic-dominance
statements about the American price become clauses of the characterization
(`discounted_americanPrice_supermartingale`,
`discounted_intrinsic_le_americanPrice`, `americanPrice_snell_minimal`).

The remaining classical form — `americanPrice = sup over stopping times τ of
E^Q[e^{−rτ} g(S_τ)]` — is downstream work on top of this file's path layer.

## Results

* `americanPrice_le_of_supermartingale_dominating`, `americanPrice_is_snell_envelope`:
  the scalar characterization.
* `spotPath`, `snellAux`, `snell`: the path-space objects.
* `snellAux_ge_payoff` / `snellAux_supermartingale` / `pathAdaptedAt_snellAux` /
  `snellAux_le_of_supermartingale_of_ge`: the four Snell clauses on paths.
* `snellAux_eq_discounted_americanPrice`: the identification theorem.
* `discounted_americanPrice_supermartingale`, `discounted_intrinsic_le_americanPrice`,
  `americanPrice_snell_minimal`: the American-price corollaries on paths.
-/

namespace MathFin

/-- **Snell envelope upper bound**: any function `V : ℕ → ℝ → ℝ` that
dominates the payoff (`hV_g`) and satisfies the one-step supermartingale
condition (`hV_super`) is bounded below by `americanPrice` at every step
and spot.

Combined with `americanPrice_ge_intrinsic` and `americanPrice_supermartingale`
(which show `americanPrice` itself satisfies both conditions), this gives
the **Snell envelope characterization**: `americanPrice` is the smallest
such `V`.

Proof: induction on `n`. The base case `n = 0` uses `hV_g 0 S`. The
inductive step uses (a) `hV_g (n+1) S` to bound the intrinsic side of the
Bellman `max`, and (b) `hV_super n S` plus monotonicity of the one-step
operator (`binomialOptionPriceOnePeriod_mono`) plus the IH to bound the
continuation side. -/
theorem americanPrice_le_of_supermartingale_dominating
    {u d r : ℝ} (h : BinomialNoArb u d r) (g : ℝ → ℝ) (V : ℕ → ℝ → ℝ)
    (hV_g : ∀ n S, g S ≤ V n S)
    (hV_super : ∀ n S,
      binomialOptionPriceOnePeriod u d r (V n (S * u)) (V n (S * d)) ≤
        V (n + 1) S) :
    ∀ n S, americanPrice u d r g n S ≤ V n S := by
  intro n
  induction n with
  | zero =>
    intro S
    rw [americanPrice_zero]
    exact hV_g 0 S
  | succ n ih =>
    intro S
    rw [americanPrice_succ]
    refine max_le (hV_g (n + 1) S) ?_
    calc binomialOptionPriceOnePeriod u d r
          (americanPrice u d r g n (S * u)) (americanPrice u d r g n (S * d))
        ≤ binomialOptionPriceOnePeriod u d r (V n (S * u)) (V n (S * d)) :=
          binomialOptionPriceOnePeriod_mono h (ih (S * u)) (ih (S * d))
      _ ≤ V (n + 1) S := hV_super n S

/-- **Snell envelope theorem (packaged form)**: `americanPrice u d r g` is
the smallest function `V : ℕ → ℝ → ℝ` that simultaneously dominates the
payoff and satisfies the one-step supermartingale property.

The statement makes the universal characterization visible: for *any* V
satisfying the two properties, `americanPrice ≤ V`. -/
theorem americanPrice_is_snell_envelope
    {u d r : ℝ} (h : BinomialNoArb u d r) (g : ℝ → ℝ) :
    (∀ n S, g S ≤ americanPrice u d r g n S) ∧
    (∀ n S,
      binomialOptionPriceOnePeriod u d r
        (americanPrice u d r g n (S * u)) (americanPrice u d r g n (S * d)) ≤
      americanPrice u d r g (n + 1) S) ∧
    (∀ (V : ℕ → ℝ → ℝ),
      (∀ n S, g S ≤ V n S) →
      (∀ n S,
        binomialOptionPriceOnePeriod u d r (V n (S * u)) (V n (S * d)) ≤
          V (n + 1) S) →
      ∀ n S, americanPrice u d r g n S ≤ V n S) :=
  ⟨americanPrice_ge_intrinsic u d r g,
   americanPrice_supermartingale u d r g,
   americanPrice_le_of_supermartingale_dominating h g⟩

/-! ## The path-space Snell envelope

Coin-flip paths `ω : ℕ → Bool`, payoff *processes* `Z : ℕ → (ℕ → Bool) → ℝ`,
and the node-average conditional expectation, as in
`Binomial/MartingaleRepresentation.lean`. -/

variable {q : ℝ} {Z U : ℕ → (ℕ → Bool) → ℝ}

/-- The **spot path**: `S_k(ω) = S₀ · ∏_{i<k} (u if ωᵢ else d)`. -/
noncomputable def spotPath (S₀ u d : ℝ) (k : ℕ) (ω : ℕ → Bool) : ℝ :=
  S₀ * ∏ i ∈ Finset.range k, (if ω i then u else d)

/-- One-step spot recursion along the `k`-th flip. -/
lemma spotPath_update_succ (S₀ u d : ℝ) (k : ℕ) (ω : ℕ → Bool) (b : Bool) :
    spotPath S₀ u d (k + 1) (Function.update ω k b)
      = spotPath S₀ u d k ω * (if b then u else d) := by
  unfold spotPath
  rw [Finset.prod_range_succ]
  have h_prefix : ∏ i ∈ Finset.range k, (if Function.update ω k b i then u else d)
      = ∏ i ∈ Finset.range k, (if ω i then u else d) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.mem_range.1 hi).ne]
  rw [h_prefix]
  simp [mul_assoc]

/-- Up-child spot: `S_{k+1}(ω, k-th flip up) = S_k(ω) · u`. -/
lemma spotPath_update_succ_true (S₀ u d : ℝ) (k : ℕ) (ω : ℕ → Bool) :
    spotPath S₀ u d (k + 1) (Function.update ω k true) = spotPath S₀ u d k ω * u := by
  simpa using spotPath_update_succ S₀ u d k ω true

/-- Down-child spot: `S_{k+1}(ω, k-th flip down) = S_k(ω) · d`. -/
lemma spotPath_update_succ_false (S₀ u d : ℝ) (k : ℕ) (ω : ℕ → Bool) :
    spotPath S₀ u d (k + 1) (Function.update ω k false) = spotPath S₀ u d k ω * d := by
  simpa using spotPath_update_succ S₀ u d k ω false

/-- The spot path is adapted: `S_k` depends only on the first `k` flips. -/
lemma pathAdaptedAt_spotPath (S₀ u d : ℝ) (k : ℕ) :
    PathAdaptedAt k (spotPath S₀ u d k) := fun ω ω' h => by
  unfold spotPath
  congr 1
  exact Finset.prod_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

/-- **Snell envelope, by remaining steps**: `snellAux q Z j k` is the envelope
value at time `k` with `j` steps to the horizon. `j = 0`: the payoff;
`j + 1`: the Bellman max of immediate payoff against the node-average
continuation `E[· | ℱ_k]`. -/
noncomputable def snellAux (q : ℝ) (Z : ℕ → (ℕ → Bool) → ℝ) : ℕ → ℕ → (ℕ → Bool) → ℝ
  | 0, k, ω => Z k ω
  | j + 1, k, ω => max (Z k ω)
      (q * snellAux q Z j (k + 1) (Function.update ω k true)
        + (1 - q) * snellAux q Z j (k + 1) (Function.update ω k false))

/-- The **Snell envelope** of the payoff process `Z` over horizon `N`,
indexed by absolute time `k`. -/
noncomputable def snell (q : ℝ) (Z : ℕ → (ℕ → Bool) → ℝ) (N k : ℕ) (ω : ℕ → Bool) : ℝ :=
  snellAux q Z (N - k) k ω

/-- **Dominance clause**: the envelope dominates the payoff at every node. -/
theorem snellAux_ge_payoff (q : ℝ) (Z : ℕ → (ℕ → Bool) → ℝ) (j k : ℕ) (ω : ℕ → Bool) :
    Z k ω ≤ snellAux q Z j k ω := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact le_max_left _ _

/-- **Supermartingale clause**: the node-average of the next-step envelope is
at most the current envelope — `E[V_{k+1} | ℱ_k] ≤ V_k` in node-average form. -/
theorem snellAux_supermartingale (q : ℝ) (Z : ℕ → (ℕ → Bool) → ℝ) (j k : ℕ) (ω : ℕ → Bool) :
    q * snellAux q Z j (k + 1) (Function.update ω k true)
      + (1 - q) * snellAux q Z j (k + 1) (Function.update ω k false)
      ≤ snellAux q Z (j + 1) k ω :=
  le_max_right _ _

/-- **Adaptedness clause**: the envelope at time `k` depends only on the first
`k` flips — it is `ℱ_k`-measurable, the filtration content of the Snell
theorem. -/
theorem pathAdaptedAt_snellAux (hZ : ∀ n, PathAdaptedAt n (Z n)) :
    ∀ j k, PathAdaptedAt k (snellAux q Z j k) := by
  intro j
  induction j with
  | zero => exact fun k => hZ k
  | succ j ih =>
    intro k ω ω' hω
    have h_child : ∀ b : Bool,
        snellAux q Z j (k + 1) (Function.update ω k b)
          = snellAux q Z j (k + 1) (Function.update ω' k b) := by
      intro b
      refine ih (k + 1) _ _ fun i hi => ?_
      rcases eq_or_ne i k with rfl | hi'
      · simp
      · rw [Function.update_of_ne hi', Function.update_of_ne hi']
        exact hω i (by omega)
    show max _ _ = max _ _
    rw [hZ k ω ω' hω, h_child true, h_child false]

/-- **Minimality clause (Snell)**: any pathwise supermartingale `U` dominating
the payoff dominates the envelope — over *arbitrary* path-processes, a
strictly larger competitor class than the scalar (Markov) form. Backward
induction: at the horizon the envelope is the payoff; at the step, the
Bellman max is squeezed because `U` beats the payoff directly and beats the
continuation by the inductive hypothesis averaged through the node
(convexity: `q ∈ [0,1]`) plus `U`'s own supermartingale property.
(Adaptedness of `U` is not needed for the bound — only for reading the node
average as a conditional expectation.) -/
theorem snellAux_le_of_supermartingale_of_ge (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hU_super : ∀ k ω, q * U (k + 1) (Function.update ω k true)
        + (1 - q) * U (k + 1) (Function.update ω k false) ≤ U k ω)
    (hU_ge : ∀ k ω, Z k ω ≤ U k ω) :
    ∀ j k ω, snellAux q Z j k ω ≤ U k ω := by
  intro j
  induction j with
  | zero => exact fun k ω => hU_ge k ω
  | succ j ih =>
    intro k ω
    refine max_le (hU_ge k ω) ?_
    calc q * snellAux q Z j (k + 1) (Function.update ω k true)
          + (1 - q) * snellAux q Z j (k + 1) (Function.update ω k false)
        ≤ q * U (k + 1) (Function.update ω k true)
            + (1 - q) * U (k + 1) (Function.update ω k false) :=
          add_le_add (mul_le_mul_of_nonneg_left (ih _ _) hq0)
            (mul_le_mul_of_nonneg_left (ih _ _) (by linarith))
      _ ≤ U k ω := hU_super k ω

/-- **Identification with the scalar Bellman recursion**: for the discounted
intrinsic payoff `Z_n(ω) = e^{−rn}·g(S_n(ω))` and risk-neutral
`q = crrUpProb u d r`, the path-space Snell envelope *is* the discounted
scalar American price:

  `snellAux q Z j k ω = e^{−rk} · americanPrice u d r g j (S_k(ω))`.

Induction on remaining steps; the discount factors recombine
(`e^{−rk}·e^{−r} = e^{−r(k+1)}`) and the positive factor `e^{−rk}` passes
through the Bellman `max`. -/
theorem snellAux_eq_discounted_americanPrice (u d r : ℝ) (g : ℝ → ℝ) (S₀ : ℝ) :
    ∀ j k ω,
      snellAux (crrUpProb u d r)
        (fun n ω => Real.exp (-r * n) * g (spotPath S₀ u d n ω)) j k ω
      = Real.exp (-r * k) * americanPrice u d r g j (spotPath S₀ u d k ω) := by
  intro j
  induction j with
  | zero => intro k ω; rfl
  | succ j ih =>
    intro k ω
    have h_cont : crrUpProb u d r * snellAux (crrUpProb u d r)
          (fun n ω => Real.exp (-r * n) * g (spotPath S₀ u d n ω)) j (k + 1)
          (Function.update ω k true)
        + (1 - crrUpProb u d r) * snellAux (crrUpProb u d r)
          (fun n ω => Real.exp (-r * n) * g (spotPath S₀ u d n ω)) j (k + 1)
          (Function.update ω k false)
        = Real.exp (-r * k) * binomialOptionPriceOnePeriod u d r
            (americanPrice u d r g j (spotPath S₀ u d k ω * u))
            (americanPrice u d r g j (spotPath S₀ u d k ω * d)) := by
      rw [ih (k + 1) (Function.update ω k true), ih (k + 1) (Function.update ω k false),
        spotPath_update_succ_true, spotPath_update_succ_false]
      unfold binomialOptionPriceOnePeriod
      have hexp : Real.exp (-r * ((k : ℕ) + 1 : ℕ))
          = Real.exp (-r * k) * Real.exp (-r) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      ring
    show max _ _ = _
    rw [americanPrice_succ,
      mul_max_of_nonneg _ _ (Real.exp_pos (-r * (k : ℝ))).le]
    exact congrArg₂ max rfl h_cont

/-- **The discounted American price process is a supermartingale** along every
path: for `k < N`, the risk-neutral node-average of the next-step discounted
value is at most the current discounted value —

  `q·X_{k+1}(up) + (1−q)·X_{k+1}(down) ≤ X_k`,  `X_k(ω) = e^{−rk}·V_{N−k}(S_k(ω))`.

This is the genuine path-process, conditional-expectation form behind the
scalar Bellman-max dominance. -/
theorem discounted_americanPrice_supermartingale (u d r : ℝ) (g : ℝ → ℝ) (S₀ : ℝ)
    {N k : ℕ} (hk : k < N) (ω : ℕ → Bool) :
    crrUpProb u d r * (Real.exp (-r * (k + 1 : ℕ)) *
        americanPrice u d r g (N - (k + 1))
          (spotPath S₀ u d (k + 1) (Function.update ω k true)))
      + (1 - crrUpProb u d r) * (Real.exp (-r * (k + 1 : ℕ)) *
        americanPrice u d r g (N - (k + 1))
          (spotPath S₀ u d (k + 1) (Function.update ω k false)))
      ≤ Real.exp (-r * k) * americanPrice u d r g (N - k) (spotPath S₀ u d k ω) := by
  have hjk : N - k = (N - (k + 1)) + 1 := by omega
  calc crrUpProb u d r * (Real.exp (-r * (k + 1 : ℕ)) *
          americanPrice u d r g (N - (k + 1))
            (spotPath S₀ u d (k + 1) (Function.update ω k true)))
        + (1 - crrUpProb u d r) * (Real.exp (-r * (k + 1 : ℕ)) *
          americanPrice u d r g (N - (k + 1))
            (spotPath S₀ u d (k + 1) (Function.update ω k false)))
      = crrUpProb u d r * snellAux (crrUpProb u d r)
            (fun n ω => Real.exp (-r * n) * g (spotPath S₀ u d n ω)) (N - (k + 1)) (k + 1)
            (Function.update ω k true)
          + (1 - crrUpProb u d r) * snellAux (crrUpProb u d r)
            (fun n ω => Real.exp (-r * n) * g (spotPath S₀ u d n ω)) (N - (k + 1)) (k + 1)
            (Function.update ω k false) := by
        rw [snellAux_eq_discounted_americanPrice, snellAux_eq_discounted_americanPrice]
    _ ≤ snellAux (crrUpProb u d r)
          (fun n ω => Real.exp (-r * n) * g (spotPath S₀ u d n ω)) ((N - (k + 1)) + 1) k ω :=
        snellAux_supermartingale _ _ _ _ _
    _ = Real.exp (-r * k) * americanPrice u d r g (N - k) (spotPath S₀ u d k ω) := by
        rw [← hjk, snellAux_eq_discounted_americanPrice]

/-- **The discounted intrinsic payoff is dominated by the American value
process** along every path — the dominance clause of the Snell
characterization, evaluated at the scalar Bellman recursion. -/
theorem discounted_intrinsic_le_americanPrice (u d r : ℝ) (g : ℝ → ℝ) (S₀ : ℝ)
    (N k : ℕ) (ω : ℕ → Bool) :
    Real.exp (-r * k) * g (spotPath S₀ u d k ω)
      ≤ Real.exp (-r * k) * americanPrice u d r g (N - k) (spotPath S₀ u d k ω) := by
  rw [← snellAux_eq_discounted_americanPrice]
  exact snellAux_ge_payoff (crrUpProb u d r)
    (fun n ω => Real.exp (-r * n) * g (spotPath S₀ u d n ω)) (N - k) k ω

/-- **Snell minimality at the American price**: any pathwise supermartingale
`U` (w.r.t. the risk-neutral node average) dominating the discounted intrinsic
payoff dominates the discounted American price along every path. Together with
`discounted_americanPrice_supermartingale` and
`discounted_intrinsic_le_americanPrice`, this characterizes the American value
process as the **smallest supermartingale above the discounted payoff** — the
Snell envelope — over arbitrary path-processes. -/
theorem americanPrice_snell_minimal (u d r : ℝ) (g : ℝ → ℝ) (S₀ : ℝ)
    (hna : BinomialNoArb u d r) {U : ℕ → (ℕ → Bool) → ℝ}
    (hU_super : ∀ (k : ℕ) (ω : ℕ → Bool),
      crrUpProb u d r * U (k + 1) (Function.update ω k true)
        + (1 - crrUpProb u d r) * U (k + 1) (Function.update ω k false) ≤ U k ω)
    (hU_ge : ∀ (k : ℕ) (ω : ℕ → Bool),
      Real.exp (-r * k) * g (spotPath S₀ u d k ω) ≤ U k ω)
    (N k : ℕ) (ω : ℕ → Bool) :
    Real.exp (-r * k) * americanPrice u d r g (N - k) (spotPath S₀ u d k ω) ≤ U k ω := by
  rw [← snellAux_eq_discounted_americanPrice]
  exact snellAux_le_of_supermartingale_of_ge (crrUpProb_mem_Ioo hna).1.le
    (crrUpProb_mem_Ioo hna).2.le hU_super hU_ge _ _ ω

/-- **Adaptedness of the discounted American value process**: the discounted
value at time `k` depends only on the first `k` flips — its
`ℱ_k`-measurability, the filtration clause of the Snell characterization at
the American price. -/
lemma pathAdaptedAt_discounted_americanPrice (u d r : ℝ) (g : ℝ → ℝ) (S₀ : ℝ)
    (N k : ℕ) :
    PathAdaptedAt k (fun ω => Real.exp (-r * k) *
      americanPrice u d r g (N - k) (spotPath S₀ u d k ω)) := fun ω ω' h => by
  show Real.exp (-r * k) * americanPrice u d r g (N - k) (spotPath S₀ u d k ω)
      = Real.exp (-r * k) * americanPrice u d r g (N - k) (spotPath S₀ u d k ω')
  rw [pathAdaptedAt_spotPath S₀ u d k ω ω' h]

end MathFin
