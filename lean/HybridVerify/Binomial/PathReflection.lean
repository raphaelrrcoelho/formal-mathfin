/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Path-level reflection identity for ±1 walks (André 1887, algebraic core)

For paths `ω : Fin n → Bool` (each entry: `+1` if `true`, `−1` if `false`),
**reflection after time `τ`** is the path that agrees with `ω` strictly
before time `τ` and *negates* every step from time `τ` onwards.

The algebraic core of André's reflection principle is the position identity

  **For any `τ ≤ k`,**
    `walkPos (reflectAfter τ ω) k = 2 · walkPos ω τ − walkPos ω k`.

Equivalently: the trajectory after time `τ` of the reflected path is the
mirror image of the original trajectory through the horizontal line at
height `walkPos ω τ`.

Combined with a hitting-time argument (the first `τ` with `walkPos ω τ = a`
when `ω` reaches level `a`), this identity yields the bijection between
*paths that touch level `a` and end at `b ≤ a`* and *paths that end at
`2a − b`*. That bijection is the counting backbone of barrier-option
pricing in the binomial tree.

This file formalises the algebraic core (the path-position identity and
involution); the hitting-time bijection is downstream work.

## Why this is more than algebra

The identity is non-trivial because reflection *changes* the path at every
position from `τ` onwards. The proof requires splitting each path sum into
a prefix (`< τ`) — preserved by reflection — and a suffix (`τ ≤ · < k`) —
negated step-by-step by reflection. The prefix contributes `walkPos ω τ`
to both sides, and the suffix-sign-flip is what produces the
`2 · walkPos ω τ − walkPos ω k` form.

## Results

* `walkStep`: step value (`+1`/`−1` from a Boolean).
* `walkPos`: position of the walk at time `k`.
* `reflectAfter`: flip every step at index `≥ τ`.
* `reflectAfter_involutive`: reflection at fixed `τ` is its own inverse.
* `walkPos_reflectAfter_le`: positions at `k ≤ τ` are unchanged.
* `walkPos_reflectAfter_ge`: positions at `k ≥ τ` reflect through
  `walkPos ω τ`.
* `walkPos_reflectAfter_endpoint`: endpoint statement: if the original
  hits `a` at `τ` and ends at `b`, the reflected ends at `2a − b`.
-/

namespace HybridVerify

variable {n : ℕ}

/-- Step value: `+1` if `true` (up), `−1` if `false` (down). -/
def walkStep (b : Bool) : ℤ := if b then 1 else -1

/-- **Step-value negation under boolean flip**: `walkStep !b = -walkStep b`. -/
lemma walkStep_not (b : Bool) : walkStep (!b) = -walkStep b := by
  unfold walkStep
  cases b <;> simp

/-- Position of the walk at time `k`: sum of the first `k` steps.

For `k = 0` the sum is empty and the position is `0`. For `k ≥ n` all
steps are included. -/
def walkPos (ω : Fin n → Bool) (k : ℕ) : ℤ :=
  ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun (i : Fin n) => i.val < k),
    walkStep (ω i)

@[simp]
lemma walkPos_zero (ω : Fin n → Bool) : walkPos ω 0 = 0 := by
  unfold walkPos
  simp

/-- **Reflection after time `τ`**: flip every step at index `≥ τ`. -/
def reflectAfter (τ : ℕ) (ω : Fin n → Bool) : Fin n → Bool :=
  fun (i : Fin n) => if i.val < τ then ω i else !(ω i)

/-- **Reflection at fixed `τ` is involutive**: applying it twice recovers the
original path. -/
lemma reflectAfter_involutive (τ : ℕ) :
    Function.Involutive (reflectAfter τ : (Fin n → Bool) → Fin n → Bool) := by
  intro ω
  funext i
  unfold reflectAfter
  by_cases h : i.val < τ
  · simp [h]
  · simp [h]

/-- **Positions before `τ` are unchanged**: for `k ≤ τ`, the reflected walk's
position equals the original's. (The flip only takes effect from index `τ`
onwards.) -/
lemma walkPos_reflectAfter_le (τ : ℕ) (ω : Fin n → Bool) {k : ℕ} (hk : k ≤ τ) :
    walkPos (reflectAfter τ ω) k = walkPos ω k := by
  unfold walkPos
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter] at hi
  have h_i_lt_τ : i.val < τ := lt_of_lt_of_le hi.2 hk
  unfold reflectAfter
  rw [if_pos h_i_lt_τ]

/-- **Position-reflection identity** (the algebraic core of André's principle).

For any `τ ≤ k`:

  `walkPos (reflectAfter τ ω) k = 2 · walkPos ω τ − walkPos ω k`.

Proof: decompose each path sum into the prefix `{i.val < τ}` (preserved by
reflection, contributing `walkPos ω τ`) and the suffix `{τ ≤ i.val < k}`
(negated step-by-step by reflection). Combining

  `walkPos (reflect) k = (prefix) − (suffix of ω)`
  `walkPos ω k         = (prefix) + (suffix of ω)`
  `walkPos ω τ         = (prefix)`

gives `walkPos (reflect) k = 2·walkPos ω τ − walkPos ω k`. -/
lemma walkPos_reflectAfter_ge (τ : ℕ) (ω : Fin n → Bool) {k : ℕ} (hτk : τ ≤ k) :
    walkPos (reflectAfter τ ω) k = 2 * walkPos ω τ - walkPos ω k := by
  let Pτ : Finset (Fin n) := Finset.univ.filter (fun (i : Fin n) => i.val < τ)
  let Pτk : Finset (Fin n) :=
    Finset.univ.filter (fun (i : Fin n) => τ ≤ i.val ∧ i.val < k)
  let Pk : Finset (Fin n) := Finset.univ.filter (fun (i : Fin n) => i.val < k)
  have h_disj : Disjoint Pτ Pτk := by
    rw [Finset.disjoint_filter]
    intros i _ hi1 hi2
    exact absurd hi1 (not_lt.mpr hi2.1)
  have h_union : Pk = Pτ ∪ Pτk := by
    ext i
    simp only [Pk, Pτ, Pτk, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨_, h_ik⟩
      by_cases h_iτ : i.val < τ
      · exact Or.inl ⟨Finset.mem_univ _, h_iτ⟩
      · exact Or.inr ⟨Finset.mem_univ _, not_lt.mp h_iτ, h_ik⟩
    · rintro (⟨_, h1⟩ | ⟨_, h2, h3⟩)
      · exact ⟨Finset.mem_univ _, lt_of_lt_of_le h1 hτk⟩
      · exact ⟨Finset.mem_univ _, h3⟩
  have h_split_σ : walkPos (reflectAfter τ ω) k =
      (∑ i ∈ Pτ, walkStep (reflectAfter τ ω i)) +
      (∑ i ∈ Pτk, walkStep (reflectAfter τ ω i)) := by
    unfold walkPos
    show ∑ i ∈ Pk, walkStep (reflectAfter τ ω i) = _
    rw [h_union, Finset.sum_union h_disj]
  have h_split_ω : walkPos ω k =
      (∑ i ∈ Pτ, walkStep (ω i)) + (∑ i ∈ Pτk, walkStep (ω i)) := by
    unfold walkPos
    show ∑ i ∈ Pk, walkStep (ω i) = _
    rw [h_union, Finset.sum_union h_disj]
  have h_τ_eq : walkPos ω τ = ∑ i ∈ Pτ, walkStep (ω i) := rfl
  have h_prefix :
      (∑ i ∈ Pτ, walkStep (reflectAfter τ ω i)) = ∑ i ∈ Pτ, walkStep (ω i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pτ, Finset.mem_filter] at hi
    unfold reflectAfter
    rw [if_pos hi.2]
  have h_suffix :
      (∑ i ∈ Pτk, walkStep (reflectAfter τ ω i)) = -∑ i ∈ Pτk, walkStep (ω i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pτk, Finset.mem_filter] at hi
    unfold reflectAfter
    rw [if_neg (not_lt.mpr hi.2.1), walkStep_not]
  rw [h_split_σ, h_prefix, h_suffix, h_split_ω, h_τ_eq]
  ring

/-- **Endpoint statement of the reflection identity**: if `ω` hits level `a` at
time `τ` (`walkPos ω τ = a`) and ends at `b` (`walkPos ω n = b`), then the
reflected path ends at `2a − b`.

This statement drives the counting argument in barrier-option pricing: a
path-to-`b`-touching-`a` and a path-to-`(2a−b)` are in bijection via
reflection at the first hitting time of `a`. -/
theorem walkPos_reflectAfter_endpoint (τ : ℕ) (ω : Fin n → Bool) (hτ : τ ≤ n)
    (a b : ℤ) (h_hit : walkPos ω τ = a) (h_end : walkPos ω n = b) :
    walkPos (reflectAfter τ ω) n = 2 * a - b := by
  rw [walkPos_reflectAfter_ge τ ω hτ, h_hit, h_end]

end HybridVerify
