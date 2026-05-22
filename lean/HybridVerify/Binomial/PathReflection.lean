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

/-! ## Hitting time and the counting bijection

The reflection identity above is the algebraic spine. To turn it into a
counting statement we choose a canonical `τ` — the **first time** the walk
hits a given level `a` — and reflect there. The bijection is then between
paths that hit `a` and end at one level and paths that hit `a` and end at
its mirror image.

The construction:

1. `hittingSet ω a`: the (finite) set of times `k ∈ {0,…,n}` with
   `walkPos ω k = a`.
2. `HitsLevel`: the predicate that `hittingSet` is nonempty.
3. `firstHit ω a h`: the smallest hit time on a hit-path.
4. `reflectAtFirstHit a`: the partial map `ω ↦ reflectAfter (firstHit ω a h) ω`
   (defaulting to identity when `ω` doesn't hit `a`).
5. **Key invariance**: `firstHit (reflectAtFirstHit ω) a = firstHit ω a`,
   because reflection preserves positions on `[0, τ]`, hence both hits at τ
   (and doesn't hit earlier).
6. **Involution**: applying reflection twice at the same `τ` is identity,
   so `reflectAtFirstHit` is an involution on `{ω : HitsLevel ω a}`.
7. **Endpoint flip**: combining with `walkPos_reflectAfter_endpoint`,
   reflection maps `{ω : hits a, ends at b}` to
   `{ω : hits a, ends at 2a − b}` bijectively.
-/

variable {a : ℤ}

/-- The (finite) set of times `k ∈ {0, …, n}` at which the walk hits level `a`. -/
def hittingSet (ω : Fin n → Bool) (a : ℤ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k => walkPos ω k = a)

/-- A path **hits level `a`** if `hittingSet` is nonempty. -/
abbrev HitsLevel (a : ℤ) (ω : Fin n → Bool) : Prop := (hittingSet ω a).Nonempty

/-- First hitting time of level `a` on a hit-path. -/
noncomputable def firstHit (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω) : ℕ :=
  (hittingSet ω a).min' h

lemma firstHit_mem_hittingSet (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω) :
    firstHit ω a h ∈ hittingSet ω a :=
  (hittingSet ω a).min'_mem h

lemma firstHit_le (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω) :
    firstHit ω a h ≤ n := by
  have h_lt : firstHit ω a h < n + 1 :=
    Finset.mem_range.mp (Finset.mem_filter.mp (firstHit_mem_hittingSet ω a h)).1
  omega

lemma walkPos_firstHit (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω) :
    walkPos ω (firstHit ω a h) = a :=
  (Finset.mem_filter.mp (firstHit_mem_hittingSet ω a h)).2

/-- **Minimality of the first hit**: any `k ≤ n` with `walkPos ω k = a` is at
least `firstHit ω a`. -/
lemma firstHit_le_of_hit (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω)
    {k : ℕ} (hk : k ≤ n) (h_eq : walkPos ω k = a) : firstHit ω a h ≤ k := by
  apply Finset.min'_le
  rw [hittingSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, h_eq⟩

/-- **Reflected path hits level `a`** when the original does. The reflected
hits at the same `firstHit` time (proven separately below). -/
lemma HitsLevel.reflectAfter_firstHit (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω) :
    HitsLevel a (reflectAfter (firstHit ω a h) ω) := by
  refine ⟨firstHit ω a h, ?_⟩
  unfold hittingSet
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨by have := firstHit_le ω a h; omega, ?_⟩
  rw [walkPos_reflectAfter_le _ _ (le_refl _)]
  exact walkPos_firstHit ω a h

/-- **First hit is invariant under reflection at the first hit time.** Crucial
for the involution property of `reflectAtFirstHit`.

Proof: both bounds.
* `firstHit σ a ≤ τ` because `σ` hits `a` at `τ` (positions agree up to `τ`).
* `firstHit σ a ≥ τ` because positions on `[0, τ)` agree with `ω`, where `ω`
  doesn't hit `a` (minimality of `τ`). -/
theorem firstHit_reflectAfter_firstHit (ω : Fin n → Bool) (a : ℤ) (h : HitsLevel a ω) :
    firstHit (reflectAfter (firstHit ω a h) ω) a
        (HitsLevel.reflectAfter_firstHit ω a h) = firstHit ω a h := by
  let hσ := HitsLevel.reflectAfter_firstHit ω a h
  apply le_antisymm
  · -- τσ ≤ τ: σ hits a at τ (positions agree up to τ).
    apply firstHit_le_of_hit _ a hσ (firstHit_le ω a h)
    rw [walkPos_reflectAfter_le _ _ (le_refl _)]
    exact walkPos_firstHit ω a h
  · -- τ ≤ τσ: if τσ < τ, positions agree there with ω; ω doesn't hit a before τ.
    by_contra h_ge_not
    have h_lt : firstHit (reflectAfter (firstHit ω a h) ω) a hσ < firstHit ω a h :=
      not_le.mp h_ge_not
    have h_τσ_le_n : firstHit (reflectAfter (firstHit ω a h) ω) a hσ ≤ n :=
      firstHit_le _ _ _
    have h_walkPos_σ :
        walkPos (reflectAfter (firstHit ω a h) ω)
            (firstHit (reflectAfter (firstHit ω a h) ω) a hσ) = a :=
      walkPos_firstHit _ _ _
    have h_walkPos_ω :
        walkPos ω (firstHit (reflectAfter (firstHit ω a h) ω) a hσ) = a := by
      rw [← walkPos_reflectAfter_le (firstHit ω a h) ω (le_of_lt h_lt)]
      exact h_walkPos_σ
    have h_ge : firstHit ω a h ≤ firstHit (reflectAfter (firstHit ω a h) ω) a hσ :=
      firstHit_le_of_hit ω a h h_τσ_le_n h_walkPos_ω
    exact absurd h_ge (not_le.mpr h_lt)

/-- **Reflection at the first hitting time of `a`**: the path-level map that
reflects every step after `firstHit ω a`. Defaulted to identity off the
hit-set. -/
noncomputable def reflectAtFirstHit (a : ℤ) (ω : Fin n → Bool) : Fin n → Bool :=
  if h : HitsLevel a ω then reflectAfter (firstHit ω a h) ω else ω

/-- **Involution**: reflecting twice at the (preserved) first hit recovers
the original path.

Proof: on the hit-set, `firstHit` is invariant under reflection
(`firstHit_reflectAfter_firstHit`), and `reflectAfter τ` is involutive
(`reflectAfter_involutive`). Off the hit-set, the map is identity. -/
theorem reflectAtFirstHit_involutive (a : ℤ) :
    Function.Involutive (reflectAtFirstHit (n := n) a) := by
  intro ω
  by_cases h1 : HitsLevel a ω
  · -- ω hits a.
    have h2 : HitsLevel a (reflectAfter (firstHit ω a h1) ω) :=
      HitsLevel.reflectAfter_firstHit ω a h1
    have h_τ_eq : firstHit (reflectAfter (firstHit ω a h1) ω) a h2 = firstHit ω a h1 :=
      firstHit_reflectAfter_firstHit ω a h1
    show reflectAtFirstHit a (reflectAtFirstHit a ω) = ω
    unfold reflectAtFirstHit
    rw [dif_pos h1]
    rw [dif_pos h2]
    rw [h_τ_eq]
    exact reflectAfter_involutive (firstHit ω a h1) ω
  · -- ω doesn't hit a; reflectAtFirstHit acts as identity.
    show reflectAtFirstHit a (reflectAtFirstHit a ω) = ω
    unfold reflectAtFirstHit
    rw [dif_neg h1, dif_neg h1]

/-- **Endpoint flip under reflection at first hit**: if `ω` hits `a` and ends
at `b`, then `reflectAtFirstHit a ω` ends at `2a − b`. -/
theorem walkPos_reflectAtFirstHit_endpoint (ω : Fin n → Bool) (a b : ℤ)
    (h : HitsLevel a ω) (h_end : walkPos ω n = b) :
    walkPos (reflectAtFirstHit a ω) n = 2 * a - b := by
  unfold reflectAtFirstHit
  rw [dif_pos h]
  exact walkPos_reflectAfter_endpoint (firstHit ω a h) ω (firstHit_le ω a h)
    a b (walkPos_firstHit ω a h) h_end

/-- **The reflection-principle bijection** (André 1887, counting form).

For any `a, b : ℤ`, the set of paths that hit level `a` and end at `b` is in
bijection with the set of paths that hit level `a` and end at `2a − b`,
via `reflectAtFirstHit a`.

The bijection is an involution (when applied twice, recovers the original
path). -/
noncomputable def reflectionPrincipleEquiv (a b : ℤ) :
    {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n = b} ≃
    {ω : Fin n → Bool // HitsLevel a ω ∧ walkPos ω n = 2 * a - b} where
  toFun ω :=
    ⟨reflectAtFirstHit a ω.val,
     by
       constructor
       · -- Reflected hits a.
         unfold reflectAtFirstHit
         rw [dif_pos ω.property.1]
         exact HitsLevel.reflectAfter_firstHit ω.val a ω.property.1
       · exact walkPos_reflectAtFirstHit_endpoint ω.val a b ω.property.1 ω.property.2⟩
  invFun ω :=
    ⟨reflectAtFirstHit a ω.val,
     by
       constructor
       · unfold reflectAtFirstHit
         rw [dif_pos ω.property.1]
         exact HitsLevel.reflectAfter_firstHit ω.val a ω.property.1
       · -- Reflected ends at 2a - (2a - b) = b.
         have h := walkPos_reflectAtFirstHit_endpoint ω.val a (2 * a - b)
           ω.property.1 ω.property.2
         linarith⟩
  left_inv ω := Subtype.ext (reflectAtFirstHit_involutive a ω.val)
  right_inv ω := Subtype.ext (reflectAtFirstHit_involutive a ω.val)

end HybridVerify
