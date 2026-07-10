/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Foundations.GirsanovSimpleTheta
public import MathFin.Foundations.AdaptedProcessToLp
public import MathFin.Foundations.ItoIntegralProcess
public import MathFin.Foundations.ItoIntegralRiemannBridgeAdapted

/-! # Marshalling a `SimpleProcess` into single-partition `(s,c)` form (Girsanov Rung 1, Route B)

The simple-θ Girsanov theorem `MathFin.isExpQMartingale_BthetaSimple` consumes a **single monotone
partition** `s : ℕ → ℝ≥0` with `𝓕_{s i}`-measurable multipliers `c : ℕ → Ω → ℝ`. The Itô-integral
density family (`ItoIntegralL2.simpleAssembly`, dense by `simpleAssembly_T_denseRange`) is indexed by
`ProbabilityTheory.SimpleProcess`, whose `value : (ℝ≥0 × ℝ≥0) →₀ (Ω → ℝ)` is a `Finsupp` over
**arbitrary overlapping intervals**. This file marshals the latter into the former: sort all interval
endpoints into a common partition, and read the per-cell multiplier off the process value.

The payoff (downstream): a bounded predictable θ is approximated in `L²` by clamped simple processes
`Vⁿ` (free from `simpleAssembly_T_denseRange` + `clampSP`), each marshalled to `(sⁿ, cⁿ)`, so the
simple exponential-martingale identity passes to the limit exactly as in the continuous-adapted case.

This module builds the partition side first: the endpoint set and the monotone partition `marshalPart`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology NNReal
open scoped NNReal ENNReal
open ItoIntegralL2 ItoIntegralProcess ItoIntegralCLM ItoIsometryAdapted ItoIntegralBrownian
open ItoIntegralRiemannBridge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

/-- The finite set of cell boundaries of a simple process on `[0,T]`: `0`, `T`, and every endpoint
of every interval in the `value` support. -/
noncomputable def marshalEndpoints (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) : Finset ℝ≥0 :=
  insert 0 (insert T (V.value.support.image Prod.fst ∪ V.value.support.image Prod.snd))

/-- `0` is always a cell boundary. -/
lemma zero_mem_marshalEndpoints (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    (0 : ℝ≥0) ∈ marshalEndpoints hBmeas T V := Finset.mem_insert_self _ _

/-- `T` is always a cell boundary. -/
lemma T_mem_marshalEndpoints (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    T ∈ marshalEndpoints hBmeas T V :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- The endpoint set is nonempty (it contains `0`). -/
lemma marshalEndpoints_nonempty (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    (marshalEndpoints hBmeas T V).Nonempty :=
  ⟨0, zero_mem_marshalEndpoints hBmeas T V⟩

/-- **Every cell boundary is `≤ T`.** `0 ≤ T`; `T ≤ T`; a left endpoint `p.1 ≤ p.2 ≤ T`; a right
endpoint `p.2 ≤ T` — the last two using the clamp hypothesis `hle` and `V.le_of_mem_support_value`. -/
lemma marshalEndpoints_le_T (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas))
    (hle : ∀ p ∈ V.value.support, p.2 ≤ T) :
    ∀ x ∈ marshalEndpoints hBmeas T V, x ≤ T := by
  intro x hx
  simp only [marshalEndpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
  rcases hx with rfl | rfl | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact zero_le
  · exact le_refl _
  · exact (V.le_of_mem_support_value p hp).trans (hle p hp)
  · exact hle p hp

/-- The monotone partition read off the sorted endpoint set: the `i`-th smallest boundary for
`i < card`, clamped to `T` beyond. This is the `s : ℕ → ℝ≥0` fed to `isExpQMartingale_BthetaSimple`. -/
noncomputable def marshalPart (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (i : ℕ) : ℝ≥0 :=
  if h : i < (marshalEndpoints hBmeas T V).card then
    (marshalEndpoints hBmeas T V).orderEmbOfFin rfl ⟨i, h⟩
  else T

/-- `marshalPart` is monotone: within the enumerated range by `orderEmbOfFin`'s monotonicity, and
constant `= T` beyond (`T` is the maximum, since every interval endpoint is `≤ T` after clamping and
`T` itself is a boundary). -/
lemma marshalPart_mono (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas))
    (hle : ∀ p ∈ V.value.support, p.2 ≤ T) :
    Monotone (marshalPart hBmeas T V) := by
  have hE := marshalEndpoints_le_T hBmeas T V hle
  intro i j hij
  unfold marshalPart
  split_ifs with hi hj hj
  · exact ((marshalEndpoints hBmeas T V).orderEmbOfFin rfl).monotone (Fin.mk_le_mk.mpr hij)
  · exact hE _ (Finset.orderEmbOfFin_mem _ _ _)
  · omega
  · exact le_refl _

/-- The per-cell multiplier: on cell `(marshalPart i, marshalPart (i+1)]`, the sum of the values of
every interval in `V.value` that **covers** the cell (`p.1 ≤ sᵢ` and `sᵢ₊₁ ≤ p.2`). This is the
`c : ℕ → Ω → ℝ` fed to `isExpQMartingale_BthetaSimple`. The covering test is deterministic (no `ω`),
so measurability/boundedness reduce to those of the finitely many covering values. -/
noncomputable def marshalMult (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (i : ℕ) (ω : Ω) : ℝ :=
  ∑ p ∈ V.value.support,
    (if p.1 ≤ marshalPart hBmeas T V i ∧ marshalPart hBmeas T V (i + 1) ≤ p.2
      then V.value p ω else 0)

/-- **The multiplier is adapted at the cell's left endpoint.** Each covering value `V.value p` is
`𝓕_{p.1}`-measurable, and covering forces `p.1 ≤ sᵢ`, so it is `𝓕_{sᵢ}`-measurable; the finite sum
stays `𝓕_{sᵢ}`-measurable. This is the `hc` hypothesis of `isExpQMartingale_BthetaSimple`. -/
lemma stronglyMeasurable_marshalMult (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (i : ℕ) :
    StronglyMeasurable[(natFiltration hBmeas (marshalPart hBmeas T V i) : MeasurableSpace Ω)]
      (marshalMult hBmeas T V i) := by
  unfold marshalMult
  refine Finset.stronglyMeasurable_fun_sum _ (fun p _ => ?_)
  by_cases hcond : p.1 ≤ marshalPart hBmeas T V i ∧ marshalPart hBmeas T V (i + 1) ≤ p.2
  · simp only [hcond]
    exact ((V.measurable_value p).mono ((natFiltration hBmeas).mono hcond.1)
      le_rfl).stronglyMeasurable
  · simp only [hcond]
    exact stronglyMeasurable_const

/-- Consecutive enumerated cells are strictly increasing (`orderEmbOfFin` is strictly monotone). -/
lemma marshalPart_lt (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) {i : ℕ}
    (hi : i + 1 < (marshalEndpoints hBmeas T V).card) :
    marshalPart hBmeas T V i < marshalPart hBmeas T V (i + 1) := by
  have hi' : i < (marshalEndpoints hBmeas T V).card := by omega
  rw [marshalPart, dif_pos hi', marshalPart, dif_pos hi]
  exact ((marshalEndpoints hBmeas T V).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (by omega))

/-- **Consecutiveness.** Within an enumerated cell `(sᵢ, sᵢ₊₁]` there is no other boundary: every
endpoint is `≤ sᵢ` or `≥ sᵢ₊₁`. Since `orderEmbOfFin` enumerates *all* of `marshalEndpoints` in
order, any endpoint is some `marshalPart k`, and `k ≤ i` or `i+1 ≤ k`. -/
lemma marshalEndpoints_consecutive (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas))
    (hle : ∀ p ∈ V.value.support, p.2 ≤ T) {i : ℕ}
    {x : ℝ≥0} (hx : x ∈ marshalEndpoints hBmeas T V) :
    x ≤ marshalPart hBmeas T V i ∨ marshalPart hBmeas T V (i + 1) ≤ x := by
  rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (marshalEndpoints hBmeas T V) rfl] at hx
  obtain ⟨k, hk⟩ := hx
  have hxk : marshalPart hBmeas T V k.val = x := by
    rw [marshalPart, dif_pos k.isLt]; exact hk
  rcases le_or_gt k.val i with h | h
  · exact Or.inl (hxk ▸ marshalPart_mono hBmeas T V hle h)
  · exact Or.inr (hxk ▸ marshalPart_mono hBmeas T V hle h)

/-- Every left endpoint of a support interval is a cell boundary. -/
lemma fst_mem_marshalEndpoints (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) {p : ℝ≥0 × ℝ≥0}
    (hp : p ∈ V.value.support) : p.1 ∈ marshalEndpoints hBmeas T V := by
  simp only [marshalEndpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))

/-- Every right endpoint of a support interval is a cell boundary. -/
lemma snd_mem_marshalEndpoints (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) {p : ℝ≥0 × ℝ≥0}
    (hp : p ∈ V.value.support) : p.2 ∈ marshalEndpoints hBmeas T V := by
  simp only [marshalEndpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr (Or.inr ⟨p, hp, rfl⟩))

/-- **Cell membership ↔ covering.** For a point `t` in the enumerated cell `(sᵢ, sᵢ₊₁]`, and an
interval `(p.1, p.2]` of the support, `t ∈ (p.1, p.2]` exactly when the interval covers the whole
cell (`p.1 ≤ sᵢ` and `sᵢ₊₁ ≤ p.2`). The `←` is monotonicity; the `→` uses consecutiveness (no
boundary strictly inside the cell) applied to the endpoints `p.1`, `p.2`. -/
lemma mem_Ioc_iff_cover (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {i : ℕ} {t : ℝ≥0} (ht1 : marshalPart hBmeas T V i < t)
    (ht2 : t ≤ marshalPart hBmeas T V (i + 1)) {p : ℝ≥0 × ℝ≥0} (hp : p ∈ V.value.support) :
    t ∈ Set.Ioc p.1 p.2 ↔
      (p.1 ≤ marshalPart hBmeas T V i ∧ marshalPart hBmeas T V (i + 1) ≤ p.2) := by
  constructor
  · rintro ⟨htp1, htp2⟩
    refine ⟨?_, ?_⟩
    · rcases marshalEndpoints_consecutive hBmeas T V hle (i := i)
        (fst_mem_marshalEndpoints hBmeas T V hp) with h | h
      · exact h
      · exact absurd ((h.trans_lt htp1).trans_le ht2) (lt_irrefl _)
    · rcases marshalEndpoints_consecutive hBmeas T V hle (i := i)
        (snd_mem_marshalEndpoints hBmeas T V hp) with h | h
      · exact absurd (h.trans_lt (ht1.trans_le htp2)) (lt_irrefl _)
      · exact h
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans_lt ht1, ht2.trans h2⟩

/-- On the enumerated range the partition is order-reflecting: `sₐ ≤ sᵢ ↔ a ≤ i`. -/
lemma marshalPart_le_iff (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) {a i : ℕ}
    (ha : a < (marshalEndpoints hBmeas T V).card) (hi : i < (marshalEndpoints hBmeas T V).card) :
    marshalPart hBmeas T V a ≤ marshalPart hBmeas T V i ↔ a ≤ i := by
  rw [marshalPart, dif_pos ha, marshalPart, dif_pos hi,
    ((marshalEndpoints hBmeas T V).orderEmbOfFin rfl).le_iff_le]
  exact Fin.mk_le_mk

/-- Every cell boundary is realized: `x ∈ marshalEndpoints → x = marshalPart k` for some `k < card`. -/
lemma exists_marshalPart_eq (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) {x : ℝ≥0}
    (hx : x ∈ marshalEndpoints hBmeas T V) :
    ∃ k, k < (marshalEndpoints hBmeas T V).card ∧ marshalPart hBmeas T V k = x := by
  rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (marshalEndpoints hBmeas T V) rfl] at hx
  obtain ⟨k, hk⟩ := hx
  exact ⟨k.val, k.isLt, by rw [marshalPart, dif_pos k.isLt]; exact hk⟩

/-- **Telescoping over covering cells (general endpoint function `F`).** For a support interval
`(p.1, p.2]` (its endpoints are cell boundaries), summing `F(sᵢ₊₁) − F(sᵢ)` over exactly the cells
`i < N` the interval covers yields `F(p.2) − F(p.1)`: the covering cells are the block `Ico a b`
where `sₐ = p.1`, `s_b = p.2`, and the block telescopes. Instantiated with `F = B(·)ω` for the
stochastic exponent and `F = min · u` for the drift. -/
lemma telescope_cover (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas))
    {p : ℝ≥0 × ℝ≥0} (hp : p ∈ V.value.support) (F : ℝ≥0 → ℝ)
    {N : ℕ} (hN : N + 1 = (marshalEndpoints hBmeas T V).card) :
    ∑ i ∈ Finset.range N,
      (if p.1 ≤ marshalPart hBmeas T V i ∧ marshalPart hBmeas T V (i + 1) ≤ p.2
        then F (marshalPart hBmeas T V (i + 1)) - F (marshalPart hBmeas T V i) else 0)
      = F p.2 - F p.1 := by
  classical
  obtain ⟨a, ha, ha_eq⟩ := exists_marshalPart_eq hBmeas T V (fst_mem_marshalEndpoints hBmeas T V hp)
  obtain ⟨b, hb, hb_eq⟩ := exists_marshalPart_eq hBmeas T V (snd_mem_marshalEndpoints hBmeas T V hp)
  have hab : a ≤ b := by
    rw [← marshalPart_le_iff hBmeas T V ha hb, ha_eq, hb_eq]
    exact V.le_of_mem_support_value p hp
  rw [← ha_eq, ← hb_eq, ← Finset.sum_filter]
  have hset : ((Finset.range N).filter
      (fun i => marshalPart hBmeas T V a ≤ marshalPart hBmeas T V i ∧
        marshalPart hBmeas T V (i + 1) ≤ marshalPart hBmeas T V b)) = Finset.Ico a b := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hiN, hai, hib⟩
      have hi_card : i < (marshalEndpoints hBmeas T V).card := by omega
      have hi1_card : i + 1 < (marshalEndpoints hBmeas T V).card := by omega
      rw [marshalPart_le_iff hBmeas T V ha hi_card] at hai
      rw [marshalPart_le_iff hBmeas T V hi1_card hb] at hib
      exact ⟨hai, by omega⟩
    · rintro ⟨hai, hib⟩
      have hi_card : i < (marshalEndpoints hBmeas T V).card := by omega
      have hi1_card : i + 1 < (marshalEndpoints hBmeas T V).card := by omega
      refine ⟨by omega, ?_, ?_⟩
      · rw [marshalPart_le_iff hBmeas T V ha hi_card]; exact hai
      · rw [marshalPart_le_iff hBmeas T V hi1_card hb]; omega
  rw [hset, Finset.sum_Ico_eq_sub _ hab,
    Finset.sum_range_sub (fun i => F (marshalPart hBmeas T V i)) b,
    Finset.sum_range_sub (fun i => F (marshalPart hBmeas T V i)) a]
  ring

/-- **The marshalled stochastic exponent equals the elementary Itô integral of `V`.** Over the
enumerated partition, the per-cell multiplier weighted by the Brownian increment reproduces
`itoSimpleProcess V T`. Proof: expand `marshalMult`, distribute, `sum_comm`, then `telescope_cover`
per interval. Needs the clamp `hle` so the `min · T` in `itoSimpleProcess_apply` drops. -/
lemma marshalStochExp_eq (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    (ω : Ω) {N : ℕ} (hN : N + 1 = (marshalEndpoints hBmeas T V).card) :
    ∑ i ∈ Finset.range N, marshalMult hBmeas T V i ω *
        (B (marshalPart hBmeas T V (i + 1)) ω - B (marshalPart hBmeas T V i) ω)
      = itoSimpleProcess hBmeas V T ω := by
  rw [itoSimpleProcess_apply, Finsupp.sum]
  have hRHS : ∀ p ∈ V.value.support, V.value p ω * (B (min p.2 T) ω - B (min p.1 T) ω)
      = V.value p ω * (B p.2 ω - B p.1 ω) := fun p hp => by
    rw [min_eq_left (hle p hp), min_eq_left ((V.le_of_mem_support_value p hp).trans (hle p hp))]
  rw [Finset.sum_congr rfl hRHS]
  simp only [marshalMult, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [← telescope_cover hBmeas T V hp (fun x => B x ω) hN, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hc : p.1 ≤ marshalPart hBmeas T V i ∧ marshalPart hBmeas T V (i + 1) ≤ p.2
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, zero_mul, mul_zero]

/-- The partition starts at `0` (the least boundary). -/
lemma marshalPart_zero (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T) :
    marshalPart hBmeas T V 0 = 0 := by
  refine le_antisymm ?_ zero_le
  obtain ⟨k, _, hk⟩ := exists_marshalPart_eq hBmeas T V (zero_mem_marshalEndpoints hBmeas T V)
  calc marshalPart hBmeas T V 0
      ≤ marshalPart hBmeas T V k := marshalPart_mono hBmeas T V hle (Nat.zero_le k)
    _ = 0 := hk

/-- Every partition point is `≤ T`. -/
lemma marshalPart_le_T (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    (i : ℕ) : marshalPart hBmeas T V i ≤ T := by
  by_cases h : i < (marshalEndpoints hBmeas T V).card
  · rw [marshalPart, dif_pos h]
    exact marshalEndpoints_le_T hBmeas T V hle _ (Finset.orderEmbOfFin_mem _ _ _)
  · exact le_of_eq (by rw [marshalPart, dif_neg h])

/-- **Coverage.** The last enumerated cell boundary is `T` (`T` is the maximum, since every endpoint
is `≤ T`). Taking `N = card − 1` gives `marshalPart N = T`, so the partition covers `[0, T]`. -/
lemma marshalPart_card_sub_one (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T) :
    marshalPart hBmeas T V ((marshalEndpoints hBmeas T V).card - 1) = T := by
  have hpos : 0 < (marshalEndpoints hBmeas T V).card :=
    Finset.card_pos.mpr (marshalEndpoints_nonempty hBmeas T V)
  refine le_antisymm ?_ ?_
  · have hlt : (marshalEndpoints hBmeas T V).card - 1 < (marshalEndpoints hBmeas T V).card := by omega
    rw [marshalPart, dif_pos hlt]
    exact marshalEndpoints_le_T hBmeas T V hle _ (Finset.orderEmbOfFin_mem _ _ _)
  · obtain ⟨k, hk_card, hk⟩ := exists_marshalPart_eq hBmeas T V (T_mem_marshalEndpoints hBmeas T V)
    calc T = marshalPart hBmeas T V k := hk.symm
      _ ≤ marshalPart hBmeas T V ((marshalEndpoints hBmeas T V).card - 1) :=
          marshalPart_mono hBmeas T V hle (by omega)

/-- **The marshalled drift equals the elementary drift of `V`.** `simpleDrift` over the enumerated
partition with the per-cell multipliers reproduces `∑_p V(p)·(p.2∧u − p.1∧u)` — the pathwise
time-integral of the step process `V` up to `u` (i.e. `driftSimpleProcess V u`). Same sum-swap +
`telescope_cover` proof as the stochastic exponent, now with `F = min · u`. -/
lemma marshalDrift_eq (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (u : ℝ≥0) (ω : Ω)
    {N : ℕ} (hN : N + 1 = (marshalEndpoints hBmeas T V).card) :
    simpleDrift (marshalPart hBmeas T V) (marshalMult hBmeas T V) N u ω
      = ∑ p ∈ V.value.support,
          V.value p ω * (NNReal.toReal (min p.2 u) - NNReal.toReal (min p.1 u)) := by
  rw [simpleDrift]
  simp only [marshalMult, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [← telescope_cover hBmeas T V hp (fun x => NNReal.toReal (min x u)) hN, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hc : p.1 ≤ marshalPart hBmeas T V i ∧ marshalPart hBmeas T V (i + 1) ≤ p.2
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, zero_mul, mul_zero]

/-- **Cell-constancy.** On the enumerated cell `(sᵢ, sᵢ₊₁]` the step process `V` is constant, equal to
the per-cell multiplier: `⇑V t ω = marshalMult i ω` for `t` in the cell. (The `⊥` atom of `apply_eq`
drops since `t > sᵢ ≥ 0`; each interval indicator matches the covering test via `mem_Ioc_iff_cover`.) -/
lemma marshalMult_eq_uncurry (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {i : ℕ} {t : ℝ≥0} (ht1 : marshalPart hBmeas T V i < t)
    (ht2 : t ≤ marshalPart hBmeas T V (i + 1)) (ω : Ω) :
    ⇑V t ω = marshalMult hBmeas T V i ω := by
  have ht0 : t ∉ ({⊥} : Set ℝ≥0) := by
    simp only [Set.mem_singleton_iff]
    exact (lt_of_le_of_lt zero_le ht1).ne'
  rw [SimpleProcess.apply_eq, Set.indicator_of_notMem ht0, zero_add, Finsupp.sum, marshalMult]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Set.indicator_apply]
  by_cases hmem : t ∈ Set.Ioc p.1 p.2
  · rw [if_pos hmem, if_pos ((mem_Ioc_iff_cover hBmeas T V hle ht1 ht2 hp).mp hmem)]
  · rw [if_neg hmem, if_neg (fun hc => hmem ((mem_Ioc_iff_cover hBmeas T V hle ht1 ht2 hp).mpr hc))]

/-! ### The clamped marshalled step process (Rung 1 approximant)

For a dense simple approximant `V` of a bounded predictable `θ`, `marshalStepSP` is the single-partition
step process on the marshalled cells whose per-cell multiplier is the `[−C,C]`-clamp of `marshalMult`.
Since the marshalled cells are disjoint, clamping the multipliers clamps the *process*, so the L²
distance to `θ̂` only shrinks (`clampM` is a contraction toward any `|·| ≤ C` target). Mirrors the
adapted Riemann bridge `ItoIntegralRiemannBridgeAdapted.stepσ` with the uniform grid replaced by the
marshalled partition and `θ(tₖ)` replaced by `clampM C (marshalMult · )`. -/

/-- **The clamped marshalled step process** `∑ᵢ clampM C (marshalMult i) · 𝟙_{(sᵢ, sᵢ₊₁]}`, a
`TBoundedSP`: each per-cell multiplier is `𝓕_{sᵢ}`-measurable (adaptedness of `marshalMult`, preserved
by `clampM`) and bounded by `C`; each cell has right endpoint `≤ T`. -/
noncomputable def marshalStepSP (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) (N : ℕ) : TBoundedSP T hBmeas :=
  ∑ i ∈ (Finset.range N).attach,
    stepSP hBmeas (a := marshalPart hBmeas T V i.1) (b := marshalPart hBmeas T V (i.1 + 1))
      (marshalPart_mono hBmeas T V hle (Nat.le_succ i.1))
      (marshalPart_le_T hBmeas T V hle (i.1 + 1))
      (φ := fun ω => clampM C (marshalMult hBmeas T V i.1 ω))
      (measurable_clampM_comp hBmeas (stronglyMeasurable_marshalMult hBmeas T V i.1).measurable)
      (M := C) (fun _ => clampM_abs_le hC _)

/-- The clamped marshalled step process integrates to the clamped stochastic sum
`∑ᵢ clampM C (marshalMult i)·(B_{sᵢ₊₁} − B_{sᵢ})`. -/
lemma itoSimple_marshalStepSP (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) (N : ℕ) (ω : Ω) :
    itoSimple hBmeas (marshalStepSP hBmeas T V hle hC N).val ω
      = ∑ i ∈ Finset.range N, clampM C (marshalMult hBmeas T V i ω)
          * (B (marshalPart hBmeas T V (i + 1)) ω - B (marshalPart hBmeas T V i) ω) := by
  rw [marshalStepSP, AddSubmonoidClass.coe_finsetSum, itoSimple_sum, Finset.sum_apply,
    ← Finset.sum_attach (Finset.range N) (fun i => clampM C (marshalMult hBmeas T V i ω)
      * (B (marshalPart hBmeas T V (i + 1)) ω - B (marshalPart hBmeas T V i) ω))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [itoSimple_stepSP]

/-- **The uncurried clamped step process is a sum of cell indicators.** -/
lemma uncurry_marshalStepSP (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) (N : ℕ) (s : ℝ≥0) (ω : Ω) :
    Function.uncurry ⇑(marshalStepSP hBmeas T V hle hC N).val (s, ω)
      = ∑ i ∈ Finset.range N,
          (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
            (fun _ => clampM C (marshalMult hBmeas T V i ω)) s := by
  show ⇑(marshalStepSP hBmeas T V hle hC N).val s ω = _
  rw [marshalStepSP, AddSubmonoidClass.coe_finsetSum, coe_finsetSum_apply,
    ← Finset.sum_attach (Finset.range N) (fun i =>
      (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
        (fun _ => clampM C (marshalMult hBmeas T V i ω)) s)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SimpleProcess.apply_eq]
  simp only [stepSP]
  rw [Finsupp.sum_single_index (by simp)]
  simp

/-- **Partition of unity.** The marshalled cells `(sᵢ, sᵢ₊₁]`, `i < N`, cover `(0, s_N]` disjointly:
their indicators sum to `1` at any `s ∈ (0, T]` (with `s_N = T`). Proved by telescoping
`𝟙_{(a,b]} = 𝟙_{Iic b} − 𝟙_{Iic a}`. -/
lemma sum_cell_indicator_eq_one (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {N : ℕ} (hmpN : marshalPart hBmeas T V N = T) {s : ℝ≥0} (hs0 : 0 < s) (hsT : s ≤ T) :
    ∑ i ∈ Finset.range N,
      (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
        (fun _ => (1 : ℝ)) s = 1 := by
  have hsub : ∀ i,
      (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ => (1 : ℝ)) s
      = (Set.Iic (marshalPart hBmeas T V (i + 1))).indicator (fun _ => (1 : ℝ)) s
        - (Set.Iic (marshalPart hBmeas T V i)).indicator (fun _ => (1 : ℝ)) s := fun i => by
    have hab := marshalPart_mono hBmeas T V hle (Nat.le_succ i)
    simp only [Set.indicator_apply, Set.mem_Ioc, Set.mem_Iic]
    by_cases h1 : s ≤ marshalPart hBmeas T V i
    · rw [if_neg (fun h => absurd h.1 (not_lt.mpr h1)), if_pos (h1.trans hab), if_pos h1]; ring
    · rw [not_le] at h1
      by_cases h2 : s ≤ marshalPart hBmeas T V (i + 1)
      · rw [if_pos ⟨h1, h2⟩, if_pos h2, if_neg (not_le.mpr h1)]; ring
      · rw [not_le] at h2
        rw [if_neg (fun h => absurd h.2 (not_le.mpr h2)), if_neg (not_le.mpr h2),
          if_neg (not_le.mpr (hab.trans_lt h2))]; ring
  simp_rw [hsub]
  rw [Finset.sum_range_sub (fun i => (Set.Iic (marshalPart hBmeas T V i)).indicator (fun _ => (1 : ℝ)) s),
    hmpN, marshalPart_zero hBmeas T V hle,
    Set.indicator_of_mem (Set.mem_Iic.mpr hsT),
    Set.indicator_of_notMem (by simp only [Set.mem_Iic, not_le]; exact hs0)]
  norm_num

/-- **The clamped marshalled process is the clamp of `V`'s process** on `(0, T]`: cell-constancy
turns each per-cell multiplier into `clampM C (⇑V s)` on its cell, and the cells' partition of unity
collapses the indicator sum. This is the identity behind the L² contraction `‖Ṽⁿ − θ̂‖ ≤ ‖Vⁿ − θ̂‖`. -/
lemma uncurry_marshalStepSP_eq_clamp (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hmpN : marshalPart hBmeas T V N = T)
    {s : ℝ≥0} (hs0 : 0 < s) (hsT : s ≤ T) (ω : Ω) :
    Function.uncurry ⇑(marshalStepSP hBmeas T V hle hC N).val (s, ω) = clampM C (⇑V s ω) := by
  rw [uncurry_marshalStepSP]
  have hstep : ∀ i ∈ Finset.range N,
      (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ => clampM C (marshalMult hBmeas T V i ω)) s
      = (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ => clampM C (⇑V s ω)) s := by
    intro i _
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hmem : s ∈ Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))
    · rw [if_pos hmem, if_pos hmem]
      congr 1
      exact (marshalMult_eq_uncurry hBmeas T V hle hmem.1 hmem.2 ω).symm
    · rw [if_neg hmem, if_neg hmem]
  have hconst : ∀ i,
      (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ => clampM C (⇑V s ω)) s
      = clampM C (⇑V s ω) *
          (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
            (fun _ => (1 : ℝ)) s := by
    intro i
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hmem : s ∈ Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))
    · rw [if_pos hmem, if_pos hmem, mul_one]
    · rw [if_neg hmem, if_neg hmem, mul_zero]
  rw [Finset.sum_congr rfl hstep]
  simp_rw [hconst]
  rw [← Finset.mul_sum, sum_cell_indicator_eq_one hBmeas T V hle hmpN hs0 hsT, mul_one]

/-- **`clampM` is a contraction toward any in-range target.** For `|g| ≤ M`,
`|clampM M x − g| ≤ |x − g|` — the pointwise inequality behind the L² bound
`‖clampM C (⇑Vⁿ) − θ‖ ≤ ‖⇑Vⁿ − θ‖` (clamping toward a bounded `θ` only helps). -/
lemma clampM_dist_le {M g x : ℝ} (hg : |g| ≤ M) : |clampM M x - g| ≤ |x - g| := by
  rw [abs_le] at hg
  obtain ⟨hg1, hg2⟩ := hg
  unfold clampM
  rcases le_total x (-M) with hx | hx
  · rw [min_eq_right (by linarith), max_eq_left hx,
      abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rcases le_total x M with hx2 | hx2
    · rw [min_eq_right hx2, max_eq_right hx]
    · rw [min_eq_left hx2, max_eq_right (by linarith),
        abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

/-! ### L² convergence of the clamped marshalled approximant

Working now over a probability measure `μ`: the clamped marshalled process converges to `θ̂` in the
Itô-integrand `L²`, because it equals `clampM C (⇑V)` a.e. and `clampM` contracts toward the bounded
`θ`. -/

section Convergence

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- On `trimMeasure_T` (supported on `(0, T] × Ω`), the uncurried clamped marshalled process equals
`clampM C (⇑V)`. -/
lemma uncurry_marshalStepSP_ae_eq_clamp (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hmpN : marshalPart hBmeas T V N = T) :
    Function.uncurry ⇑(marshalStepSP hBmeas T V hle hC N).val
      =ᵐ[trimMeasure_T (μ := μ) T hBmeas] fun z => clampM C (Function.uncurry ⇑V z) := by
  have hsupp : ∀ᵐ z ∂(trimMeasure_T (μ := μ) T hBmeas), z.1 ∈ Set.Ioc 0 T := by
    rw [trimMeasure_T_eq_restrict]
    exact ae_restrict_of_forall_mem
      (MeasureTheory.measurableSet_predictable_Ioc_prod (𝓕 := natFiltration hBmeas) 0 T
        MeasurableSet.univ) (fun z hz => hz.1)
  filter_upwards [hsupp] with z hz
  exact uncurry_marshalStepSP_eq_clamp hBmeas T V hle hC hmpN hz.1 hz.2 z.2

/-- **The clamp contracts in `L²`.** The clamped marshalled approximant is at least as close to `θ̂`
as the raw approximant `V`: `‖Ṽ − θ̂‖ ≤ ‖V − θ̂‖`. Both norms are `eLpNorm`s of differences; the a.e.
identity `⇑Ṽ = clampM C (⇑V)` and the pointwise contraction `clampM_dist_le` (with `|θ| ≤ C`) give the
bound. -/
lemma norm_simpleAssembly_marshalStepSP_sub_le (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hmpN : marshalPart hBmeas T V N = T)
    {θ : ℝ≥0 → Ω → ℝ} (hpred : IsStronglyPredictable (natFiltration hBmeas) θ)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) :
    ‖simpleAssembly_T (μ := μ) T hBmeas (marshalStepSP hBmeas T V hle hC N)
        - processToLpPredictable (μ := μ) T hBmeas hpred hbdd‖
      ≤ ‖simpleAssembly_T (μ := μ) T hBmeas ⟨V, hle⟩
        - processToLpPredictable (μ := μ) T hBmeas hpred hbdd‖ := by
  have hf1 := memLp_uncurry_trim_T (μ := μ) T hBmeas (marshalStepSP hBmeas T V hle hC N).val
  have hfV := memLp_uncurry_trim_T (μ := μ) T hBmeas V
  have hg := memLp_uncurry_of_bdd_predictable (μ := μ) T hBmeas hpred hbdd
  have hLHS : simpleAssembly_T (μ := μ) T hBmeas (marshalStepSP hBmeas T V hle hC N)
      - processToLpPredictable (μ := μ) T hBmeas hpred hbdd
      = hf1.toLp _ - hg.toLp _ := rfl
  have hRHS : simpleAssembly_T (μ := μ) T hBmeas ⟨V, hle⟩
      - processToLpPredictable (μ := μ) T hBmeas hpred hbdd
      = hfV.toLp _ - hg.toLp _ := rfl
  rw [hLHS, hRHS, ← MemLp.toLp_sub hf1 hg, ← MemLp.toLp_sub hfV hg, Lp.norm_toLp, Lp.norm_toLp]
  apply ENNReal.toReal_mono (hfV.sub hg).2.ne
  rw [eLpNorm_congr_ae ((uncurry_marshalStepSP_ae_eq_clamp hBmeas T V hle hC hmpN).sub
    (Filter.EventuallyEq.refl _ (Function.uncurry θ)))]
  apply eLpNorm_mono_ae
  filter_upwards with z
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  exact clampM_dist_le (hbdd z.1 z.2)

/-- **The CLM agrees with the elementary Itô integral on simple processes.**
`itoIntegralCLM_T (simpleAssembly_T V) = itoAssembly_T V`, immediate from the `extendOfNorm`
construction of the CLM. -/
lemma itoIntegralCLM_T_simpleAssembly_T (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (V : TBoundedSP T hBmeas) :
    itoIntegralCLM_T hB T hBmeas (simpleAssembly_T (μ := μ) T hBmeas V)
      = itoAssembly_T hB T hBmeas V := by
  rw [itoIntegralCLM_T, LinearMap.extendOfNorm_eq (simpleAssembly_T_denseRange T hBmeas)
    ⟨1, fun W => by rw [one_mul]; exact (assembly_isometry_T hB T hBmeas W).le⟩]

/-- **The clamped marshalled approximant converges to `θ̂` in the integrand `L²`.** The contraction
`norm_simpleAssembly_marshalStepSP_sub_le` squeezed against `V n → θ̂`. This is the single
`E`-convergence that drives all three functional limits (stochastic integral, drift, quadratic
variation): each is a continuous functional of the integrand, read off along this one sequence. -/
theorem tendsto_simpleAssembly_marshalStepSP (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n => simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) :
    Tendsto (fun n => simpleAssembly_T (μ := μ) T hBmeas
        (marshalStepSP hBmeas T (V n).val (V n).property hC
          ((marshalEndpoints hBmeas T (V n).val).card - 1))) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (tendsto_iff_norm_sub_tendsto_zero.mp hV)
  exact norm_simpleAssembly_marshalStepSP_sub_le hBmeas T (V n).val (V n).property hC
    (marshalPart_card_sub_one hBmeas T (V n).val (V n).property) hpred hbdd

/-- **The clamped approximant's Itô integral converges to `∫θ dB`.** Given a raw approximating
sequence `V n → θ̂` in the integrand `L²` (from `simpleAssembly_T_denseRange`), the *clamped*
marshalled Itô integrals `itoAssembly_T (marshalStepSP (V n))` converge in `L²(μ)` to
`itoIntegralCLM_T θ̂ = ∫θ dB`. Proof: the contraction gives `simpleAssembly_T (marshalStepSP (V n)) →
θ̂` (`tendsto_simpleAssembly_marshalStepSP`), then the CLM is continuous and agrees with the
elementary integral on simple processes. The predictable analogue of `tendstoInMeasure_riemannσ`'s
`L²` input. -/
theorem tendsto_itoAssembly_marshalStepSP (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n => simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) :
    Tendsto (fun n => itoAssembly_T hB T hBmeas
        (marshalStepSP hBmeas T (V n).val (V n).property hC
          ((marshalEndpoints hBmeas T (V n).val).card - 1)))
      atTop (𝓝 (itoIntegralCLM_T hB T hBmeas
        (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) := by
  have hCLM := ((itoIntegralCLM_T hB T hBmeas).continuous.tendsto _).comp
    (tendsto_simpleAssembly_marshalStepSP T hBmeas hpred hC hbdd V hV)
  simp_rw [Function.comp_def, itoIntegralCLM_T_simpleAssembly_T] at hCLM
  exact hCLM

omit [IsProbabilityMeasure μ] in
/-- Replacing each `f n` by an a.e.-equal `f' n` preserves convergence in measure. -/
lemma tendstoInMeasure_congr_left {E : Type*} [MetricSpace E] {f f' : ℕ → Ω → E} {g : Ω → E}
    (h : ∀ n, f n =ᵐ[μ] f' n) (hfg : TendstoInMeasure μ f atTop g) :
    TendstoInMeasure μ f' atTop g := by
  intro ε hε
  refine (hfg ε hε).congr fun n => measure_congr ?_
  rw [Filter.eventuallyEq_set]
  filter_upwards [h n] with x hx
  simp only [hx]

/-- **A raw approximating sequence for `θ̂`.** From the density of the simple-process embedding, there
is a sequence `V : ℕ → TBoundedSP` with `simpleAssembly_T (V n) → θ̂`. -/
lemma exists_approxSeq (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hbdd : ∀ t ω, |θ t ω| ≤ C) :
    ∃ V : ℕ → TBoundedSP T hBmeas,
      Tendsto (fun n => simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
        (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd)) := by
  obtain ⟨x, hx_mem, hx_tendsto⟩ := mem_closure_iff_seq_limit.mp
    (simpleAssembly_T_denseRange (μ := μ) T hBmeas
      (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))
  choose V hV using hx_mem
  exact ⟨V, by simpa only [hV] using hx_tendsto⟩

/-- **The clamped stochastic exponents converge in measure to `∫θ dB`.** Transporting the `L²`
convergence (`tendsto_itoAssembly_marshalStepSP`) to convergence in measure and reading the `L²`
classes back as the genuine functions `itoSimple (marshalStepSP (V n))`. The predictable analogue of
`tendstoInMeasure_riemannσ`. -/
theorem tendstoInMeasure_marshalStochSum (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n => simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) :
    TendstoInMeasure μ (fun n => itoSimple hBmeas
        (marshalStepSP hBmeas T (V n).val (V n).property hC
          ((marshalEndpoints hBmeas T (V n).val).card - 1)).val) atTop
      (⇑(itoIntegralCLM_T hB T hBmeas (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) := by
  refine tendstoInMeasure_congr_left (fun n => ?_)
    (tendstoInMeasure_of_tendsto_Lp
      (tendsto_itoAssembly_marshalStepSP hB T hBmeas hpred hC hbdd V hV))
  exact (memLp_itoSimple hB hBmeas (marshalStepSP hBmeas T (V n).val (V n).property hC
    ((marshalEndpoints hBmeas T (V n).val).card - 1)).val).coeFn_toLp

/-- **The stochastic-exponent a.e.-subsequence extraction.** Every subsequence `ns` of the clamped
stochastic exponents has a further subsequence converging a.e. to `∫θ dB` — the single stochastic
input the a.e.-subsequence set-integral engine of the assembly needs (mirror of
`exists_subseq_riemannσ_ae`). -/
theorem exists_subseq_marshalStochSum_ae (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBmeas) θ) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ t ω, |θ t ω| ≤ C) (V : ℕ → TBoundedSP T hBmeas)
    (hV : Tendsto (fun n => simpleAssembly_T (μ := μ) T hBmeas (V n)) atTop
      (𝓝 (processToLpPredictable (μ := μ) T hBmeas hpred hbdd)))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ ω ∂μ, Tendsto (fun k => itoSimple hBmeas
        (marshalStepSP hBmeas T (V (ns (ms k))).val (V (ns (ms k))).property hC
          ((marshalEndpoints hBmeas T (V (ns (ms k))).val).card - 1)).val ω) atTop
      (𝓝 (⇑(itoIntegralCLM_T hB T hBmeas
        (processToLpPredictable (μ := μ) T hBmeas hpred hbdd)) ω)) := by
  have hconv : TendstoInMeasure μ (fun k => itoSimple hBmeas
      (marshalStepSP hBmeas T (V (ns k)).val (V (ns k)).property hC
        ((marshalEndpoints hBmeas T (V (ns k)).val).card - 1)).val) atTop
      (⇑(itoIntegralCLM_T hB T hBmeas (processToLpPredictable (μ := μ) T hBmeas hpred hbdd))) :=
    fun ε hε => (tendstoInMeasure_marshalStochSum hB T hBmeas hpred hC hbdd V hV ε hε).comp hns
  obtain ⟨ms, hms, hae⟩ := hconv.exists_seq_tendsto_ae
  exact ⟨ms, hms, hae⟩

end Convergence

end MathFin
