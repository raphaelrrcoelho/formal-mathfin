# Rung 4 — d-asset one-period FTAP (design)

**Goal.** `MathFin.OnePeriodVector.ftap_one_period_vector`: on an arbitrary
probability space `(Ω, P)`, for a measurable `ℝᵈ`-valued discounted excess return
`Y : Ω → EuclideanSpace ℝ (Fin d)` and **constant** portfolios `θ ∈ ℝᵈ` (trivial
initial information),

> `NoArbitrage P Y ↔ ∃ Q, IsEMM P Y Q`

where `NoArbitrage`: `∀ θ, ⟪θ,Y⟫ ≥ 0 a.e. → ⟪θ,Y⟫ = 0 a.e.`; `IsEMM Q`: `Q ~ P`,
`Y` is `Q`-integrable, `∫ Y ∂Q = 0 ∈ ℝᵈ`. The faithful one-period d-asset Föllmer–
Schied / Dalang–Morton–Willinger (T=1).

## Why this rung, and what it deliberately avoids

The general-Ω **multi-period** crown needs three pieces of analysis Mathlib lacks
(L⁰ gains-cone closedness via a Kabanov–Stricker subsequence lemma; a measurable
selection / disintegration gluing; a Kreps–Yan strictly-positive separation). The
**one-period d-asset** case with trivial `ℱ₀` sidesteps all three: `θ` ranges over
the **finite-dimensional** `ℝᵈ`, so the gains set is finite-dimensional and the EMM
is **explicit**.

## Proof architecture — the Esscher / softplus-potential construction

**Forward** (`EMM ⇒ NA`). Under `Q`, `∫ ⟪θ,Y⟫ ∂Q = ⟪θ, E_Q[Y]⟫ = 0`
(`integral_inner` + `fair`); a non-negative integrand with zero integral is `0` a.e.
(`integral_eq_zero_iff_of_nonneg_ae`); transport to `P` by `Pabs.ae_eq`. Mirrors the
scalar `MathFin.OnePeriod` forward with `θ·Y ↦ ⟪θ,Y⟫`.

**Backward** (`NA ⇒ EMM`), the novel core — an **explicit minimal-divergence EMM**:

1. **Reduction to `Y ∈ L¹`.** Replace `P` by the equivalent probability
   `P̃ = P.withDensity (w/κ)`, `w = (1 + ‖Y‖)⁻¹ ∈ (0,1]`, `κ = ∫ w ∂P`. Then
   `‖Y‖·(w/κ) ≤ κ⁻¹` is bounded so `Y ∈ L¹(P̃)`, `P̃ ~ P`, and NA — an a.e. notion —
   transfers. (Direct generalisation of the scalar reduction, `|Y| ↦ ‖Y‖`.)

2. **The softplus potential.** `f(θ) = ∫ log(1 + exp ⟪θ,Y⟫) ∂P̃`. With
   `h(u) = log(1+eᵘ)` (softplus): `h` convex, `h ≥ 0`, `h(u) ≤ u⁺ + log 2`, and
   `h'(u) = σ(u) = (1+e^{-u})⁻¹ ∈ (0,1)` (logistic). So `f` is well-defined for
   `Y ∈ L¹` (`h(⟪θ,Y⟫) ≤ ‖θ‖‖Y‖ + log 2`), convex in `θ`, with directional
   derivative `D_u f(θ) = ∫ ⟪u,Y⟫ · σ(⟪θ,Y⟫) ∂P̃` (1-D differentiation under the
   integral, dominated by `‖u‖‖Y‖ ∈ L¹` since `σ ∈ (0,1)`).

3. **Coercivity ⇒ minimiser.** Let `ker = {u : ⟪u,Y⟫ = 0 a.e.}` (a subspace of ℝᵈ);
   `f` is constant along `ker`. On `ker⊥`, NA gives coercivity: for unit `u ∈ ker⊥`,
   `⟪u,Y⟫` is not a.e. `≤ 0` (else NA forces `= 0` a.e., i.e. `u ∈ ker`), so
   `P̃(⟪u,Y⟫ > 0) > 0` and `f(tu)/t → E[⟪u,Y⟫⁺] > 0` as `t→∞`. A minimising sequence
   thus stays bounded on `ker⊥`; extract a convergent subsequence
   (`IsCompact.exists_isMinOn` on a sublevel ball) → global minimiser `θ*`.

4. **First-order condition ⇒ fairness.** `θ*` a global min of the differentiable
   convex `f` ⇒ `∇f(θ*) = 0`, i.e. `∫ ⟪u,Y⟫·σ(⟪θ*,Y⟫) ∂P̃ = 0 ∀u`, i.e.
   `∫ Y · σ(⟪θ*,Y⟫) ∂P̃ = 0 ∈ ℝᵈ`.

5. **The explicit EMM.** `z = σ(⟪θ*,Y⟫) ∈ (0,1)` is measurable, **strictly positive**,
   **bounded**. `Q = P̃.withDensity(z) / (∫ z ∂P̃)` (normalise) is a probability with
   `Q ~ P̃ ~ P` (z>0 bounded), `Y ∈ L¹(Q)` (z bounded), and
   `∫ Y ∂Q = (∫ z·Y ∂P̃)/(∫ z ∂P̃) = 0`. The EMM density is the **Esscher / minimal-
   entropy-type** weight — the d-asset analogue of the scalar balancing density.

## Mathlib lemma map (confirmed present, pin ~v4.31)

`integral_inner`, `Integrable.const_inner`, `ContinuousLinearMap.integral_comp_comm`;
`integral_eq_zero_iff_of_nonneg_ae`; `withDensity_absolutelyContinuous(')`,
`integrable_withDensity_iff_integrable_smul'`, `integral_withDensity_eq_integral_toReal_smul`;
`convexOn_exp` / `StrictConvexOn`; `hasDerivAt_integral_of_dominated_loc_of_lip`
(1-D FOC); `IsCompact.exists_isMinOn` / `LowerSemicontinuousOn.exists_isMinOn`;
`EuclideanSpace`/`Submodule.orthogonal`. Softplus convexity + logistic bounds are
elementary (built locally).

## Tasks

- **T1** model (`NoArbitrage`, `IsEMM`) + forward `noArbitrage_of_isEMM`.
- **T2** softplus `h`/logistic `σ` lemmas; `f`, convexity, well-definedness on L¹;
  directional derivative `D_u f = ∫ ⟪u,Y⟫·σ(⟪θ,Y⟫)`.
- **T3** coercivity on `ker⊥` under NA ⇒ minimiser ⇒ FOC ⇒ `∫ Y·σ(⟪θ*,Y⟫) = 0`
  (integrable core `exists_isEMM_of_noArbitrage_integrable`).
- **T4** bounded-density reduction (drop integrability) — mirror scalar.
- **T5** biconditional `ftap_one_period_vector` + `#print axioms`.
- **T6** wiring: umbrella, AxiomAudit pin, corpus `mf-ftap-one-period-vector`,
  AxiomAuditGen regen, full build, ledger, coverage, values panel.

## Scope (honest)

One period, **d assets**, **trivial `ℱ₀`** (constant `θ`), arbitrary `(Ω,P)`. The
general-Ω **multi-period** DMW (predictable `L⁰(ℱ_t)`-strategies, the L⁰ closedness
core) and the conditional gluing remain open — those are Rungs 5–6.
