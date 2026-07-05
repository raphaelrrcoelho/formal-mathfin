# Design: the adapted-coefficient Itô formula

- **Date:** 2026-07-05
- **Status:** approved design, pre-implementation
- **Author:** Raphael Coelho
- **Topic:** Itô's formula for an Itô process with **adapted** drift/diffusion
  coefficients, `X_t = X₀ + ∫₀ᵗ b_s ds + ∫₀ᵗ σ_s dB_s`; the analytic keystone is
  the quadratic variation of a stochastic integral, `⟨X⟩_t = ∫₀ᵗ σ_s² ds`.

## 1. Goal

Formalise Itô's formula against a general **adapted-coefficient** Itô process:

> For `X_t = X₀ + ∫₀ᵗ b_s ds + ∫₀ᵗ σ_s dB_s` with bounded adapted continuous
> coefficients and `f ∈ C²`,
>
> `f(X_T) − f(X₀) =ᵐ ∫₀ᵀ f'(X_s) σ_s dB_s + ∫₀ᵀ (f'(X_s) b_s + ½ f''(X_s) σ_s²) ds`.

The current tower has Itô's formula only for **constant-coefficient** processes
`X_t = X₀ + b·t + σ·B_t` (`ito_formula_itoProcess`), proved by the reduction
`X_t = g(t, B_t)` to the time-dependent formula for functions of `B_t`. That
reduction **collapses** for adapted coefficients — `X_t = X₀ + ∫b ds + ∫σ dB` is
a path functional, not a function of `(t, B_t)` — so this is a genuinely
different proof architecture whose heart is a real **quadratic variation of a
stochastic integral**.

This is the foundational prerequisite for continuous-time Girsanov (issue #40):
the Doléans–Dade exponential `Z_t = exp(∫θ dB − ½∫θ² ds)` needs Itô's formula
with adapted coefficients (`σ = θ`, `b = −½θ²`, `f = exp`), whereupon the drift
cancels and `Z_t = 1 + ∫₀ᵗ Z_s θ_s dB_s` is a stochastic integral, hence a
(local) martingale. Girsanov itself is **out of scope here** (SP3, §9).

## 2. Scope — locked decisions

- **Route β** (chosen over the simple-process/approximation shortcut): build the
  general adapted-coefficient Itô formula, not a bespoke Doléans exponential.
  This also unlocks SDEs and a general Feynman–Kac later.
- **This spec covers SP1 + SP2**: the adapted-σ quadratic variation **and** the
  full adapted Itô-formula assembly. Girsanov (SP3) is a separate later
  spec→plan cycle.
- **Coefficients:** `b, σ : ℝ≥0 → Ω → ℝ`, **bounded, adapted, continuous paths**.
  Bounded `b` makes the drift path `A_t = ∫₀ᵗ b ds` Lipschitz (the hypothesis
  `ItoProcessQV` already uses). `σ` bounded + path-continuous gives the
  L²-time-continuity the freezing lemma needs.
- **Driver:** `IsPreBrownianReal B μ`, `IsProbabilityMeasure μ` — the tower's
  standard `[0,T]` setting.
- **Function class:** `f ∈ C²` (the mathematical minimum) with bounded `f', f''`
  for the clean formula (B5); a stopping-time-**localized** version for unbounded
  `f` (B6). **Explicit decision:** to avoid rebuilding the Taylor-remainder brick,
  default to the tower's existing convention — `C³` with at-most-exponential-growth
  derivatives (as `ito_formula_itoProcess` requires) — unless the plan shows
  `ItoFormulaRemainder` already closes the `C²` remainder for the `X`-increment
  form. The statement is quoted at `C²`; the working hypothesis is `C³`-exp-growth.
- **Statement idiom:** the QV keystone is stated as an **L² limit of
  squared-increment sums along the uniform partition** (matching
  `QuadraticVariationL2.tendsto_qv` / `ItoProcessQV.tendsto_qv_ito_process`);
  there is no abstract `⟨·⟩` bracket object in the tower and we do not introduce
  one. The Itô formula's stochastic term is carried by the existing continuous
  Itô integral `itoIntegralCLM_T` (trim-`L²` realization of the integrand).

### Out of scope (named follow-ons)
- **SP3 — continuous Girsanov** (issue #40): Doléans exponential martingale,
  `B^θ = B − ∫θ ds` is `Q`-Brownian, re-derive `discountedGBM_isMartingale`,
  flip `gir-thm-9.1.8` reduced_core→full, wire the architecture-doc Girsanov row.
- **The exp-growth *global* formula** for `f = exp` on the Doléans exponent — the
  concrete `f = exp` instance is folded into SP3 (the fallback in §8 keeps SP2
  shippable even if B6 is deferred).
- **Unbounded / general (non-continuous, non-bounded) coefficients**; the
  semimartingale Itô formula; multi-dimensional / covariation Itô.

## 3. What already exists (reuse, do not rebuild)

The Summit-B follow-ons already built most of the analytic engine, aimed at the
`f(t, B_t)` case:

- **`WeightedQuadraticVariation.tendsto_weighted_qv_process`** — for a **bounded
  adapted continuous weight** `w`, `∑ₖ w_{tₖ}(ΔBₖ)² → ∫₀ᵀ w_s ds` in L². Already
  at full generality in the weight ("never cared where the weight came from,
  only that it is adapted and bounded"). Companion
  `tendsto_riemann_L2_process` (Riemann sum of a continuous path).
- **`ItoIntegralRiemannBridge.itoIntegralCLM_T_of_bdd_cont`** — `∑ φ(B_{tₖ})ΔBₖ →
  itoIntegralCLM_T gφ` in L², for bounded continuous `φ` (integrand `φ∘B`), via
  `TBoundedSP` step approximants + `Lp` closedness.
- **`ItoIntegralCovariation`** — the bilinear Itô isometry
  `𝔼[(∫φ dB)(∫ψ dB)] = ∫ φ ψ d(trim)` and the bundled `LinearIsometry
  itoIsometry_T`. The freezing lemma's L²-error identity is one application.
- **`ItoProcessQV.tendsto_qv_ito_process`** — `∑ₖ(ΔXₖ)² → σ²T` in L² for
  **constant** σ, Lipschitz drift. Supplies the drift-drops-out mechanism (the
  drift² and cross terms die at rates `Cₐ²T²/n` and `1/n` — bounds that use only
  `|b| ≤ Cₐ`, **not** σ constant, so they transfer verbatim to adapted σ).
- **`ItoProcessPredictable` (`itoProcessCLM`, `φ ● B`)** — the adapted Itô
  integral `∫₀ᵗ σ dB` as a process, with the energy identity; Summit-B's
  continuous L²-martingale modification.
- **`ItoFormulaRemainder` / `ItoFormulaTDRemainder`** — the Taylor-remainder
  machinery (`∑ Rₖ → 0`).
- **`ItoFormulaUnrestrictedLocMart.ito_formula_unrestricted_local`** — Summit-C's
  double-cutoff **spatial** stopping-time localization (the pattern B6 reuses).
- **`itoIntegralCLM_T`** — the continuous `[0,T]` Itô integral carrying the
  stochastic term.

### Correction (2026-07-05, discovered at execution) — the missing infrastructure (SP0)

The claim above that the engine "generalizes for free" was over-optimistic. It
holds for the *weight* in the second-order term, but **not** for the diffusion
increment itself. Two pieces the tower does **not** have, confirmed by grep at
execution time:

1. **Raw-process → `Lp`-class realization.** The Itô integral takes its integrand
   as an `Lp` class `φ : Lp ℝ 2 (trimMeasure_T T hBmeas)`, not a raw
   `σ : ℝ≥0 → Ω → ℝ`. Realizing a bounded adapted continuous `σ` as `φ` is a real
   lemma (σ predictable-measurable + L² + `.toLp`) — `ItoIntegralRiemannBridge`
   did exactly this for `φ∘B` and it was substantial (predictability as an a.e.
   limit of simple processes).
2. **No sub-interval increment API.** `itoProcessCLM … t …` is the integral up to
   `t`; there is **no** lemma tower-wide giving
   `M_{t₂} − M_{t₁} = ∫_{(t₁,t₂]} σ dB` (only the `[0,∞)` `restrictToBand` gluing).
   B1a must build the CLM's time-additivity from the `extendOfNorm` construction.

**Consequence:** SP1's B1a is not a "fiddly step" but a prerequisite milestone
**SP0 — the concrete adapted stochastic integral**: (i) `σ`-realization
(`processToLp_of_bdd_adapted_cont`), (ii) the sub-interval increment identity.
The Route-β plan is re-sequenced **SP0 → SP1 → SP2**.

### Route decision update (2026-07-05) — two tracks

Given SP0's real cost, the program runs **two tracks in parallel**:
- **Track β (this spec):** SP0 → SP1 → SP2, the general adapted-coefficient Itô
  formula (the foundational tool). Longer; infrastructure-first.
- **Track α (the Girsanov path, faster):** the simple-process route to
  bounded-adapted-θ Girsanov, which needs **none** of SP0 — its stochastic
  exponential factorizes into concrete per-cell increments. Bricks: **α1**
  conditional Wald with adapted multiplier (`E[exp(θᵢΔBᵢ − ½θᵢ²Δtᵢ)|𝓕_{tᵢ}]=1`,
  mirroring `condExp_adapted_mul_increment` + the Gaussian MGF of
  `waldExponential_isMartingale`) → **α2** simple stochastic exponential is a
  martingale (product/telescoping) → **α3** bounded-adapted-θ by L²-bounded
  approximation → **α4** `B^θ` is `Q`-Brownian (via `Z·exp(aB^θ−½a²t)=Z^{θ+a}`
  ∀a + exponential characterization) → wire, flip `gir-thm-9.1.8`. Track α reaches
  the actual Girsanov deliverable without SP0; Track β delivers the general tool.

## 4. The design — bricks

The linchpin is the **freezing lemma (B1)**: it appears twice — in the QV
keystone (B2, second-order term) *and* in the assembly (B5, first-order
stochastic term) — because both need to replace a stochastic-integral increment
`ΔMₖ = ∫_{tₖ}^{tₖ₊₁} σ dB` by the frozen `σ_{tₖ}·ΔBₖ`.

Notation: uniform partition of `[0,T]`, `tₖ = kT/n`; `M_t = ∫₀ᵗ σ dB` (the
`itoProcessCLM` process); `A_t = ∫₀ᵗ b ds`; `ΔYₖ = Y_{tₖ₊₁} − Y_{tₖ}`.

### B1 — Freezing lemma (**new**)
`ΔMₖ − σ_{tₖ}ΔBₖ = ∫_{tₖ}^{tₖ₊₁} (σ_s − σ_{tₖ}) dB` (a sub-interval Itô integral),
so by the Itô isometry (`ItoIntegralCovariation`)
`𝔼[(ΔMₖ − σ_{tₖ}ΔBₖ)²] = ∫_{tₖ}^{tₖ₊₁} 𝔼[(σ_s − σ_{tₖ})²] ds`.
Bounded + path-continuous σ ⟹ (DCT) `∑ₖ 𝔼[(ΔMₖ − σ_{tₖ}ΔBₖ)²] → 0`. Then the
**weighted defect** `∑ₖ w_{tₖ}[(ΔMₖ)² − σ_{tₖ}²(ΔBₖ)²] → 0` in L¹ via
`(a−b)(a+b)` + Cauchy–Schwarz against the L²-bounded `∑(ΔMₖ)²`, `∑(ΔBₖ)²`.
- *Sub-brick B1a:* the per-cell increment identity — the process increment `ΔMₖ`
  of `itoProcessCLM` equals the sub-interval Itô integral `∫_{tₖ}^{tₖ₊₁} σ dB`.
  This connects the *process* to sub-interval integrals; the riskiest plumbing.

### B2 — Adapted-σ weighted quadratic variation (**new assembly**) — SP1 keystone
`∑ₖ w_{tₖ}(ΔXₖ)² → ∫₀ᵀ w_s σ_s² ds` in L², for bounded adapted continuous `w`.
Expand `(ΔXₖ)² = (ΔAₖ)² + 2ΔAₖΔMₖ + (ΔMₖ)²`:
- drift² `∑ w(ΔAₖ)² → 0` and cross `∑ w·2ΔAₖΔMₖ → 0` — the `ItoProcessQV`
  bounds, which use only `|b| ≤ Cₐ`;
- diffusion `∑ w(ΔMₖ)² → ∫ w σ² ds` — **B1** (freeze `(ΔMₖ)² ↝ σ_{tₖ}²(ΔBₖ)²`)
  then `WeightedQuadraticVariation.tendsto_weighted_qv_process` with weight `wσ²`.
`w ≡ 1` gives `⟨X⟩ = ∫σ²ds` (`tendsto_qv_ito_process_adapted`), the headline SP1
theorem generalizing `ItoProcessQV` from constant to adapted σ.

### B3 — The adapted Itô process as a continuous adapted process (**mostly reuse**)
`X_t = X₀ + A_t + M_t` with `M` the `itoProcessCLM` process (Summit-B continuous
L²-martingale modification) and `A_t = ∫₀ᵗ b ds` continuous (bounded `b`). Adapted,
continuous paths a.s.

### B4 — Adapted Riemann→Itô bridge (**modest generalization**)
`∑ₖ ψ_{tₖ} ΔBₖ → itoIntegralCLM_T gψ` in L², for **bounded adapted continuous**
`ψ` (the use case `ψ = f'(X)·σ`). Generalizes
`itoIntegralCLM_T_of_bdd_cont` from `ψ = φ∘B` to a general bounded adapted
continuous integrand; the `TBoundedSP`-approximant + `Lp`-closedness proof
carries over (`ψ_{tₖ}` is a bounded adapted coefficient).

### B5 — Assemble the formula, bounded `f', f''` (**new**)
Telescope `f(X_T) − f(X₀) = ∑ₖ [f(X_{tₖ₊₁}) − f(X_{tₖ})]`, Taylor each term:
`= f'(X_{tₖ})ΔXₖ + ½ f''(X_{tₖ})(ΔXₖ)² + Rₖ`. Then, in L¹/L²:
- `∑ f'(X_{tₖ})ΔAₖ → ∫ f'(X) b ds` (Riemann of a continuous path);
- `∑ f'(X_{tₖ})ΔMₖ → ∫ f'(X) σ dB` — **B1** (freeze `ΔMₖ ↝ σ_{tₖ}ΔBₖ`) then **B4**
  with `ψ = f'(X)σ`;
- `∑ ½ f''(X_{tₖ})(ΔXₖ)² → ½ ∫ f''(X) σ² ds` — **B2** with weight `w = f''(X)`;
- `∑ Rₖ → 0` — `ItoFormulaRemainder` (adapted to the `X`-increment form).

### B6 — Localize to unbounded `f` (**new / hardest**)
For `f` with unbounded but continuous `f''` (e.g. exp-growth), the weight
`f''(X)` in B2 is not bounded. Localize **spatially**: stop `X` at the exit time
`τ_N = inf{t : |X_t| ≥ N}` (the raw-filtration exit time already built for
Summit C), apply B5 to the stopped process (bounded weight on `[−N, N]`), and let
`N → ∞`, leaving a continuous-local-martingale residual — reusing the
`ito_formula_unrestricted_local` double-cutoff pattern. **Not** the constant-coeff
*time* cutoff (that used the `(t, B_t)` reduction, which is gone here).

## 5. Files (new, `MathFin/Foundations/`)

| file | bricks | one-theorem-per-file where practical |
|---|---|---|
| `AdaptedStochasticIntegralFreezing.lean` | B1 (+ B1a) | the freezing lemma + weighted defect |
| `AdaptedQuadraticVariation.lean` | B2 | `tendsto_weighted_qv_ito_process`, `tendsto_qv_ito_process_adapted` |
| `AdaptedItoProcess.lean` | B3 | `X` as a continuous adapted process + its increment lemmas |
| `ItoIntegralRiemannBridgeAdapted.lean` | B4 | `itoIntegralCLM_T_of_bdd_cont_adapted` |
| `ItoFormulaAdapted.lean` | B5, B6 | `ito_formula_adapted` (bounded `f''`) + `ito_formula_adapted_local` |

Module-system rule applies to every file (`@[expose] public section` after the
docstring). Keep files small (one theorem + private helpers) for
re-elaboration speed.

## 6. Deliverables / faithfulness

- **New `full` benchmark entries** (domain `stochastic_calculus`,
  `benchmarks/stochastic_calculus.json`):
  1. **Adapted-σ quadratic variation** (SP1) — `⟨X⟩ = ∫σ²ds`, referencing
     `tendsto_qv_ito_process_adapted`.
  2. **The adapted Itô formula** (SP2) — `ito_formula_adapted`, referencing the
     capstone.
- **Coverage:** both count toward `full + library_wrapper` delivery. Update
  `docs/coverage.md`, `docs/bridges.md` (a new Foundations bridge:
  constant-coeff → adapted-coeff Itô), `docs/roadmap.md`, and
  `docs/mathematical-architecture.md` (note SP1/SP2 land; the Girsanov row
  stays partial until SP3).
- **Do not** claim the Girsanov row is wired — that is SP3.

## 7. Verification

- Per brick: `./scripts/lean-check.sh MathFin/Foundations/<file>.lean` green
  (0 sorries) against the warm daemon.
- After the benchmark edits: regenerate `MathFin/AxiomAuditGen.lean`
  (`python3 -m tools.verify.axiom_audit_gen --write`); extend
  `MathFin/AxiomAudit.lean` for the two headliner theorems; `#print axioms`
  must be `propext, Classical.choice, Quot.sound` only.
- Final canonical gate: full `lake build` (daemon down — one Lean process),
  then `ledger status` fresh / re-verify stale, `pytest` gates 19/19.
- Each session ends green; no sorries committed.

## 8. Risks & scope boundaries

- **Top risk — B6 localization.** Spatial stopping-time localization of the
  adapted formula is the hardest, least-templated brick. **Fallback:** SP2 ships
  the **bounded-`f''`** formula (B5) as the `full` deliverable; B6 and the
  exp-growth global form move into SP3, where `f = exp` is handled concretely
  (and the Doléans exponent's structure — the drift cancellation — may permit a
  more direct argument than the fully general localization).
- **B1a plumbing risk.** Identifying the `itoProcessCLM` process increment `ΔMₖ`
  with the sub-interval Itô integral `∫_{tₖ}^{tₖ₊₁} σ dB` is fiddly (trim-measure
  / restriction bookkeeping). Isolate it as its own lemma; it is the one place
  the *process* meets *sub-interval* integrals.
- **Ledger blast radius.** Editing the Itô tower re-stales a transitive closure
  of `stochastic_calculus` / `mathematical_finance` entries; re-verify via the
  warm daemon (no `--exec`, detached) — a corpus-scale `--exec` sweep OOMs the
  10 GB box (memory doctrine).
- **Multi-session.** SP1 (B1–B2) is one coherent milestone; SP2 (B3–B6) is a
  second. Land SP1 green before starting SP2. Coordinate before SP3.

## 9. Follow-on: SP3 — continuous Girsanov (separate spec)

Once `ito_formula_adapted` (with the exp-growth case, B6 or the SP3 fallback)
exists:
1. **Doléans exponential:** `Z_t = exp(∫θ dB − ½∫θ² ds)`; Itô ⟹ `Z_t = 1 +
   ∫₀ᵗ Z_s θ_s dB_s` (drift cancels) ⟹ local martingale; bounded θ + the L²
   bound `𝔼[Z_t²] ≤ exp(K²T)` ⟹ true martingale.
2. **Girsanov:** for `Q = withDensity(Z_T)`, `B^θ = B − ∫θ ds` is `Q`-Brownian
   (via `exp(aB^θ − ½a²t)` a `Q`-martingale ∀a — `Z·exp(aB^θ − ½a²t) =
   Z^{θ+a}`, a `P`-martingale by step 1 — plus an exponential-characterization
   sub-lemma).
3. **Wire:** re-derive `discountedGBM_isMartingale` through it; flip
   `gir-thm-9.1.8` reduced_core→full; architecture-doc Girsanov row → WIRED
   (bounded case).
