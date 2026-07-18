# HJM interest-rate models — a formalization program

**Status:** design ratified 2026-07-18. **Ambition:** the full landmark — the HJM
drift condition with the bond dynamics *derived*, nothing assumed.
**Axis:** a formalization landmark (a cross-tower *stochastic Fubini*) that yields
a finance crown (the no-arbitrage drift restriction). Naming the axis first, per
`feedback_question_the_goal`: the deliverable is Fubini-as-a-shared-primitive; HJM
is its first flagship consumer.

Tracking issue: **#138** (umbrella). Child issues: **#139–#158** (numbered in §6).

---

## 1. The crown theorem

Work on a filtered space `(Ω, F, (F_t), Q)` carrying a `Q`-Brownian motion `W`
(risk-neutral / bank-account numéraire). The state is the **entire forward-rate
curve** `f(t,T)` for `t ≤ T`, an Itô process in `t` for each fixed maturity `T`:

```
df(t,T) = α(t,T) dt + σ(t,T) dW_t         (t-dynamics, T fixed)
```

**HJM drift condition (Heath–Jarrow–Morton 1992).** The discounted bond
`P(·,T)/B(·)` is a `Q`-martingale for every maturity `T` (no arbitrage) **iff**

```
α(t,T) = σ(t,T) · ∫_t^T σ(t,u) du          for all t ≤ T.
```

The forward-rate drift is completely pinned by its own volatility structure. This
is the theorem worth having; everything below is the atomic path to it.

## 2. Objects

| object | definition |
|---|---|
| bond | `P(t,T) = exp(−∫_t^T f(t,u) du)` |
| short rate | `r(t) = f(t,t)` |
| bank account | `B(t) = exp(∫_0^t r(s) ds)` |
| discounted bond | `Z(t,T) = P(t,T)/B(t)` |
| integrated drift | `α*(t,T) = ∫_t^T α(t,u) du` |
| integrated vol | `σ*(t,T) = ∫_t^T σ(t,u) du` |

Coefficient hypotheses: `α, σ` predictable in `s`, jointly measurable in `(s,T)`,
with `∫_0^T ∫_0^T (|α| + σ²) < ∞` — enough for the Itô integrals and the two
Fubini interchanges. These live in an `HJMModel` bundle (Tier 0).

## 3. The mathematical spine

Five identities carry the whole result. Signs verified against Björk, *Arbitrage
Theory in Continuous Time*, ch. 23.

**(A) Log-bond dynamics.** `Y(t,T) := log P(t,T) = −∫_t^T f(t,u) du`. The lower
limit *and* the integrand both move with `t`; the stochastic Leibniz rule gives

```
d(∫_t^T f(t,u)du) = −f(t,t) dt + ∫_t^T df(t,u) du
                  = −r(t) dt + α*(t,T) dt + σ*(t,T) dW_t
```

so `dY(t,T) = [r(t) − α*(t,T)] dt − σ*(t,T) dW_t`. The interchange
`∫_t^T (σ(t,u) dW_t) du = (∫_t^T σ(t,u) du) dW_t` **is** the stochastic Fubini
theorem (§4). The `−f(t,t)dt = −r(t)dt` lower-limit term is where the short rate
*emerges* — conceptually the crux of the assembly.

**(B) Bond dynamics.** `P = exp(Y)`, Itô-for-exp:
`dP/P = dY + ½ d⟨Y⟩ = [r − α* + ½σ*²] dt − σ* dW`.

**(C) Discounted-bond dynamics.** `B` is finite-variation, `dB/B = r dt`, so
`dZ/Z = dP/P − r dt = [−α*(t,T) + ½σ*(t,T)²] dt − σ*(t,T) dW`.

**(D) Drift condition, integrated form.** `Z` is a positive continuous
(local) martingale iff its drift vanishes:
`α*(t,T) = ½ σ*(t,T)²` for a.e. `t`, all `T`.

**(E) Drift condition, differential form (the crown).** Differentiate (D) in `T`
(FTC + chain rule): `∂_T α* = α(t,T)`, `∂_T[½σ*²] = σ*(t,T)·σ(t,T)`, hence

```
α(t,T) = σ(t,T) · σ*(t,T).
```

The converse integrates `α = σσ* = ½ ∂_T(σ*²)` from `t` to `T` using
`σ*(t,t)=0`, recovering `α* = ½σ*²`, hence the martingale property.

## 4. Architecture: stochastic Fubini as a shared cross-tower primitive

The interchange in (A) is not an HJM lemma. It is the statement **"an
integral-CLM commutes with a parameter Bochner-integral,"** and Mathlib already
proves that fact for *any* continuous linear map:

```
ContinuousLinearMap.integral_comp_comm (L : E →L[𝕜] Fₗ) (φ_int : Integrable φ μ) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ)
    -- Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
```

Every stochastic-integral tower in the library already exposes its integral **as
a CLM** — the shared `extendOfNorm`/CLM abstraction that unified the Wiener, Itô,
and Lévy towers (`Foundations/ExtendOfNormIsometry.lean`):

| tower | integral CLM | file |
|---|---|---|
| Wiener | `wienerIntegralLp : Lp ℝ 2 (Ioc 0 T) →L[ℝ] Lp ℝ 2 μ` | `WienerIntegralL2` |
| Itô | `itoIntegralCLM_T : L²(predictable) →L[ℝ] Lp ℝ 2 μ` | `ItoIntegralCLM` |
| Lévy | `itoLevyIntegralL2 : levyClosure N →L[ℝ] Lp ℝ 2 P` | `PoissonCompensatedIntegralOperator` |

So stochastic Fubini is **one tower-agnostic primitive + one-line instances** —
not a wrapper leaf plus a separate lemma. The primitive bundles the commute with
its only non-trivial obligation:

```
stochFubini_ofCLM (I : L²(m) →L[ℝ] L²(P)) (φ : A → L²(m)) (hφ : Integrable φ μ) :
    ∫_A I(φ u) dμ(u) = I(fun s ↦ ∫_A φ u s dμ(u))       -- I ∈ {Wiener, Itô, Lévy}
```

Its proof is `integral_comp_comm` *inline* (no named wrapper) plus the one genuine
analytic step, the **L²-representative fact**: the Bochner integral
`∫_A [φ(·,u)] dμ(u)` in `L²(m)` is represented a.e. by `s ↦ ∫_A φ(s,u) du` (loogle
Mathlib first — `integral_integral_swap` may already give it). Two deliberate
non-choices keep it elegant: **no** `clm_comm_paramIntegral` wrapper (renaming a
single Mathlib lemma is the avoid-wrapper anti-pattern — folded inline), and
**no** `StochasticIntegralTower` typeclass (`I` as an explicit CLM argument is
already maximal generality; a class would bundle an isometry the theorem never
uses). The hypothesis `Integrable φ μ = ∫_A ‖φ(·,u)‖_{L²} dμ(u) < ∞` is the sharp
Veraar condition, and on a finite maturity interval `A=[t,T]` follows from joint
square-integrability by Cauchy–Schwarz — so no generality is lost.

This is the same move as the Lévy roadmap's *"the Summit dissolved, not climbed"*:
the shared abstraction that already exists is exactly what makes the hard theorem
cheap. **Consumers beyond HJM:**

- **Itô–Lévy formula** (`#132`) and **Merton PIDE** (`#133`) consume the *Lévy*
  instance — jump term-structure comes almost free once the primitive exists.
- **Vasicek** integrated-rate computation (`VasicekBondPrice`) refactors onto the
  *Wiener* instance — a coherence proof-of-reuse that pays the abstraction back
  into existing code (`docs/bridges.md`).

## 5. Honest scope

**Consumed (library / Mathlib), not re-proved:** `ContinuousLinearMap.integral_comp_comm`;
`ito_formula_expBrownian` (Itô-for-exp, `Foundations/ItoFormulaGBM`); the
martingale ⇔ zero-drift core; the three tower CLMs; FTC/Leibniz calculus.

**Genuinely new:** (a) the L²-representative fact inside `stochFubini_ofCLM` (its
one analytic step, possibly already in Mathlib); (b) the process/pathwise lift
onto `ItoIntegralProcess`; (c) the moving-boundary stochastic-Leibniz assembly
(where `r(t)` emerges); (d) the drift-condition assembly; (e) the bridges.

**Nothing in the crown is assumed.** With the CLM reframing the bond dynamics are
*derived* through F4, so `C4` (the iff) is a genuine `full` result. The only
deferred summit is `G4` Musiela (an SPDE in its own right); it ships `placeholder`
and gets its own follow-up. Fullest-generality integrability side-conditions may
be tightened iteratively — each node declares what it assumes.

## 6. The atomic issue DAG

```
H0 ─┬─► F1 ─► F3 ─► F4 ─► B1 ─┐
    │         ├─► F5 (Wiener + Vasicek refactor)   ├─► B3 ─► D1 ─► D2 ─► C1 ─► C2 ─► C4
    │         └─► F6 (Lévy → #132/#133)      B2 ───┘                        └─► C3 ─┘
    └───────────────────────────────────────────────────────► G1, G2, G3, G4 (bridges)
```

Legend: `id · benchmark-id — title` *(labels · status · formalization_status)*.

**Issue numbers:** H0 #139 · F1 #141 (the `stochFubini_ofCLM` primitive; #140
dissolved into it) · F3 #142 · F4 #143 · F5 #144 · F6 #145 · B1 #146 · B2 #147 ·
B3 #148 · D1 #149 · D2 #150 · C1 #151 · C2 #152 · C3 #153 · C4 #154 · G1 #155 ·
G2 #156 · G3 #157 · G4 #158 (umbrella #138).

### Tier 0 — objects · `FixedIncome/HJM/Model.lean`
- **H0 · `mf-hjm-model`** — the `HJMModel` bundle (`W, f(t,T), α, σ` + adapted /
  measurable / integrable fields) and `hjmBond`, `hjmShortRate`, `bankAccount`,
  `discountedBond`, `starDrift α*`, `starVol σ*`. Defs + basic well-definedness.
  *(new-defs, area:fixed-income · ready · scaffolding)*

### Tier 1 — stochastic Fubini, the shared primitive · `Foundations/StochasticFubini*.lean`
- **F1 · `sc-stochastic-fubini-clm`** (#141, folds in the dissolved #140) — the
  tower-agnostic primitive `stochFubini_ofCLM (I : L²(m) →L[ℝ] L²(P)) …`. Proof =
  `integral_comp_comm` inline + the L²-representative fact (`∫_A [φ(·,u)] dμ`
  represented by `s ↦ ∫_A φ(s,u) du`) — the one analytic step, maybe already in
  Mathlib. No wrapper, no typeclass. **the keystone.** *(foundations · ready · full)*
- **F3 · `sc-stochastic-fubini-ito`** — the one-line Itô instance of F1 at
  `I := itoIntegralCLM_T`: `∫_A (∫_0^T φ dW) du = ∫_0^T (∫_A φ du) dW`. *(foundations · ready · full)*
- **F4 · `sc-stochastic-fubini-ito-process`** — the pathwise all-`t` lift on
  `ItoIntegralProcess` (continuous modification). the form HJM's bond dynamics
  need. *(foundations · blocked-design · full)*
- **F5 · `sc-stochastic-fubini-wiener`** — the Wiener instance + refactor the
  `VasicekBondPrice` integrated-rate step to consume it (coherence). *(foundations, fixed-income · ready · full)*
- **F6 · `sc-stochastic-fubini-levy`** — the Lévy instance via `itoLevyIntegralL2`;
  unblocks `#132` / `#133`. *(foundations · ready · full)*

### Tier 2 — log-bond dynamics · `FixedIncome/HJM/BondDynamics.lean`
- **B1 · `mf-hjm-logbond-fixed-limit`** — fixed lower limit
  `−∫_{t0}^T df(t,u) du` via F4. *(fixed-income · blocked-design)*
- **B2 · `mf-hjm-logbond-leibniz`** — the moving-boundary correction
  `+r(t)dt = f(t,t)dt`; the stochastic-Leibniz node. *(fixed-income · blocked-design)*
- **B3 · `mf-hjm-logbond-dynamics`** — assemble
  `dY = [r − α*] dt − σ* dW`. *(fixed-income · blocked-design)*

### Tier 3 — bond & discounted-bond dynamics · `FixedIncome/HJM/DiscountedBond.lean`
- **D1 · `mf-hjm-bond-dynamics`** — Itô-for-exp on `P = exp Y` (consume
  `ito_formula_expBrownian`): `dP/P = [r − α* + ½σ*²]dt − σ*dW`. *(fixed-income · blocked-design)*
- **D2 · `mf-hjm-discounted-bond-dynamics`** — subtract `r dt`:
  `dZ/Z = [−α* + ½σ*²]dt − σ*dW`. *(fixed-income · blocked-design)*

### Tier 4 — the drift condition, the crown · `FixedIncome/HJM/DriftCondition.lean`
- **C1 · `mf-hjm-drift-integrated`** — martingale ⟹ `α* = ½σ*²` (consume
  martingale ⇔ zero-drift). *(fixed-income · blocked-design)*
- **C2 · `mf-hjm-drift-condition`** — differentiate in `T` ⟹ **`α = σσ*`**
  (crown, forward direction). *(fixed-income · blocked-design)*
- **C3 · `mf-hjm-drift-converse`** — `α = σσ*` ⟹ integrate ⟹ martingale ⟹
  no-arbitrage. *(fixed-income · blocked-design)*
- **C4 · `mf-hjm-drift-iff`** — package the equivalence: discounted-bond
  martingale ↔ HJM drift condition. the headline. *(fixed-income · blocked-design)*

### Tier 5 — bridges (tower integration, finance-facing) · `FixedIncome/HJM/Bridges.lean`
- **G1 · `mf-hjm-short-rate`** — `r(t) = f(t,t)` and the induced short-rate SDE. *(fixed-income · blocked-design)*
- **G2 · `mf-hjm-ho-lee`** — `σ` constant ⟹ the Ho–Lee affine term structure. *(fixed-income · blocked-design)*
- **G3 · `mf-hjm-vasicek-bridge`** — `σ(t,T) = σ e^{−κ(T−t)}` recovers the
  existing `VasicekBondPrice` affine term structure. **the seam into existing
  work.** *(fixed-income · blocked-design)*
- **G4 · `mf-hjm-musiela`** — the Musiela parametrization `r(t,x) = f(t,t+x)`;
  its own SPDE summit. *(fixed-income · blocked-design · placeholder)*

## 7. Module layout

```
MathFin/Foundations/StochasticFubini.lean          -- F1, F2
MathFin/Foundations/StochasticFubiniIto.lean        -- F3, F4  (+ F5 Wiener instance)
MathFin/Foundations/StochasticFubiniLevy.lean       -- F6      (near the Lévy operator)
MathFin/FixedIncome/HJM/Model.lean                  -- H0
MathFin/FixedIncome/HJM/BondDynamics.lean           -- B1, B2, B3
MathFin/FixedIncome/HJM/DiscountedBond.lean         -- D1, D2
MathFin/FixedIncome/HJM/DriftCondition.lean         -- C1, C2, C3, C4
MathFin/FixedIncome/HJM/Bridges.lean                -- G1, G2, G3, G4
```

Each `module`-header file carries `@[expose] public section`; each imports a
`MathFin` module and re-exports, not `import Mathlib` (per the module-system
rule). File splits may consolidate if a node proves small.

## 8. Benchmarks, ledger, audit, values cadence

- Each `full` / `library_wrapper` node lands a benchmark entry
  (`sc-stochastic-fubini-*` in `stochastic_calculus.json`, `mf-hjm-*` in
  `mathematical_finance.json`) that imports the module and re-exports the named
  lemma in 5–25 lines.
- After every node: regenerate `MathFin/AxiomAuditGen.lean`
  (`python3 -m tools.verify.axiom_audit_gen --write`), add the coverage row, and
  run `python3 -m tools.verify.ledger status` → `verify` on the stale entries.
- `#guard_msgs`-pin the load-bearing constants in `AxiomAudit.lean`
  (`stochFubini_ofCLM`, the Itô-process Fubini, `mf-hjm-drift-condition`).
- The values-review cadence gate (`test_values_review_is_current`) fires at +12
  entries; refresh `docs/values-review.md` with the ranked backlog when it does.

## 9. Build order

1. **Keystone first:** `F1` (the `stochFubini_ofCLM` primitive) → `F3` (its Itô
   instance) — every downstream tier waits on it. `F1`'s one hard step is the
   L²-representative fact (maybe already in Mathlib).
2. `F4` (process lift) + `H0` (objects) in parallel.
3. Critical path to the crown: `B1/B2 → B3 → D1 → D2 → C1 → C2 → C4`.
4. Bridges `G1 → G2 → G3` (the Vasicek seam is the payoff); `G4` Musiela deferred.
5. Tower payback in parallel once `F3/F4` land: `F5` (Vasicek refactor), `F6`
   (Lévy → `#132/#133`).

## 10. Risks & open questions

- **The L²-representative fact** (inside `F1`/`stochFubini_ofCLM`) is the analytic
  crux — if Mathlib's `Lp`/Bochner-representative API (`integral_integral_swap`)
  doesn't line up cleanly, this is the step that could grow. Mitigation: it is
  fully general and reusable, so the investment is never HJM-only.
- **B2 moving-boundary Leibniz** mixes a deterministic boundary derivative with a
  stochastic integrand differential; needs care that it is not a hidden second
  Fubini. Scope each assumption explicitly.
- **Martingale vs local-martingale** in (D): the clean statement is
  local-martingale ⇔ zero-drift; upgrading to a true martingale (hence genuine
  no-arbitrage) needs an integrability/Novikov-type side condition. State the
  local-martingale form as the crown; note the upgrade as a declared refinement.
- **G3 Vasicek bridge** must land on the *existing* `vasicekBondPrice_affine`
  statement, not a re-derivation — else it is a wrapper, not a seam.

## 11. References

- Heath, Jarrow, Morton (1992), *Bond pricing and the term structure of interest
  rates*, Econometrica 60(1).
- Björk, *Arbitrage Theory in Continuous Time*, 3rd ed., ch. 23–25 (HJM, short
  rate, Musiela).
- Filipović, *Term-Structure Models: A Graduate Course*.
- In-repo: `Foundations/Numeraire`, `FixedIncome/ForwardMeasure`,
  `FixedIncome/ForwardRate`, `FixedIncome/VasicekBondPrice`,
  `Foundations/ItoFormulaGBM`, `Foundations/ItoIntegralCLM`,
  `Foundations/ExtendOfNormIsometry`, `Foundations/PoissonCompensatedIntegralOperator`.
- Mathlib: `ContinuousLinearMap.integral_comp_comm`.
