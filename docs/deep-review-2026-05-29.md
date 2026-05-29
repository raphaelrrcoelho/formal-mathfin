# Deep review — 2026-05-29 (the Itô-calculus stack)

A contract-aligned, adversarial review of this session's Itô-calculus work
(the CLM, the process scaffold, the discrete squaring/cubing identities, the
continuous L² Itô-squared formula, the 2D Itô formula, GBM-as-SDE, and the
BS-PDE routing). The lens is the six standing values: inspired math quality,
Mathlib/Degenne coherence, zero slop, architectural ingenuity, first
principles, superior concept clarity.

Method: two independent adversarial reviewers (faithfulness/vacuity;
architecture/slop) fanned out across the new files, plus a first-principles
read of the load-bearing CLM density argument and a direct source-check of
every flagged theorem. Every finding below was verified against the actual
code, not taken on a reviewer's word.

**Headline verdict.** The *mathematics* is sound and the genuinely-hard pieces
are real: the CLM density argument (orthogonal-complement → π-λ set-integral
vanishing → `ae_eq_zero`) is correct and well-built; the GBM partials are
genuine `HasDerivAt` chain-rule derivations; `itoSquared_L2_tendsto` is a real
L² convergence; the discrete telescoping identities are honest specialisations.
**The failure was in honesty-of-framing, not correctness**: a cluster of
`unfold; ring` algebraic bridges were dressed in derivation language
("solves the SDE", "no-arbitrage gives the PDE", "the full SDE") in docstrings
and the blueprint, erasing the `full` vs `reduced_core` distinction the project
itself insists on. Plus one architectural miss (a `one_mul` wrapper), one
premature-infra file, and a deeper architectural shortcut (below). **All
docstring/framing violations have been fixed in this pass; the one genuine
mathematical upgrade (`gbm_solves_sde` made `full`) was applied; the deeper
architectural items are documented with a concrete fix and left for a
continuation.**

---

## The deepest finding — the L²-Itô formula bypassed the CLM (raised by RC)

`itoSquared_L2_tendsto` proves `∑ B_{t_k}·ΔB_k → ½(B_T²−B_0²−T)` in L² via the
discrete squaring identity + `tendsto_qv` (the quadratic-variation track). It
**never mentions `itoIntegralCLM_T`** — the canonical continuous Itô integral
the session built at 733 LOC. The limit is *named* `∫B dB` by the docstring,
not *proved* to equal the CLM-integral of `B`.

Consequence: the library holds two unconnected notions of `∫₀ᵀ B dB` (the
abstract CLM one; the concrete QV-limit one) with no theorem bridging them, and
the CLM has **zero consumers** precisely because the one result that should
have validated it took the QV shortcut instead. This is the same hole as
agent-B Finding 2 and the F1 bridge gap, seen from the proof side: "build
bridges, not replacements" was violated — the QV track *replaced* the CLM here
rather than bridging to it.

Honest grade: **expedient and true, but sub-principled.** The QV route is a
legitimate, transparent elementary proof (the `+T` term *is* the quadratic
variation), but it is a *parallel* proof, not a *structural* one.

**The principled fix (next continuation, ~300-400 LOC):**
```
itoIntegralCLM_T_of_brownian :
    itoIntegralCLM_T T hBmeas ⟦s ↦ B s⟧ = ½ • ⟦B_T² − B_0² − T⟧
```
— approximate `s ↦ B_s` by left-endpoint step processes in `Lp 2 (trim_T)`,
push through CLM-continuity (`itoIntegralCLM_T V_n` evaluates *by construction*
to the Riemann sum), identify the limit via `itoSquared_L2_tendsto`. This
bridges the two notions and gives the CLM its first genuine consumer —
collapsing F1 and the no-consumer finding at once. It is the single
highest-value next step in the whole Itô track.

---

## Findings & actions

| # | Finding | Severity | Status |
|---|---|---|---|
| R1 | `gbm_solves_sde` took the partials as *free scalar arguments* — nothing forced them to be the real derivatives; proof was `unfold; ring`. The "GBM solves the SDE" content lived entirely in the separate, type-unlinked `hasDerivAt_*` lemmas. | **serious** | **FIXED** — restated with the partials bound by `HasDerivAt` hypotheses; `HasDerivAt.unique` now *forces* them to the genuine derivatives. The theorem is now genuinely `full`: a caller cannot fake the partials. Diffusion folded in. |
| R2 | `gbm_diffusion` was literally `(1:ℝ)*(σS) = σS` (= `one_mul`) with a docstring claiming "Together with gbm_solves_sde this is the full SDE." A forbidden wrapper (`feedback_avoid_wrapper_lemmas`) + an overclaim. | moderate | **FIXED** — deleted; the diffusion coefficient is now a conjunct of the (full) `gbm_solves_sde`, where `f_x` is pinned to `σS` by hypothesis, so it is no longer a free-standing `one_mul`. |
| R3 | `bs_pde_eq_itoDrift2D_minus_rV` docstring narrated "No-arbitrage (`e^{−rt}V` is a Q-martingale...) is exactly this set to 0" — a derivation that is **not stated or proved** here (the theorem is an `unfold; ring` polynomial identity). | moderate | **FIXED** — docstring rewritten: states plainly it is a polynomial identity routing the PDE LHS through the shared `itoDrift2D`, with an explicit "what this does NOT prove" note (the martingale step is deferred). |
| R4 | `docs/blueprint.md` presented the GBM-SDE and BS-PDE-from-Itô nodes as ✅ ("solves the GBM SDE", "a *derived* SDE solution rather than a posited model", "no-arbitrage gives the PDE"), erasing the `full`/`reduced_core` split the contract requires. The blueprint is where readers calibrate depth. | **serious** | **FIXED** — both nodes demoted to a new 🚧 status ("partially formalized — genuine core + explicitly deferred lift"), added to the legend. The genuine pieces (partials, L² Itô-squared) and the deferred pieces (continuous SDE solution, martingale→PDE) are now separated in the prose. |
| R5 | `ItoIntegralProcess.lean` — unconsumed scaffold whose docstring claimed downstream consumers (the L²-Itô formula, SDEs, stopping times) that **do not exist** (the L²-Itô work bypassed it via QV). Premature infra under the project's own "load-bearing only when consumed" rule. | **serious** | **PARTIALLY FIXED** — docstring rewritten with a prominent "STATUS — staging only, no current consumer" honesty note citing the architecture rule; its two non-load-bearing linearity-lemma pins removed from `AxiomAudit.lean`. **Deletion deferred to RC's call** (see open question). |
| R6 | Redundant `import Mathlib` in `ItoLemma2D.lean` and `PDEFromIto.lean` (both get Mathlib transitively via `ItoLemma`). | minor | **FIXED** — dropped, with the same transitive-import comment the F4 fix used on `ItoFormulaSquaredL2.lean`. |
| R7 | `bs_pde_from_no_arbitrage` (pre-existing) named/blueprint-titled as a no-arbitrage derivation, but is a polynomial iff. | minor | **FIXED (blueprint)** — node demoted to 🚧 with the deferred-martingale-step note. Theorem name left (rename is churn; docstring already honest). |
| R8 | The `'` rearrangement lemmas (`discrete_squaring_identity'`, `discrete_cubing_identity'`) are `linarith`-restatements with no consumer. | minor (low-harm) | **LEFT** — kept; they are cheap canonical-shape variants. Flagged for trim if no consumer appears. |

## What is genuinely good (verified, not adjusted)

- **CLM density argument** (`simpleAssembly_T_denseRange`, `ItoIntegralCLM.lean`):
  read in full — the orthogonal-complement reduction, the basic-rectangle
  `iocSP_T` construction, the inner-product-as-set-integral identification, and
  the π-λ `setIntegral_eq_zero_of_orthogonal_pred` are all real, correct, and
  well-structured. This is the keystone and it holds.
- **GBM partials** (`hasDerivAt_gbmValue_space/_time/_space_space`): genuine
  `HasDerivAt` derivations from the `Real.exp` chain rule. The real math
  content of the GBM section. (Now properly *consumed* by the full
  `gbm_solves_sde`.)
- **`itoSquared_L2_tendsto`**: a genuine L² convergence (reduces to the real
  `tendsto_qv` squeeze). `full`. (The framing caveat is R-deepest, not a
  correctness issue.)
- **Discrete telescoping identities** (`discrete_squaring/cubing_identity`,
  `discrete_ito_formula_2d`): honest specialisations of a real telescoping
  identity; the polynomial Taylor remainders (`_sq/_cube/_quartic`) are true
  closed-form computations.
- **Mathlib/Degenne coherence**: no duplication of Mathlib's analytic Taylor
  theorem (the discrete remainder is a deliberately different formal object);
  exp chain-rule correctly reused; naming consistent.

## Open question for RC (the one judgment call I did not unilaterally make)

`ItoIntegralProcess.lean` (R5): the overclaim is fixed (honest status note), but
the file remains *premature infrastructure* — a thin `SimpleProcess.integral`
projection with no consumer, which the actual L²-Itô work bypassed. Two honest
options:
1. **Keep as staging** (current state) — a labelled landing-pad for the
   continuous-Itô-integral-as-process, on the bet the next continuation builds
   on it.
2. **Delete it** — and build the process integral *directly against the CLM*
   when the time comes (which is the more principled construction anyway, per
   the deepest finding above). Git preserves it.

I lean to (2) on zero-slop grounds, but it touches your Itô-climb staging, so
it's your call. Everything else in this review is already applied and builds.
