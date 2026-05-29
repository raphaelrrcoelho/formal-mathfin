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
| R5 | `ItoIntegralProcess.lean` — unconsumed scaffold whose docstring claimed downstream consumers (the L²-Itô formula, SDEs, stopping times) that **do not exist** (the L²-Itô work bypassed it via QV). Premature infra under the project's own "load-bearing only when consumed" rule. | **serious** | **RESOLVED** — deleted as the hollow projection it was (option 2 below), then *recreated principled* per RC. The new file carries genuine analytic content rather than a deferred-everything stub: `memLp_itoSimpleProcess` (`(V●B)_t ∈ L²(μ)` at **every** `t`, via the active/past truncation case-split on the same adapted-increment engine as `memLp_itoSimple`), the explicit truncated increment-sum `itoSimpleProcess_apply`, and `itoSimpleProcess_eq_itoSimple` tying the process to the **terminal CLM base object**. Built on Degenne's `SimpleProcess.integral` (so `V`-linearity is inherited, not re-proved). Two genuine-content pins re-added to `AxiomAudit.lean`; honest docstring scopes what is still deferred (adaptedness/continuity/martingale/time-indexed isometry) as the *next, consuming* layer. |
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

## Open question for RC — RESOLVED (2026-05-29)

`ItoIntegralProcess.lean` (R5): RC took option (2) — delete the thin projection —
**and then** asked to add it back "in a principled way". Both halves are now done.
The hollow scaffold is gone; the file that replaced it is not a projection-with-a-
status-note but a real layer: it proves `(V●B)_t ∈ L²(μ)` at every `t`
(`memLp_itoSimpleProcess`), the explicit truncated increment-sum, and the terminal
agreement with the CLM base object (`itoSimpleProcess_eq_itoSimple`) — i.e. it
*connects to* the L²/CLM foundation instead of paralleling it, and inherits
`V`-linearity from Degenne's `SimpleProcess.integral` rather than re-deriving it.
What stays deferred (adaptedness of `t ↦ (V●B)_t`, pathwise continuity, the
martingale property, the time-indexed isometry) is now the honestly-scoped *next*
layer that will **consume** `memLp_itoSimpleProcess`, not an unconsumed promise.

The two earlier options, for the record:
1. ~~Keep as staging~~ — rejected (zero-slop: a labelled landing-pad with no
   consumer is still premature infra).
2. **Delete, then rebuild with genuine content connected to the CLM** — taken.

Everything in this review is applied and the full library + `AxiomAudit` pins build.

---

# Library-wide sweep (2026-05-29) — "are there more like this?"

Four adversarial reviewers fanned out over all 148 files / 10 directories,
hunting the same deviation patterns (overclaiming docstring on `ring`/`rfl`
proofs; spec-with-axiomatized-conclusion; wrapper lemmas; premature infra;
vacuity; tautology-dressed-as-connection). Every substantive finding was
re-verified against source before action. **Verdict: the library is
overwhelmingly clean and honest** — consistent with the 2026-05-26 audit. The
residual deviations were few, and notably the *same two patterns* this session
introduced in the Itô files recurred in a handful of older files. All
Lean-level + doc-level findings are FIXED; one benchmark-status overclaim
FIXED; build green 8653/8653, router test green, 0 placeholders.

## Genuine deviations found + fixed

| # | File | Pattern | Severity | Fix |
|---|---|---|---|---|
| L1 | `Foundations/VarianceSwapEquivalence.lean` `varianceSwap_log_eq_QV_limit_value` | **tautology-dressed-as-connection** — second conjunct was `σ²·T = σ²·T` by `rfl`, with an "equivalence of two characterisations" docstring; the imported QV-limit functional was never referenced (the *exact* `gbm_diffusion` pattern). | moderate→serious | **FIXED, principled** — restated to consume the genuine `tendsto_expected_bsLogPrice_equipartition_sum` (a real `Tendsto → σ²·T`) under a `BrownianQuadraticVariation` hypothesis; both conjuncts now real, `hB`/`hT_nonneg` load-bearing. Mirrors the `gbm_solves_sde` fix. |
| L2 | `docs/bridges.md` row 41 (Vasicek) | **overclaim contradicting the file's own docstring** — "First full SDE pricing in the library — variance computation uses simple-Itô-isometry", but `VasicekSDE.lean` posits mean/variance as bare `def`s, imports no isometry, proves only `positivity` + `t=0`. (The GBM-SDE overclaim pattern.) | serious (docs) | **FIXED** — row rewritten to match the file: "terminal-distribution form (stated, not derived)", SDE→law derivation "open, gated on the continuous Itô integral". |
| L3 | `RiskMeasures/RockafellarUryasev.lean` + benchmark `mf-cvar-rockafellar-uryasev` | **named after a famous variational theorem, proves a `ring` identity** — `unfold;ring` rearrangement of the CVaR/VaR defs (no `inf`, no `E[(L−c)⁺]`); declared `formalization_status: full` in the benchmark (the `bs_pde`-named-after-no-arbitrage pattern, in the delivery layer). | moderate | **FIXED** — lemma renamed `gaussianCVaR_rockafellarUryasev → gaussianCVaR_eq_VaR_plus_tail_term` (the honest name the Results list already used); title/docstring reframed to "additive form, NOT the variational theorem"; benchmark status `full → reduced_core` with honest scope; lean ref updated. (full 211→210, reduced 16→17.) |
| L4 | 5 stale docstrings: `FeynmanKacHeatEquation` (listed 2 nonexistent thms), `StandardGaussianMGF` (1 nonexistent), `StatePrices` (name drift), `BlackScholes/PDE` (`bs_pde_satisfied`→`bs_pde_holds`), `BisectionIV` (`bsV_strictMono_in_σ`→`bsV_strictMonoOn_sigma`) | zero-slop / concept-clarity (docstrings naming theorems that don't exist) | minor | **FIXED** — all corrected to the actual theorem names. |
| L5 | `Performance/Ratios.lean` module docstring | FOC-as-optimality — "Kelly fraction *maximizes* log-growth" but only `g'(f*)=0` (the FOC) is proved (per-lemma docstrings were already correct). | minor | **FIXED** — reworded to "critical point (`g'(f*)=0`, the FOC proved here); maximizer because `g` concave — concavity not formalized." |

## Deferred (structural, NOT honesty violations — flagged, not yet acted)

- **Wrapper lemmas** (`feedback_avoid_wrapper_lemmas`): `FixedIncome/ForwardRate.lean`
  `forwardRate_nonFlat_eq` (a byte-identical re-export of the lemma above it);
  `Binomial/Bermudan.lean` `bermudan_le_american`/`european_le_bermudan` (one-line
  `Finset.sup'_mono` wrappers). Honestly disclosed in their headers (no
  overclaim), so deferred — delete/inline in a structural-cleanup pass.
- **Benchmark `formalization_status` re-audit**: the Rockafellar mislabel
  (`full` that was `reduced_core`) surfaced *by accident* via the rename. The
  agents audited the Lean files, not systematically the 234 benchmark status
  *declarations*. `mathematical_finance.json` is 185/186 `full` — mostly
  justified (closed-form Greeks ARE genuine `HasDerivAt` derivations, per the
  BS audit), but a dedicated pass cross-checking every `full` declaration
  against its proof tactic is the natural next sweep. Recommended, not yet run.

## What the sweep confirmed is genuinely sound (spot-checked, not adjusted)

- The deep Foundations probability machinery (BrownianMartingale, WienerIntegralL2,
  ItoIsometryAdapted, QuadraticVariationL2, FeynmanKac, LpContinuousMartingaleConvergence,
  GaussianGirsanov) — genuine multi-step derivations, accurate docstrings.
- BlackScholes (40 files) — **entire cluster clean**: every Greek a real
  `HasDerivAt` derivation; pricing via genuine Gaussian integration; `*Hyp`
  bundles pin the *law of the driver*, not the price (no conclusion-smuggling);
  unused hypotheses are `_`-prefixed AND disclosed.
- Binomial/Futures/FixedIncome (35 files) — clean apart from L2 + the two
  wrappers; the substantive files (PathReflection, CRRConvergence, DriftLimit,
  DurationSensitivity, FTAPTwoState, ReplicatingUniqueness) are real
  first-principles derivations.
- Portfolio/Performance/RiskMeasures/Actuarial/DeFi (27 files) — clean apart
  from L3 + L5; the FOC files (`SharpeFOCDerivation`, `RiskParityFOC`,
  `TangentPortfolio`) are *scrupulously* honest (explicit "verifies by algebra,
  does not derive from maximization" disclaimers); `Markowitz` genuinely proves
  global minimality (companion `_ge_min` via completing-the-square).

---

# Benchmark-status re-audit (2026-05-29) — the delivery-counting layer

The library files were clean; the *benchmark `formalization_status` declarations*
were a separate surface the file-audit didn't systematically cover (the
Rockafellar mislabel had surfaced only by accident, via a rename). So: four
adversarial reviewers over all 11 benchmark files / 251 theorems, tracing each
declared status to the underlying lemma's actual statement+proof. Criterion: the
disqualifier is NOT "uses `ring`" (put-call parity by `ring` is genuinely
`full`); it is the *Rockafellar gap* — name/description evoking more than the
proof delivers (mode A), conclusion-smuggled-into-a-hypothesis (mode B), or an
unfaithful library wrapper (mode C).

**Result: 13 over-credited entries reclassified; delivery-ready 234 → 222**
(full 210→203, library 24→19, reduced 17→29, placeholder 0). Router test green.
The vast majority of `full` declarations are genuine (BS Greeks are real
`HasDerivAt` derivations; pricing is real Gaussian integration; closed-form
algebra on independently-defined quantities is legitimately `full`). The 13:

| benchmark | was | now | why |
|---|---|---|---|
| `mf-tangent-portfolio-foc` | full | reduced_core | `by ring` cross-product identity named "FOC from Sharpe maximization" — no calculus (mode A; exact Rockafellar twin) |
| `mf-american-supermartingale` | full | reduced_core | `le_max_right` on the Bellman def; "supermartingale under risk-neutral measure" not formalized (A) |
| `mf-american-intrinsic-bound` | full | reduced_core | `le_max_left` on the Bellman def (definitional) |
| `mf-kmv-merton-pd` | full | reduced_core | only the `≤1` probability bound proved; "PD = Φ(−d₂)" is the model def (A) |
| `mf-markowitz-n-psd` | full | reduced_core | `h_psd w` — PSD hypothesis instantiated at `w` (mode B, conclusion-in-hypothesis) |
| `mf-newton-raphson-fixed-at-root` | full | reduced_core | definitional unfold (`f σ=0 ⟹ σ−f σ/f' σ=σ`) |
| `mart-thm-2.3.6` "Optional Stopping" | library_wrapper | reduced_core | wraps the **bounded-time submartingale inequality**, claims the **UI-martingale equality** `E[M_τ]=E[M_0]` (mode C) |
| `bm-thm-5.1.5` "BM Martingale" | full | library_wrapper | one-line `:= IsPreBrownian.isMartingale` (Degenne re-export); also "B²−t" claim isn't in the snippet |
| `mc-thm-1.2.11/1.3.12/1.4.25/1.4.32/1.4.40` (×5) | library_wrapper | reduced_core | `library_wrapper` credit rested on the **dropped Isabelle backend**; active Lean is a structure-with-conclusion-field + projection (matches how `poisson_processes` already tiers its Isabelle-backed items) |

Also softened (kept `library_wrapper`, faithful for the a.s. part): `mart-thm-2.5.1`
("L² convergence" → a.s.; the in-L² half isn't wrapped) and `mart-thm-2.5.3`
(integrability of the limit not separately wrapped). The benchmark *code* was
untouched in all cases — only metadata/name/description.

**Build-staleness flagged (separate from status, NOT yet fixed — needs the
verify harness to confirm):** three benchmark snippets may not compile against
the current Mathlib pin — `mart-thm-2.2.9` (`hA_bdd` shape mismatch vs
`martingaleTransform_isMartingale`), `cv-cond-exp-tower` (lowercase
`condexp_condexp_of_le`, renamed to `condExp_…`), `dist-thm-B.1.2-affine`
(`gaussianReal_const_mul`/`_add_const` possibly renamed). A benchmark that
doesn't compile but is declared delivery-ready is itself an honesty risk;
recommended to run `docker compose … verify benchmarks/<file>.json` on these
three and fix or downgrade. Held for a verify-harness pass.

## Upgrade-properly round — earning `full` back by doing the real work

In response to "can't we move them all to full *properly*?": the answer is *only
where the genuine derivation can be supplied* — relabeling up is the very
overclaim this review removed. Going through the 13 reclassified entries:

* **Already had the genuine derivation in the library** (the benchmark was just
  wrapping the shallow lemma) — re-pointed, **earned back to `full`**, both
  compile-verified:
  - `mf-tangent-portfolio-foc` → `sharpeSqTwo_critical_iff_crossProduct_FOC`
    (`SharpeFOCDerivation.lean`): the Sharpe FOC as a genuine `HasDerivAt`
    critical-point characterisation (derivative + uniqueness + factorisation),
    not the `ring` cross-product shadow `tangentTwo_satisfies_FOC`.
  - `mf-kmv-merton-pd` → `kmvPD_eq_one_sub_survival_probability`
    (`KMVMertonStructural.lean`): KMV PD = the *actual* risk-neutral default
    probability `1 − Q(V_T>F)`, via `riskNeutralProb_S_T_gt_K` — not the `≤1`
    bound.
  - This also surfaced a NEW shadow: `mf-kmv-survival-Phi-d2` was `full` but
    only proves the normal-CDF symmetry `1 − Φ(−x) = Φ(x)` (algebra), with the
    *probabilistic* survival content actually living in the lemma now wrapped by
    `mf-kmv-merton-pd`. Demoted `full`→`reduced_core`. (Net: 222→223 delivery,
    now genuine.)
* **Inherently not `full`** — no deeper theorem exists; they are one-line
  definitional facts: `mf-american-intrinsic-bound` (`g ≤ max(g,·)` is true *by
  definition*), `mf-newton-raphson-fixed-at-root` (the deeper theorem would be
  Newton *convergence*, a different statement). Honest `reduced_core`.
* **Gated on machinery not in Lean** — `full` needs a real new development:
  `mf-american-supermartingale` (measure-theoretic conditional expectation /
  filtration on the binomial model), `mf-markowitz-n-psd` (a probability space
  of random returns to *derive* covariance-PSD instead of assuming it),
  `mart-thm-2.3.6` (UI-martingale optional-stopping *equality* — the bounded
  martingale equality is achievable from the submartingale inequality both ways,
  a genuine but non-trivial follow-up), the 5 `markov_chains` (deep
  ergodic / Perron-Frobenius theory). Honest `reduced_core` / `library_wrapper`
  until that machinery lands.
* **Genuinely a wrapper** — `bm-thm-5.1.5` is a faithful one-line Degenne
  re-export: `library_wrapper` is the correct tier and already counts as
  delivery-ready.

A tangent-weight-*specific* full statement (`tangentWeightTwo` *is* a Sharpe
critical point) is achievable — the algebra reduces to `tangentTwo_satisfies_FOC`
after clearing the denominator `D` — but the denominator-cancellation needs
careful Lean iteration; deferred rather than shipped unverified.
