# Values review — the final verification

The mechanical gates (`tests/test_values.py`, `AxiomAudit*.lean`, the
verification ledger, the CI gates in `build.yml`) enforce everything a
machine can check. This protocol covers what a machine cannot: the judgment
lenses that define the repo's quality bar. The **review is judgment** — a
multi-agent panel reading the work — and the **pipeline enforces that it
happens**: `tests/test_values.py::test_values_review_is_current` fails when
the corpus has grown more than 12 entries past the last recorded verdict
below. A regex cannot check "beautiful"; a regex can check "nobody looked."

## The eight lenses

1. **Inspired math quality** — each result earns its place: a structural
   fact or a clean mechanism, not bookkeeping dressed as a theorem.
2. **Mathlib / BrownianMotion (Degenne) coherence** — consume the libraries'
   machinery, never re-derive it; choose the canonical upstream API; no thin
   wrappers around single upstream lemmas.
3. **Zero slop** — no opaque discharges where a certificate-shaped proof
   exists, no ring-fallback hiding the conceptual step, no duplicated
   sub-derivations, no dead hypotheses.
4. **Architectural ingenuity** — the decomposition is the right shape: each
   lemma carries one idea, the pieces compose so future results get cheaper,
   nothing is proved at the wrong level of generality.
5. **First principles** — conclusions are derived from honest hypotheses;
   no hypothesis secretly contains the conclusion; no theorem that is its
   own definition unfolded.
6. **Mathlib / BrownianMotion idiomatic register** — naming, hypothesis
   style, namespace and `variable` discipline, statement shapes a Mathlib
   reviewer would accept.
7. **Concept clarity** — every docstring tells the honest mathematical
   story (what is proved, from what, what is *not* claimed); a strong
   probabilist reads the statement and says "yes, that is the theorem."
8. **Beautiful, elegant math** — the proof is the obviously-right argument
   once seen; the writeup neither obscures a beautiful idea nor dresses up
   a trivial one.

## Protocol

- **When**: at the close of any session that adds or changes proof content;
  at latest every 12 corpus entries (the CI ratchet's slack — one session's
  growth).
- **How**: at least three independent review agents, the lenses split among
  them, reading the session's diff and its context (read-only; never running
  Lean). Findings are triaged blocking / minor / nit. **Blocking findings
  are fixed before the verdict is recorded**; minor findings become recorded
  actions with owners (usually: next session's opening move).
- **Record**: append a verdict block below, headed exactly
  `## YYYY-MM-DD — commit <sha> — corpus <N>` (the test parses this line),
  with per-lens verdicts and the findings ledger. Verdicts are honest:
  PASS-WITH-NOTES is a normal outcome; an undeserved PASS is itself a values
  violation.

## Verdict log

## 2026-06-28 — working tree (uncommitted) — corpus 295 — localized (exponential-growth) time-dependent Itô formula: the rung-3 unlock to GBM

**Scope.** New proof content in `Foundations/ItoFormulaLocalized.lean` (`SmoothTrunc`,
`abs_le_of_expGrowth_deriv`, `fCut`/`cutoff_bddDeriv`, `pathIntegral_expGrowth_memLp`,
`boundary_tendsto_L2`, `drift_tendsto_L2`, headline `ito_formula_td_localized`),
`Foundations/BrownianExpMoment.lean` (Brownian marginal exponential moments), and the
strict generalization+exposure of `WeightedQuadraticVariation.tendsto_riemann_continuous`
(global → local `[0,T]` bound) and `measurable_pathIntegral` (drop the uniform bound). Corpus
entry `sc-ito-formula-localized` (`full`, axioms-clean `[propext, Classical.choice, Quot.sound]`).

**Panel.** Two independent reviewers, four lenses each.

| lens | verdict |
|---|---|
| inspired math | PASS |
| Mathlib/Degenne coherence | PASS |
| zero slop | PASS-WITH-NOTES |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS |
| beautiful, elegant math | PASS-WITH-NOTES |

**Blocking findings**: none.

**Checks that mattered.** (1) The localization recovers the limit integrand by the Itô
**isometry** (two-way: forward to bound `aₙ`, backward to make `(gfxₙ)` Cauchy) +
completeness + CLM continuity — never an explicit trim-L² realization of `s ↦ f_x(s,B_s)`;
the elegant route. (2) `pathIntegral_expGrowth_memLp` gets its L² bound by Fatou over
left-endpoint Riemann sums + discrete Cauchy–Schwarz × the per-marginal exponential moment —
**no Tonelli, no joint measurability** — which is strictly more than `memLp_pathIntegral_process`
and the honest way to avoid the Carathéodory wall the rest of the tower carefully sidesteps.
(3) The result is *derived*, not assumed: `boundary_tendsto_L2`/`drift_tendsto_L2` target the
**true** `f` (boundary `f(T,B_T)−f(0,B_0)`, drift `f_t+½f_xx`), and the conclusion is the
genuine Itô identity. (4) The single extra cost vs the bounded engine — joint continuity of
`f_t` — is disclosed honestly in the file/headline/corpus docs: the per-variable `HasDerivAt`
hyps give only *separate* differentiability, and exp-growth (unlike a global derivative bound,
which feeds `continuous_uncurry_of_bdd_partials`) does not supply joint continuity. (5)
Consumes the right Mathlib/Degenne machinery throughout (`ContDiffBump` antiderivative,
Gaussian MGF, `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`,
`Finset.sum_mul_sq_le_sq_mul_sq`, `lintegral_liminf_le`, the existing `itoIntegralCLM_T_norm`
isometry and `tendsto_norm_toLp_sub'` bridge); the WQV change is backward-compatible (the
in-file callers still compile) and genuinely needed by the new lemma.

**Recorded actions.**
1. *(done in this review)* removed dead code the panel found — an unused `have h1` (drift
   integrand bound, `nlinarith` re-derives it) and two unused `hM1 : 0 ≤ S.M₁` (only `M₁²`,
   structurally nonneg, is ever used).
2. *(done in this review)* replaced two trivial-monotonicity `nlinarith`s in `cutD2_bdd`/
   `cutD3_bdd` with the named `le_mul_of_one_le_right`; fixed two deprecated
   `integrable_finset_sum`/`integral_finset_sum` → `…finsetSum`.
3. *(nit, accepted)* `SmoothTrunc.cont₁/cont₂` are derivable from the `hasDeriv` fields; kept
   as a convenience (consumed in four places). `pathIntegral_expGrowth_memLp`'s `0 ≤ K`
   precondition is unused by the proof (K² absorbs the sign) but kept as honest API for the
   bound constant.
4. *(nit, open)* the "reaches GBM/Black–Scholes" applicability claim has no consumer wiring it
   to a pricing module yet — tracked on the roadmap open frontier (the Itô formula against an
   Itô process `∫ f'(X) dX`).



The first time the deep analytic Itô tower feeds a pricing module at the
*integral-law* level (not the drift-algebra level). Two new files:
`MathFin/Foundations/WienerIntegralGaussian.lean` proves the distributional
fact the isometry construction left open — a deterministic-integrand Wiener
integral is Gaussian, `μ.map (wienerIntegralLp B hB T f) = gaussianReal 0 ‖f‖²`
(`wienerIntegralLp_map_eq_gaussianReal`) — by the characteristic-function
route: simple-process Gaussianity (`IsGaussianProcess.of_isGaussianProcess` on
the scaled-increment family + `HasGaussianLaw.map_eq_gaussianReal`, mean 0 from
`IsPreBrownianReal.integral_eval`, variance the Itô isometry
`wiener_assembly_isometry`), lifted to all `L²` by a `|t|`-Lipschitz
characteristic-function bound (`Real.norm_exp_I_mul_ofReal_sub_one_le` + an
`L¹ ≤ L²` estimate on the probability space) feeding `DenseRange.induction_on`,
then `Measure.ext_of_charFun`. Its consumer
`MathFin/FixedIncome/VasicekSDEGaussian.lean` (`vasicekShortRate_hasLaw_gaussian`)
makes the Vasicek SDE terminal law a *theorem*:
`r_T = mean + σ ∫₀ᵀ e^{−κ(T−s)} dB_s ~ N(vasicekSDEMean, σ²(1−e^{−2κT})/(2κ))` —
variance pinned by the FTC integral `∫₀ᵀ e^{−2κ(T−s)} ds` (`vasicekKernel_integral_sq`,
antiderivative `e^{−2κ(T−s)}/(2κ)`), affine transport via
`gaussianReal_const_mul`/`gaussianReal_const_add`. Retires `VasicekSDE.lean`'s
"stated, not derived". Corpus entries `sc-wiener-integral-gaussian`,
`mf-vasicek-sde-terminal-gaussian` (both `full`); corpus 292 → 294, 257 → 259 full.
lake build 8821 jobs (0 errors, 0 sorries; only Degenne-package `sorry` + benign
unused-section-variable warnings); ledger 294/294 fresh; AxiomAudit +
AxiomAuditGen pin both headlines at `[propext, Classical.choice, Quot.sound]`.

Review panel (focused, the 8 lenses + a dedicated mathematical-honesty pass):
**PASS, no blocking findings.** Honesty pass confirmed: the FTC integral is the
claimed value; `κ > 0` (and the weaker `0 ≤ κ` / `κ ≠ 0` in the helpers) are
genuinely necessary, not vacuous; the charFun density argument is gap-free (no
`convert`/`simp` papering over a step); the scope claim (deterministic integrand)
matches what the theorem delivers. Coherence: consumes the upstream Gaussian /
charFun / affine-map API throughout, reproving nothing. The review's one
non-blocking note — a private `lpTwoNormSq` helper duplicating the (private)
`Lp_real_two_norm_sq` in `WienerIntegralL2.lean` — was **resolved**: the
foundational lemma was de-privatised and is now consumed directly, with the
duplicate deleted (no copy). Honest scope: the *deterministic*-integrand case;
the genuinely-random-integrand localized Itô formula remains the open frontier.

## 2026-06-27 — commit 913f969 — corpus 292 — the [0,∞) unbounded-horizon Itô integral as a continuous local martingale

The `[0,∞)` crown of the continuous-time Itô tower. New files
`MathFin/Foundations/ItoIntegralProcessL2Infinite.lean` (the `L²` process
`itoProcessL2Inf`, the `SimpleProcess` clamp `clampSP` + horizon consistency
`itoProcessL2Inf_eq_itoProcessCLM`) and
`MathFin/Foundations/ItoIntegralProcessLocalMartingaleInfinite.lean` (the per-horizon
gluing + the headline `exists_continuous_localMartingale_modification_infinite`); the
`[0,T]` follow-on (`…LocalMartingaleGeneral.lean`) strengthened to also expose per-horizon
`StronglyMeasurable[augFiltration]`. Corpus entry `sc-ito-infinite-local-martingale`
(`full`); `sc-ito-general-local-martingale` updated to the strengthened conclusion. lake
build 8819 jobs (0 warnings, 0 sorries); ledger 292/292 fresh; AxiomAudit pins the headline
at `[propext, Classical.choice, Quot.sound]`.

Three-agent panel (lenses split 1·2·8 / 3·6·7 / 4·5):

| lens | verdict |
|------|---------|
| inspired math quality | PASS |
| Mathlib / BrownianMotion coherence | PASS |
| zero slop | PASS |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS (one note, fixed in this commit) |
| beautiful, elegant math | PASS |

**Blocking findings**: none.

**Checks that mattered**: the result is *not* a degenerate witness —
`itoProcessL2Inf t f = E[∫₀^∞ f dB | 𝓕_t]` is a genuine CLM composition and its martingale
property is the honest conditional-expectation tower (not assumed); the glued process is
`0` only off a co-null set (an honest a.e.-modification, not a cheat trivializing
continuity/martingale); the three conclusions (modification at *every* `t`,
everywhere-continuous on all of `ℝ≥0`, real `IsLocalMartingale`) are each derived, none
degenerate; no hidden hypotheses beyond `IsPreBrownianReal` + measurability + pathwise
continuity of `B`. The `clampSP` `SimpleProcess` truncation genuinely preserves
`𝓕(left-endpoint)`-measurability (drop intervals starting past `T`, clamp surviving right
endpoints — *not* both, which would break it); `clampSP_value_sum` factors the three
agreement statistics into one principled identity rather than triplicated case-work. The
key architectural win — horizon-independent integrand ⇒ *global* martingale ⇒ no clamp in
step 4 (vs. the `min·T` clamp of the `[0,T]` follow-on) — is real and load-bearing. No
reproving of Mathlib/Degenne lemmas; `monoMeasureLp` is a clean upstream candidate (Mathlib
has `MemLp.mono_measure`, no packaged CLM), not wrapper-slop.

**Recorded actions**:
1. *(done in this commit)* the `[0,T]` theorem docstring now enumerates the new 4th
   conjunct `(iv) StronglyMeasurable[augFiltration i]` (panel concept-clarity note).
2. *(nit, accepted)* `isCadlag_of_continuous` is re-derived in the `[0,∞)` file because the
   `[0,T]` copy is `private`; a shared public helper is a fold-in for the next touch.
3. *(nit, open)* `monoMeasureLp` is a genuine Mathlib-upstream candidate; route it through
   the BM-upstream triage when that window opens.

## 2026-06-26 (IV) — the general-integrand Itô process as a continuous local martingale (the IsLocalMartingale follow-on) — corpus 291

New file `MathFin/Foundations/ItoIntegralProcessLocalMartingaleGeneral.lean`
(augmentation core + the assembly) + corpus entry `sc-ito-general-local-martingale`
(`full`). Upgrades the gate (III) to Degenne's local-martingale interface:
`exists_continuous_localMartingale_modification` — an everywhere-continuous process
`X` that is a modification of `itoProcessCLM T t φ` for `t ≤ T`, has continuous paths
for **every** `ω`, and is a genuine `IsLocalMartingale` for the **null-augmented**
Brownian filtration `𝓕ᴮ ⊔ 𝓝`. Degenne's `Martingale.IsLocalMartingale` needs paths
càdlàg for every `ω`, forcing the everywhere-continuous representative; on a null set it
can only be repaired while staying adapted if the filtration carries the null sets —
hence the augmentation, whose cond-expectation invariance (`condExp_sup_nulls`) transfers
the L² martingale property to the repaired process.

**Panel**: three independent agents — (math correctness + first principles
[adversarial]), (Mathlib/Degenne coherence + zero slop + idiomatic register),
(skeptic: honest scope + concept clarity + no-overclaim).

| lens | verdict |
|---|---|
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS (blocking finding fixed in this commit) |
| zero slop | PASS |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS (notes fixed in this commit) |
| beautiful, elegant math | PASS |

**Blocking findings**: one, **fixed in this commit**. The coherence reviewer caught that
`exists_ae_eq_of_sup_nulls` hand-rolled a `MeasurableSpace M` (sets `=ᵐ` an `m₁`-set) that
**is** Mathlib's `eventuallyMeasurableSpace m₁ (ae μ)` — an anti-wrapper reproof of a named
Mathlib construction. Rewritten to consume `eventuallyMeasurableSpace` +
`le_eventuallyMeasurableSpace` directly (the theorem statement, genuinely new, is unchanged);
`condExp_sup_nulls` and the null-augmented filtration were confirmed genuinely absent upstream
(no Mathlib/Degenne "completed filtration" constructor; BM has only the `IsComplete` predicate).

**Notes addressed** (non-blocking, fixed): the "usual conditions" phrasing overclaimed (the
construction adds the **completeness** half only — null sets — not right-continuity); reworded
across the module/`nullsAlg`/`augFiltration` docstrings + the two benchmark scopes. The theorem
docstring mis-cited `condExp_sup_nulls` for *adaptedness* (adaptedness comes from `G ∈ 𝓝`;
`condExp_sup_nulls` transfers the *martingale* property) — corrected, and the "[0,T]" framing
clarified (the martingale property holds **globally** on `ℝ≥0` via the `min · T` freeze; only
the modification clause is horizon-scoped). Scope "impossible" → "not achievable"; "consumes" →
"is built to consume".

**Checks that mattered**:
- **No mathematical hole** (full adversarial trace of all five concerns). The two cruxes
  (`exists_ae_eq_of_sup_nulls`, `condExp_sup_nulls`) are true and correctly proven; the
  `by_cases i ≤ T` martingale-identity transfer at clamped indices `min i T ≤ min j T` is valid
  in both branches (L² identity for `i ≤ T`; cond-exp of an already-`𝓕_i`-measurable terminal
  value for `T < i`); the `min · T` clamp genuinely yields a **global** martingale without
  needing values past `T` (the standard "freeze a `[0,T]` martingale" device, not degenerate).
- **The `IsLocalMartingale` is genuine, not vacuous**: it is obtained by first proving the
  strictly stronger `Martingale` (everywhere-continuous, frozen past `T`) and downgrading via
  `Martingale.IsLocalMartingale` (Degenne's `Locally.of_prop` with the constant `τ ≡ ⊤`). The
  result therefore *under*-claims relative to what is proved.
- **The null augmentation earns its keep** exactly at adaptedness: the good set `G = Nᶜ` is
  co-null but **not** `natFiltration`-measurable, so `𝓝` is what keeps the everywhere-continuous
  representative adapted (`stronglyMeasurable_of_tendsto` on the pointwise limit of
  `G.indicator`(simple integrals), each `natFiltration`-measurable, `G ∈ 𝓝`).
- **Axioms-clean** `[propext, Classical.choice, Quot.sound]` (AxiomAudit pin); `lake build`
  green (8817 jobs); ledger 291/291 fresh; pytest 19/19.

## 2026-06-26 (III) — continuous modification of the general-integrand Itô process (the gate) — corpus 290

New file `MathFin/Foundations/ItoIntegralProcessContinuousModification.lean`
(13 declarations) + corpus entry `sc-ito-general-continuous-modification`
(`full`). The first pathwise-regularity result for the **general** integrand:
`exists_continuous_modification_itoProcess` — the L²-valued process
`itoProcessCLM T t φ` has a pathwise-continuous modification on `[0,T]`
(modification a.e. at every `t ≤ T` + a.s. continuous paths). The
tower→pricing gate.

**Panel**: three independent agents — (coherence + idiomatic + slop),
(soundness [adversarial] + ingenuity + first principles), (skeptic: integrity
+ honesty + concept clarity).

| lens | verdict |
|---|---|
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS |
| zero slop | PASS |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS (blocking finding fixed in this commit) |
| beautiful, elegant math | PASS |

**Blocking findings**: one, **fixed in this commit**. All three reviewers
independently flagged the **module docstring** (`:16-17`, `:27-28`) stating the
modification is "packaged as a continuous (hence local) martingale" and "is a
continuous L² martingale — hence an `IsLocalMartingale`" — content the file does
**not** prove (it delivers only the modification + pathwise continuity). The
gating benchmark `formalization_scope` was already honest (defers
`IsLocalMartingale`); only the in-file prose overstated. Reworded to describe the
continuous modification as the *input* the localized calculus will consume, with
the `IsLocalMartingale` packaging an explicit follow-on (it needs paths càdlàg for
every `ω`, hence an augmented filtration / "usual conditions" that `natFiltration`
does not carry — B3 sidesteps this only because the *simple* process is continuous
and adapted for every `ω`).

**Checks that mattered**:
- **No mathematical hole** (full adversarial trace). The constants are exact:
  per-term tail `μ(Aₙ) ≤ εₙ⁻¹·2·2⁻ⁿ = 2·(2/3)ⁿ` (summable), uniform tail
  `dist (fₙ) X ≤ (3/4)ⁿ/(1−3/4) = 4·(3/4)ⁿ` (the `dist_le_of_le_geometric_of_tendsto₀`
  output, no off-by-one). The **two-rate coupling** is the crux and is valid:
  Borel–Cantelli needs `Σ εₙ⁻¹·2⁻ⁿ < ∞`, uniform-Cauchy needs `Σ εₙ < ∞`; with
  `εₙ = (3/4)ⁿ ∈ (½,1)ⁿ` both converge. Index shifts (`summable_nat_add_iff N`,
  `tendsto_add_atTop_nat n`, `hN (k+n)` justified by `N≤n≤k+n`) carry no off-by-one.
- **Coherence**: nothing upstream reproved. Degenne's `maximal_ineq_norm` is
  applied **directly in continuous time** (right-continuity from B3) — better than
  the spec's planned continuous-sup→countable-sup reduction. Non-redundant *and
  stronger*: Degenne's general càdlàg modification (`exists_modification_isCadlag`)
  is `sorry`-backed; the L²+Doob route yields a genuinely **continuous** version.
- **Integrity**: `sorry`-free, axiom-clean. `AxiomAudit.lean` pins
  `itoContinuousMod_modification` / `_continuousOn` / `exists_continuous_modification_itoProcess`
  to exactly `[propext, Classical.choice, Quot.sound]`; the whole 13-lemma chain feeds
  the capstone, so the clean print certifies the chain (including the consumed
  `maximal_ineq_norm`). The `full` claim is honest: the headline is the genuine
  "continuous modification exists" statement (both clauses about the same `X`,
  non-vacuous comparison target), faithfully 1:1 re-exported; the benchmark scope
  correctly discloses the `[0,T]` horizon and defers `[0,∞)` / localized-Itô /
  `IsLocalMartingale`.
- **Elegance win (recorded)**: the implementation uses weak-(1,1) + `L¹ ≤ L²` (one
  monotonicity step, never squares the L² norm) where the spec proposed weak-(2,2)
  with `εₙ = 2^{-n/2}`. Cleaner first-principles math; keep it.

**Recorded actions**:
1. *(done this commit)* docstring honesty fix — the blocking finding above.
2. *(done this commit)* idiom: `field_simp` → explicit `inv_mul_cancel₀ hε.ne'`
   for `ε⁻¹·(ε·x) = x`; `nlinarith [pow_nonneg …]` → `linarith [pow_nonneg …]` (the
   goal `a + a·2⁻¹ ≤ 2a` is linear in the atom `a = (2⁻¹)ⁿ`).
3. *(done this commit)* `omit hB in` on the `itoContinuousMod` def, making its
   non-dependence on the pre-Brownian property explicit (matches the file's `omit`
   discipline; `include` did not force `hB` into the def, but the marker is honest).
4. *(nit, open)* minor duplication: the `Iic T = Icc 0 T` conversion (×2) and the
   `(V−W).val = V.val − W.val := rfl` + `itoSimpleProcess_sub` point-linearity
   (×2). Fold into helpers on next touch; consider relocating `itoSimpleProcess_sub`
   beside `_add`/`_neg` in the B1a module for reuse.
5. *(deferred, scoped)* the `IsLocalMartingale` framing needs augmented-filtration
   ("usual conditions") infrastructure that `natFiltration` lacks — a separate
   deliverable, honestly disclosed in the benchmark scope and the module docstring.

## 2026-06-26 (II) — d-asset one-period FTAP: reduced_core → FULL — corpus 289

**Scope**: dropping the non-redundancy hypothesis from the **d-asset** one-period FTAP, this
session. `Foundations/FTAPOnePeriodVector.lean` was generalised from
`Y : Ω → EuclideanSpace ℝ (Fin d)` to a discounted return valued in any **finite-dimensional**
real inner-product space `F` (the `ℝᵈ` market is the instance `F = EuclideanSpace ℝ (Fin d)`),
and the coercivity/minimiser machinery was rebuilt around the **gains kernel**
`N = gainsKernel = {θ : ⟪θ,Y⟫ = 0 a.e.}`: the softplus potential is constant along `N` and
coercive on `Nᗮ`, so it is minimised over `Nᗮ` and — being `N`-translation-invariant — a
minimiser there is **automatically global** over all of `F`. This discharges the old `hndg`
assumption entirely; the first-order-condition lemma and the whole Esscher/`withDensity` EMM
block are reused verbatim. The corpus entry `mf-ftap-one-period-vector` is now **`full`**
(254 full + 18 wrappers = 272/289 delivery-ready, 17 reduced cores). Library green
(`lake build` 8814 jobs), axioms-clean (`[propext, Classical.choice, Quot.sound]`), ledger
289/289 fresh, pytest 19/19, zero warnings/sorries.

| lens | verdict |
| --- | --- |
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS |
| zero slop | PASS |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS (after fix) |
| beautiful, elegant math | PASS |

**Panel**: three independent review agents, lenses grouped (1+4+5+8 / 2+3+6 / clarity+faithfulness),
reading the module, the corpus entry, and `coverage.md` read-only against the pinned Mathlib (no Lean
run — the daemon held the local Lean slot). Initial outcome **2 PASS + 1 BLOCK**.

**Honesty — the "full" claim, verified clean**: the headline `ftap_one_period_vector` carries
**only** `Measurable Y` — no integrability, no boundedness, no non-redundancy. `NoArbitrage` is the
genuine textbook NA; `IsEMM` carries true equivalence (`Q ≪ P` **and** `P ≪ Q`), `Integrable Y Q`,
and `∫ Y ∂Q = 0`. The redundant-everything case (`Nᗮ = ⊥ ⟺ Y =ᵐ 0`) is handled explicitly
(`Q = P`); redundant directions are absorbed by the `Nᗮ`-minimisation + `N ⊔ Nᗮ = ⊤` decomposition,
with `N ⊓ Nᗮ = ⊥` (via `inner_right_of_mem_orthogonal`) keeping the `Nᗮ`-coercivity honest.
`FiniteDimensional F` is the d-asset model itself (Föllmer–Schied 1.6), not a narrowing. The panel
confirmed no hidden hypothesis sneaks the restriction back in.

**Coherence / ingenuity**: no reproved lemma — the orthogonal-complement API (`isCompl_orthogonal`,
`sup_orthogonal_of_hasOrthogonalProjection`, `inner_right_of_mem_orthogonal`,
`closed_of_finiteDimensional`, `orthogonal_orthogonal`, `bot_orthogonal_eq_top`), extreme-value,
Fermat, and differentiation-under-the-integral are all consumed upstream. Generalising to abstract
`F` is the **minimal-interface** move (the proof uses only the inner product + finite-dimensionality,
never a coordinate basis), making `ℝᵈ` and even the scalar `ℝ` free instances; the verbatim reuse of
the FOC + `withDensity` block is good factoring.

**Blocking finding (remediated before this verdict)**: the corpus entry's **metadata** prose (`name`
"…Non-Redundant", `description`, and especially `formalization_scope` "…NARROWER… assumes the market
is NON-REDUNDANT… the redundant-asset generalisation… remain out of scope") still described the
pre-upgrade reduced core, flatly contradicting the `full` status flipped one field above — a
restriction-in-disguise surfaced in metadata, exactly what the values gate exists to catch. Plus
`coverage.md` listed the now-closed d-asset case as an open follow-on. All synced to the full theorem.

**Recorded actions**:
1. *(done this verdict)* Corpus `name` / `description` / `formalization_scope` for
   `mf-ftap-one-period-vector` rewritten to the full statement; `coverage.md` live-status +
   open-follow-ons line corrected (only the general-Ω multi-period DMW remains open).
2. *(done this verdict)* `set F`/`F'` in `hasDerivAt_potential_dir` renamed to `Φ`/`Φ'` (they
   shadowed the market type `F`); two unused `set N := … with hN` binders dropped; the scalar sibling
   `FTAPOnePeriod.lean`'s `## Scope` (which still called the d-asset case open) repointed at the
   now-complete `ftap_one_period_vector`.
3. *(done — follow-up commit)* The `isEquivProbMeasure_withDensity` cross-file dedup is landed: new
   shared module `Foundations/EquivMeasure.lean` (a measurable, strictly-positive, normalised density
   → equivalent probability measure: `IsProbabilityMeasure` ∧ `Q ≪ P` ∧ `P ≪ Q`), consumed at all
   **four** sites (the two `FTAPOnePeriodVector` densities + the two scalar `FTAPOnePeriod` densities),
   each `obtain ⟨…⟩ := isEquivProbMeasure_withDensity P … ; rw [← h…def] at …`. Term-preserving
   extraction, net −~40 lines of duplicated ritual; the helper bundles four Mathlib lemmas consumed
   four times (a real abstraction, not a thin wrapper — zero-slop / coherence). lake build 8815 jobs,
   ledger 289/289 fresh, pytest 19/19, axiom-clean.
4. *(noted, kept)* "Esscher" stays the project's chosen label for the softplus/logistic construction
   (the density is the bounded logistic `σ`, not the raw exponential tilt); the body shows `σ`
   explicitly, so no reader is misled.

**The actual crown still open**: the general-Ω **multi-period** DMW (L⁰-cone closedness + measurable
selection), unchanged by this rung.

## 2026-06-26 — commit bc9a258 — corpus 289

**Scope**: the **d-asset** one-period FTAP (Föllmer–Schied Thm 1.6, non-redundant
markets), this session. New proof content: `Foundations/FTAPOnePeriodVector.lean`
(~580 lines) — the vector model (`NoArbitrage`, `IsEMM` over `EuclideanSpace ℝ (Fin d)`),
the forward direction, the **softplus potential** `f(θ)=∫ log(1+exp⟪θ,Y⟫)` with its
logistic derivative, differentiation under the integral (`hasDerivAt_potential_dir`),
coercivity (`exists_pos_lower_bound`), the global minimiser (`exists_global_min_potential`),
the first-order condition (`integral_logistic_smul_eq_zero`), the integrable Esscher-EMM
core, the bounded-density reduction, and the biconditional `ftap_one_period_vector`; one
`reduced_core` corpus entry (`mf-ftap-one-period-vector`). Library green (`lake build`
8814 jobs), axioms-clean (`[propext, Classical.choice, Quot.sound]`), ledger 289/289 fresh,
pytest 19/19.

| lens | verdict |
| --- | --- |
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS |
| zero slop | PASS |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS |
| beautiful, elegant math | PASS |

**Panel**: three independent review agents, lenses grouped (1+2+8 / 3+4+5 / 6+7), reading
`FTAPOnePeriodVector.lean` read-only against the pinned Mathlib (no Lean run — the daemon
held the local Lean slot).

**Honesty — the headline checks, verified clean**: the backward direction **constructs**
the EMM, never posits it. The Esscher density `z = σ⟪θ₀,Y⟫` is the first-order condition of
a genuine optimisation: the softplus potential is convex and finite on all of `ℝᵈ` (the
`log(1+exp)` tempering avoids the exponential-moment restriction of the classical Esscher
tilt while keeping `σ ∈ (0,1)` for a uniform `L¹` domination), coercivity comes from the
**attained** unit-sphere minimum of `g(θ)=∫⟪θ,Y⟫⁺` (genuinely needing both no-arbitrage —
applied to `−θ` — and non-redundancy), the minimiser exists by compactness, and its FOC
`∫ Y·σ⟪θ₀,Y⟫ = 0` is real differentiation under the integral
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le` + `IsLocalMin.hasDerivAt_eq_zero`,
scalarised per direction then assembled via `inner_self_eq_zero` — strictly less machinery
than a Fréchet-derivative route). Nothing is a definitional `rfl`. Non-redundancy enters
**only** the coercivity step (one `apply hndg`), is honestly the `reduced_core` narrowing,
and is named in the module `## Scope`, the theorem docstring, and the corpus scope.

**Coherence / ingenuity checks**: no reproved lemma — parametric differentiation, Fermat,
extreme-value, Lipschitz, inner/integral, and `withDensity` APIs are all consumed upstream.
`lipschitzWith_integral_inner` is a clean reusable abstraction ("averaging a 1-Lipschitz
function of `⟪θ,Y⟫` is `(∫‖Y‖)`-Lipschitz"), consumed for both the potential and the
positive-gain average so continuity falls out of Lipschitz for free. The integrable-core →
reduction → biconditional layering and the single `d = 0` empty-market split (at the first
point `Nonempty (Fin d)` is needed) are the right shape.

**Blocking findings**: none.

**Recorded actions**:
1. *(done this verdict)* Module `## Scope` now lists **non-redundant** among the
   restrictions and the **redundant** one-period d-asset case (quotient by the gains kernel)
   among the open follow-ups — the panel's one substantive clarity gap (the narrowing was
   stated everywhere except its dedicated Scope block).
2. *(done this verdict)* Intro wording sharpened: `z = σ⟪θ₀,Y⟫` is the unnormalised **weight**;
   its normalisation `z/E[z]` is the EMM density.
3. *(done this verdict)* Dead `with hz` binder dropped (the unused-variable linter does not
   flag `set … with`).
4. *(considered, deferred)* The "equivalent probability measure from a strictly-positive
   normalised density" block (`IsProbabilityMeasure` + `Q≪P` + `P≪Q` via `withDensity`)
   recurs ~3× across this file and the scalar `FTAPOnePeriod.lean`. Both panellists flagged a
   shared `isEquivProbMeasure_withDensity` helper. It is a **cross-file** dedup of ritual (the
   densities — logistic Esscher vs `(1+‖Y‖)⁻¹` tempering — differ), judged a non-blocking
   cleanup-pass opportunity; deferred to a dedicated cross-file pass so the two FTAP files
   move together.
5. *(noted, kept)* Three `classical` (lines 278/393/471) read defensively; standard idiom,
   removability unconfirmed without a compile. Kept.

## 2026-06-25 — commit a5197ee — corpus 288

**Scope**: the general-Ω one-period Fundamental Theorem of Asset Pricing
(Föllmer–Schied Thm 1.55 / one-period Dalang–Morton–Willinger), shipped this session.
New proof content: `Foundations/FTAPOnePeriod.lean` — the scalar L⁰ model
(`NoArbitrage`, `IsEMM` with mutual absolute continuity), the forward direction
`noArbitrage_of_isEMM`, the balancing-density core `exists_isEMM_of_pos_tails`
(EMM `Q = P.withDensity (λ·𝟙_{Y≥0} + μ·𝟙_{Y<0})`, weights solved so `Y` is fair), the
scalar no-arbitrage dichotomy + integrable backward `exists_isEMM_of_noArbitrage_integrable`,
the integrability-dropping reduction `exists_isEMM_of_noArbitrage` (equivalent
`P̃ = P.withDensity (1+|Y|)⁻¹/κ`), and the biconditional
`ftap_one_period : NoArbitrage ↔ ∃ EMM`; one `full` corpus entry
(`mf-ftap-one-period-general`). Library green (`lake build` 8813 jobs), axioms-clean
(`[propext, Classical.choice, Quot.sound]`), ledger 288/288 fresh, pytest 19/19.

| lens | verdict |
| --- | --- |
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS |
| zero slop | PASS |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS |
| beautiful, elegant math | PASS |

**Panel**: three independent review agents, lenses grouped (1+2+8 / 3+4+5 / 6+7),
reading `FTAPOnePeriod.lean` read-only against the pinned Mathlib (no Lean run — the
daemon held the local Lean slot).

**Honesty — the headline checks, verified clean**: the backward direction genuinely
**constructs** the EMM, never posits it. `exists_isEMM_of_pos_tails` builds
`Q = P.withDensity (ofReal Z)` with `Z = λ·𝟙_{Y≥0} + μ·𝟙_{Y<0}`, the weights **solved**
from the fairness + normalisation 2×2 system (`D = −c·P(s) + a·P(sᶜ)`, `λ = −c/D`,
`μ = a/D`), with `D > 0` proved by a genuine case-split on `P(s)=0`; `∫Z=1` and `∫Z·Y=0`
are then *derived* (`field_simp; ring` bottoming out in the chosen weights, not a
definitional `rfl` — the `test_values.py` rfl-tripwire does not fire). The scalar
dichotomy (`θ=±1` annihilates a one-signed `Y`) upgrades the weak tail inequalities to
strict via `integral_eq_zero_iff_of_nonneg_ae` on the restricted measure — real
measure-theoretic work. Mutual absolute continuity `Q ~ P` is established from the
strictly-positive density on **both** sides (`withDensity_absolutelyContinuous` / `…'`),
never assumed. Scope honest in module docstring + corpus `formalization_scope` +
`coverage.md`: one period, one scalar asset, arbitrary Ω; the general-Ω **multi-period**
DMW (measurable selection) and the d-asset case named as open.

**Coherence / ingenuity checks**: library consumption is clean — no reproved lemma. The
one bespoke helper `hsplit` (`∫ Z·g = λ·∫_s g + μ·∫_sᶜ g`) is the problem-specific
two-region decomposition over `integral_add_compl`, not a re-derivation of additivity.
The elementary Föllmer–Schied route (bounded-density reduction + scalar dichotomy +
balancing `withDensity`) is the inspired choice: it avoids Hahn–Banach / Kreps–Yan
precisely because the one-period scalar case makes the EMM *explicit* — the verified
contrast with the finite-Ω sibling `ftap_discrete`, which *does* route through
`exists_pos_dual_of_disjoint_stdSimplex`. The 5-theorem decomposition cuts at the right
joints: `exists_isEMM_of_pos_tails` is a reusable quantitative core knowing nothing of
no-arbitrage; integrability is dropped in a separate, conceptually-orthogonal reduction
rather than inlined.

**Blocking findings**: none.

**Recorded actions**:
1. *(done this verdict)* Dead `with hsdef` binders removed from both
   `exists_isEMM_of_pos_tails` and `exists_isEMM_of_noArbitrage_integrable`
   (`set s := … with hsdef` where `hsdef` was never referenced — a dead hypothesis, the
   panel's one concrete slop flag).
2. *(done this verdict)* Down-weight renamed `m → μ` (`lam`/`mu` for `λ`/`μ`) so the
   up/down symmetry the docstrings describe is literal in the source — flagged by two
   panellists (idiomatic register + elegant math).
3. *(considered, kept)* The two sign-asymmetric contrapositive tail blocks (`{Y≥0}`
   direct, `{Y<0}` via `−Y`) and the ~6-line `withDensity`-⇒-equivalent-probability
   boilerplate shared by the two existence theorems. Both panellists judged a `wlog` /
   shared `equivProbOfDensity` abstraction below the threshold where factoring pays (the
   sign-flip is genuine math; the boilerplate is over two differently-named densities at
   the only two sites). Kept; revisit if a third site appears.
4. *(nit, kept)* `exists_isEMM_of_noArbitrage`'s docstring states `κ = ∫ w ∈ (0,1]` while
   the proof establishes/uses only `0 < κ` (upper bound true but unused). Kept as honest
   exposition of the object — proving an unused `κ ≤ 1` would itself be slop.

## 2026-06-25 — commit 74e94b6 — corpus 287

**Scope**: the finite-Ω Fundamental Theorem of Asset Pricing (Harrison–Pliska /
finite Dalang–Morton–Willinger), shipped this session to public `main`. New proof
content: `Foundations/ConvexSeparation.lean` (the separating-dual kernel
`exists_pos_dual_of_disjoint_stdSimplex`); `Foundations/FTAPMultiState.lean`
backward direction + biconditional `hasEMM_multi_iff_not_hasArbitrage`;
`Foundations/FTAPDiscrete.lean` (the multi-period model `NoArbitrage`/`IsEMM`, both
directions, `ftap_discrete : NoArbitrage ↔ ∃ EMM`); two `full` corpus entries
(`mf-ftap-discrete-complete`, `mf-ftap-single-period-complete`). Also a build-env fix
(`7b15319`, warm REPL daemon on v4.31 — infra, not proof content). Library green,
axioms-clean, ledger 287/287 fresh, pytest 19/19.

| lens | verdict |
| --- | --- |
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS-WITH-NOTES |
| zero slop | PASS-WITH-NOTES |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS-WITH-NOTES |
| beautiful, elegant math | PASS-WITH-NOTES |

**Panel**: four independent review agents, lenses paired (3+6 / 2+4 / 5+7 / 1+8),
reading the new files read-only (no Lean run — the daemon held the local Lean slot).

**Honesty — the headline checks, verified clean**: the backward direction genuinely
**constructs** the EMM from no-arbitrage (gains subspace disjoint from the simplex →
`geometric_hahn_banach_compact_closed` → strictly-positive dual → `PMF` measure → the
one-step martingale property via `ae_eq_condExp_of_forall_setIntegral_eq`) — `Q` is
built, never posited. `IsEMM.mart`'s one-step-up-to-`T` form is the **faithful**
finite-horizon object (`S` genuinely need not be a `Q`-martingale past `T`); it is
proved via the textbook set-integral condExp characterisation and consumed
substantively by the forward telescoping, so the biconditional is non-trivial both
ways. The full-support hypothesis `∀ ω, 0 < P {ω}` is standard finite-state hygiene
(makes `~P` ≡ full support and `ᵐ[P]` ≡ pointwise), not a trivialiser, and is not
droppable without a messier theorem. Scope stated honestly in three places (module
docstrings, corpus `formalization_scope`, `coverage.md`) — "finite case of DMW"; the
general-Ω multi-period crown (L⁰-closedness + measurable selection) is named as open.

**Coherence / ingenuity checks**: `martingaleTransform_add`/`_smul` are genuinely new
(Mathlib has only `martingalePart` linearity for the Doob decomposition — a different
object; no `martingaleTransform` upstream). The separating-dual kernel is consumed by
**both** the single-period multi-state and the multi-period scalar backward
directions — genuine reuse at the right altitude. The forward-direction overlap with
`FTAP.emm_implies_no_arbitrage` is **not** a missed factoring: the honest
finite-horizon one-step `IsEMM` is strictly weaker than the all-time `Martingale` the
abstract forward (and `martingaleTransform_isMartingale`) require, so no shared core
is extractable without weakening the theorem — the hand telescoping is forced and
correct. The global-separation architecture is decisively the elegant route for
finite Ω (vs per-atom backward induction + gluing).

**Blocking findings**: none.

**Recorded actions**:
1. *(done this verdict)* Stale public-doc claims corrected — all three **under**-stated
   the work after this session: `README.md` (FTAP line said "multi-state forward" →
   now multi-state biconditional + multi-period finite-Ω biconditional),
   `FTAPMultiState.lean` module header (said "forward direction / backward not attempted
   here" → "both directions"), `FTAPTwoState.lean` cross-ref (mis-cited
   `NoArbitrageDerivations` for the general forward → `FTAPMultiState`).
2. *(done this verdict)* The "full-support ⇒ null set empty" reasoning, written twice in
   `FTAPDiscrete.lean` (`gains_disjoint_stdSimplex` + `exists_isEMM_of_noArbitrage`),
   extracted to one `private lemma eq_empty_of_pos_singleton` consumed at both sites.
3. *(considered, kept)* `FTAPDiscrete.lean`'s file-wide
   `set_option linter.unusedSectionVars false` (the repo's only such suppression; house
   style is `omit … in`). Switching needs **five** `omit` clauses — the two algebraic
   lemmas, the span-induction, and `gains_disjoint`/`noArbitrage_of_isEMM` all use
   heterogeneous subsets of the rich shared `variable` context — noisier than one
   suppression. Kept with an explanatory comment; revisit if the file is split.
4. *(nit, open)* `ConvexSeparation.lean:84–101` hand-rolls "a linear functional equals
   the coordinate-sum of its standard-basis values" + a sign-flip `calc`; correct but
   ~12 lines more verbose than a `Pi.basisFun`/`Finset.sum_pi_single` collapse. Sharpen
   on next touch of the file.

## 2026-06-24 — commit 4e921c4 — corpus 285

**Scope**: the v4.31 toolchain bump + full-library port (branch
`bump-bm-mathlib-4.31`: ~36 MathFin files across the BrownianMotion `d6f23da`
+ Mathlib `v4.31.0` + toolchain `v4.31.0` co-bump) and the lint-cleanup commit
`4e921c4`. Mechanical drift-fixing — no new theorems, no benchmark entries added
(corpus unchanged at 285). Library green (8810 jobs), axiom-clean.

| lens | verdict |
| --- | --- |
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS |
| zero slop | PASS |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS |
| beautiful, elegant math | PASS-WITH-NOTES |

**Panel**: three independent review agents, lenses split (2+3 / 4+5+6 / 1+7+8),
reading `git diff origin/main...HEAD -- MathFin/` read-only (no Lean run — the
ledger build held the one local Lean slot).

**Statement integrity (the port's #1 risk) — verified clean**: every changed
`theorem`/`lemma`/`def` signature is exactly one of (a) `IsPreBrownian` →
`IsPreBrownianReal` rename, (b) instance binder `[hB]` → explicit `(hB)` +
`include`/`omit hB in` (same hypothesis, v4.31-mandated since it is now a `Prop`),
or (c) a definitionally-equal reformulation (`max (t-s)(s-t)` ↔ `nndist ↑t ↑s`,
`B t - B s` ↔ `fun ω => B t ω - B s ω`). No hypothesis dropped, no conclusion
weakened, no measure/variance changed to a non-equal value. Deprecations migrated
1:1 to the non-deprecated upstream lemma (`measure_sdiff`, `FunLike.coe_*`,
`apply_sup'_eq_sup'_comp`, `zero_le`, unqualified CLM `*_apply`) — consumed, not
wrapped. The cleanup removed only provably-dead tactic arms + a no-op `change` +
unused simp args; no live step lost. Docstrings updated in lockstep (incl. the
`@[blueprint]` spine); exhaustive grep found zero surviving `IsPreBrownian` or
deprecated-name references in changed files.

**Blocking findings**: none.

**Benchmark corpus**: the ledger sweep surfaced that the port had been
library-only — 20 benchmark snippets (the inline re-exports in `benchmarks/*.json`)
still used the v4.30 API. All 20 were ported: explicit `(hB : IsPreBrownianReal …)`
threading with `hB` as the re-exported lemma's first argument, and the BM-API
renames (`IsPreBrownian.isMartingale`→`IsPreBrownianReal.isMartingale`,
`memHolder_mk`/`mk` now on `IsPreBrownianReal`). `bm-prop-5.1.2` was the one that
looked like a removed constructor (`IsGaussianProcess.isPreBrownian_of_covariance`)
but is in fact *absorbed into Mathlib* as `IsGaussianProcess.isPreBrownianReal_of_covariance`
(`Mathlib.Probability.BrownianMotion.Basic`) — same min-covariance characterization,
so it stays a faithful one-line library_wrapper. All **285** ledger entries now
re-verify fresh under the v4.31 pins (`lake env lean` per snippet); pytest 19/19.

**Recorded actions (non-blocking, next-session tidy)**:
1. *(nit)* `Foundations/ItoIntegralBrownian.lean:251` — `riemannFn` `def` sits under
   an active `include hB` with no `omit hB in`, so it carries a vacuous `hB` argument
   (harmless; build green). Inconsistent with the file's own `omit hB in` discipline;
   one-line fix deferred (it touches `riemannFn`'s callers, so out of scope for a
   mid-finalize edit on the memory-constrained box).
2. *(minor)* `BlackScholes/StrikeGreeks.lean:136/141` — `hasDerivAt_bsV_K` declares
   two side conditions for `K·σ·√τ` (`≠ 0` and `0 <`); `field_simp` may not need both.
   No unused-variable warning fired (both are referenced), so it is at most a
   functional redundancy — confirm with a build which (if either) is droppable.
3. *(nit)* the `nndist ↑t ↑s = (t-s)` bridge is hand-inlined ~7× (QuadraticVariationL2,
   BrownianMartingale, ItoFormulaRemainder, WienerIntegral); orientations differ per
   site, but a shared helper would DRY it.
4. *(nit)* the `convert … <;> try rfl` / `<;> first | rfl | ring` module-instance-diamond
   closer idiom is marginally noisier than the pre-bump closers — the honest minimal
   response to the v4.31 elaborator (drives the lone PASS-WITH-NOTES on lens 8), not
   obfuscation. The `StrikeGreeks` rewrite to `congr_deriv` + named value lemmas is a
   net clarity gain.

**Verdict: PASS-WITH-NOTES** — a faithful mechanical port that preserves every
statement and improves coherence (current API) and one proof's legibility; the only
blemishes are cosmetic idiom noise and one vacuous-binder nit, none blocking.

## 2026-06-23 — commit 2e23025 — corpus 285

**Scope**: D1 — covariation of Itô integrals (the bilinear Itô isometry).
`Foundations/ItoIntegralCovariation.lean` + umbrella import, 4 AxiomAudit pins,
benchmark `sc-ito-covariation-bilinear-isometry` (full), roadmap/coverage notes.
The `[0,T]` Itô CLM is bundled as a `LinearIsometry` (`itoIsometry_T`);
polarization (`LinearIsometry.inner_map_map`) gives `⟪∫φ dB, ∫ψ dB⟫ = ⟪φ, ψ⟫`
(`inner_itoIntegralCLM_T`); `L2.inner_def` unfolds the μ-side to the expectation
form `𝔼[(∫φ dB)(∫ψ dB)] = ⟪φ, ψ⟫` (`covariation_itoIntegralCLM_T`); the diagonal
`φ = ψ` recovers the isometry (`variance_itoIntegralCLM_T`).

**Panel**: three agents — (Mathlib/Degenne coherence + idiomatic register + zero
slop), (concept clarity + first principles + honest scope), (inspired/beautiful
math + architectural ingenuity + AxiomAudit honesty floor).

| lens | verdict |
|---|---|
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS |
| zero slop | PASS |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS |
| beautiful, elegant math | PASS |

**Blocking findings**: none.

**Checks that mattered**: the Mathlib lemmas (`LinearIsometry.inner_map_map`,
`L2.inner_def`, `RCLike.inner_apply`, `conj_trivial`, `real_inner_self_eq_norm_sq`,
`ContinuousLinearMap.coe_coe`) were each cross-checked against ledger-verified
sibling files that use them identically; nothing of B1's isometry is reproved
(the bilinear law is pure polarization of `itoIntegralCLM_T_norm`); the bundled
`LinearIsometry` is novel in the repo (no other `→ₗᵢ[` for the Itô integral) and
is the genuine reusable artifact, not a wrapper-to-inline; `mul_comm` in the
`simpa` is load-bearing, not masking a mismatch (sibling `ItoIntegralL2Dense`
confirms `⟪x,y⟫_ℝ` reduces second-argument-first under this pin); `[IsProbabilityMeasure μ]`
is genuinely required (the CLM needs it; `IsPreBrownian` does not imply it);
`full` status is correct (multi-step composition over a bundled definition, not a
one-line wrapper, not a definitional `rfl`); the RHS is honestly the inner product
`⟪φ, ψ⟫` (the `= ∫ φψ d(trim) = 𝔼∫₀ᵀ φψ ds` chain is a true explanatory gloss, not
a literal Lean claim); the `[0,∞)` analog is honestly deferred; the 4 AxiomAudit
pins are correct and complete at `[propext, Classical.choice, Quot.sound]` (no
`sorry`/`sorryAx`).

**Recorded actions**:
1. *(done in this commit)* docstring polish from panel nits — the predictable
   `trim` measure is described as a `.trim` (not `Measure.restrict`), and the
   `variance_` name is justified in-docstring (the Itô integral is centered, so
   its second moment is its variance).
2. *(open, next session)* **D2** — the general-integrand local martingale — is
   gated on a pathwise continuous-modification of the B1b integral (Doob
   L²-maximal inequality → a.s.-uniform limit of the simple approximants), a
   multi-session build; it is the load-bearing prerequisite for localizing the
   Itô formula (`ito_formula_td_L2_bddDeriv`, presently bounded-derivative only)
   to unbounded/GBM coefficients — the analytic-tower → pricing-tower bridge.
3. *(open)* the `[0,∞)` bilinear analog lands cheaply once a named
   full-trim-measure def is exposed in `ItoIntegralL2Dense.lean`.

## 2026-06-13 — commit 839dd06 — corpus 283

**Scope**: Summit B / B3 — the elementary Itô integral as a continuous local
martingale (the localization entry point). `MathFin/Foundations/ItoIntegralProcessLocalMartingale.lean`
(`itoSimpleProcess_pathContinuous`, `itoSimpleProcess_isLocalMartingale`), corpus
entry `sc-ito-simple-process-local-martingale`.

**Panel**: two agents — (A) slop / coherence / first-principles / idiom, with an
explicit no-sorry-dependency audit; (B) does-it-earn-its-place / continuity-hypothesis
honesty / scope honesty / stale docs.

**Findings & resolution**:
- **BLOCKER (honesty, stale docs)** — `docs/roadmap.md` still read "Next: **B3**"
  as future work, and `docs/coverage.md`'s live-status block was stale (corpus
  280 / 263-ready, pre-B2). Both updated to record B2+B3 as delivered (corpus
  283 / 266-ready); `docs/blueprint.md` frontier note extended with the B3
  localization bridge.
- **MINOR (earns-its-place / clarity)** — the module docstring led with the
  "localization entry point" headline, foregrounding the (trivial) local-martingale
  weakening over the genuine new content. Reordered to lead with the **pathwise
  continuity** as the result and present the local martingale as its consequence
  and the upstream-coherence bridge.

**The earns-its-place judgment (both agents)**: the local-martingale statement is
mathematically a one-line weakening of B1a's true `L²` martingale
(`Martingale.IsLocalMartingale`). It clears the bar because the genuine content is
`itoSimpleProcess_pathContinuous` — the **first sample-path regularity result** in
a tower that was otherwise entirely `L²`/in-measure — and the local-martingale is
the honest, canonical framing that connects the integral to Degenne's localization
machinery (the gateway for SDE/Lévy/Girsanov). **Continuity-hypothesis honesty**:
PASS — taking `∀ ω, Continuous (B · ω)` as a hypothesis is the standard pathwise
setting (`IsPreBrownian` fixes only the finite-dim laws; a continuous version
exists by Kolmogorov–Chentsov), stated honestly in three places; consuming
Degenne's KC construction is infeasible for an arbitrary `IsPreBrownian B`.
**No-sorry audit**: PASS — `#print axioms` is `[propext, Classical.choice,
Quot.sound]`; the `isStable_submartingale` `sorry` in upstream `LocalMartingale.lean`
is provably off the `Martingale.IsLocalMartingale` proof path. **Coherence**: PASS —
pure consumption (B1a + `Martingale.IsLocalMartingale` + `itoSimpleProcess_apply`);
the private `isCadlag_of_continuous` is justified plumbing (no `Continuous → IsCadlag`
exists upstream; `IsCadlag` is Degenne-only). **Scope**: PASS — `full` justified,
no overclaim (simple integrands, continuity assumed).

**Verdict: PASS** (one stale-doc blocker + one docstring minor, both fixed). Build
8726 jobs green, axioms-clean; ledger 283/283 fresh; pytest 19.

## 2026-06-13 — commit 6bd9477 — corpus 282

**Scope**: Summit B / B2 — the unbounded-horizon `[0,∞)` Itô integral as a
continuous linear isometry. `MathFin/Foundations/ItoIntegralL2Dense.lean`
(`itoIntegralL2`, `itoIntegralL2_norm`), corpus entry
`sc-ito-infinite-horizon-isometry`, plus de-privatising
`ItoIntegralCLM.setIntegral_eq_zero_of_orthogonal_pred` for reuse. Closes the
σ-finite density gap recorded in `docs/ito-integral-clm-deferred.md`.

**Panel**: three agents over the eight lenses (slop / idiom / clarity;
coherence / first-principles / architecture; inspired / elegant / honesty).

**Findings & resolution** (all fixed before this verdict):
- **BLOCKER (clarity/honesty)** — `ItoIntegralCLM.lean`'s module docstring still
  declared the unbounded-horizon CLM "left gated … not required by any
  downstream pricing module." Now false on both counts (it is built, and this
  file de-privatises a CLM lemma to serve it). Rewritten to point at
  `ItoIntegralL2Dense` and name the consumed bridges.
- **MINOR (slop/idiom)** — five implementation-detail helpers (`iocSP`,
  `uncurry_iocSP_eq`, `inner_simpleAssembly_iocSP`, `itoOrthRect`,
  `aezeroOfOrth`) leaked into the public namespace, against the repo convention
  (only the density theorem + CLM + isometry are public, as in
  `ItoIntegralCLM`/`WienerIntegralL2`). Marked `private`.
- **MINOR (clarity)** — module doc said B2 "removes the horizon bound from
  `itoIntegralCLM_T`"; it is a sibling CLM reusing that file's density
  machinery, not a direct extension. Reworded.
- **MINOR (honesty, stale docs)** — `docs/coverage.md`, `docs/blueprint.md`,
  `docs/roadmap.md`, and the deferred-doc header still listed the
  infinite-horizon variant as open/future. All updated to record B2 as
  delivered; the deferred doc carries a `CLOSED 2026-06-13` stamp.

**Coherence / first principles / architecture** — PASS, unanimous. Pure
consumption of the finite-horizon layer (the `predictableRect` π-system reused
verbatim, T-independent) + Degenne `SimpleProcess` + Mathlib `extendOfNorm` /
`Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`; nothing of the π-system or the
isometry is reproved. The σ-finite-exhaustion argument (per-frame `g =ᵐ 0` via
the finite-horizon lemma, then a null-cover patch over `{0}×univ`) is sound and
formally tight, and is the right architecture — reduce the σ-finite case to the
already-proven finite case rather than rebuild density from scratch (and it
sidesteps the upstream elementary-set π-system gap the deferred doc anticipated
needing). `full` status justified: a genuine theorem, axioms-clean, AxiomAudit-pinned.

**Verdict: PASS** (one blocker + minors, all fixed). Build 8725 jobs green,
axioms-clean; ledger 282/282 fresh; pytest 19.

## 2026-06-12 — commit 867d265 — corpus 281

**Scope**: the deferred per-`t` Itô isometry, now closed —
`MathFin/Foundations/ItoIntegralProcessIsometry.lean` (`itoProcessCLM_norm_sq`:
`‖(φ●B)_t‖² = ∫_{(0,t]×Ω} φ² d(trimMeasure_T T)` `= ∫₀ᵗ E[φ_s²] ds`, for every
predictable `φ ∈ L²([0,T])` and `t ≤ T`) — plus the de-privatisation of the generic
`lp_two_norm_sq` in `ItoIntegralL2` (reused, not copied) and 1 new `full` corpus entry
`sc-ito-general-time-isometry`. This is the refinement B1b openly deferred (the
band-over-trimmed-measure computation).

**Panel**: 3 independent agents — two splitting the eight lenses
(coherence/slop/idiomatic/first-principles; inspired/architecture/clarity/beauty), one
completeness/faithfulness critic (snippet ⊨ theorem, no circularity, AxiomAudit honesty,
de-dup). Read-only, no Lean.

**Per-lens verdicts — all PASS**:
1. *Inspired math* — the L²-energy law that makes the Itô integral an isometric
   embedding at every `t`, not only the terminal; the load-bearing fact behind
   quadratic-variation / hedging-error analysis in continuous time.
2. *Mathlib/Degenne coherence* — consumes B1a's `itoSimpleProcess_isometry_time`, the
   repo's `integral_rectTerm_mul` / `trimMeasure_T_eq_restrict` / `simpleAssembly_T`, and
   Mathlib's `DenseRange.equalizer` / `integral_trim` / `eLpNorm_indicator_le`. The one
   hand-built object `truncCLM` is justified: Mathlib has only the *constant*-indicator
   `indicatorConstLp` and no `Lp→Lp` restriction CLM (confirmed by loogle search).
3. *Zero slop* — every helper load-bearing; stepping-stones `private`; the generic
   `lp_two_norm_sq` de-duplicated rather than copied (the very concern that triggered
   this round). [fix applied: `integral_rectTerm_mul_band` made `private`.]
4. *Architectural ingenuity* — reduce the per-`t` isometry to a band-restricted *simple*
   isometry, then transfer by density through `truncCLM`; reuses the SAME
   `simpleAssembly_T` dense embedding, so the bridge to B1a is definitional.
5. *First principles* — no circularity (`truncCLM_norm_sq` assumes no isometry; the
   simple case is B1a + Fubini + the pure-ℝ overlap identity), and the statement is the
   genuine isometry — RHS a real integral against the predictable Lebesgue⊗μ measure, not
   `‖x‖²=‖x‖²` in disguise.
6. *Idiomatic register* — `mkContinuous` CLM, `DenseRange.equalizer` + `congrFun`,
   `filter_upwards … rw [show …]`, `omit … in` placement — all match the adjacent
   `ItoIntegralProcessGeneral` / CLM files.
7. *Concept clarity* — docstrings name the key identity and state honest scope. [fixes
   applied: the `truncCLM` docstring no longer flatly calls itself "the orthogonal
   projection" (only norm-`≤1` is formalised) and now states the *squared*-norm isometry;
   the `ItoIntegralProcessGeneral` module docstring updated from "deferred" to "proved in
   the companion module".]
8. *Beautiful, elegant math* — the reconciliation `band_overlap_real` (B1a's
   per-endpoint-`∧t` overlap form = the joint-overlap-`∩(0,t]` form, both measuring
   `(p.1,p.2]∩(q.1,q.2]∩(0,t]`) gets its own named lemma with the "why" in prose.

**Blocking findings**: none (3-agent consensus).

**Recorded actions**:
1. *(done this round)* de-privatised `ItoIntegralL2.lp_two_norm_sq` and deleted the
   temporary in-file copy — the generic `‖g‖² = ∫ g²` now has a single home and three
   consumers across two files.
2. *(done this round)* `integral_rectTerm_mul_band` → `private`; `truncCLM` docstring
   sharpened (orthogonal-projection qualification + squared-norm statement).
3. *(open, non-blocking)* `∫₀ᵗ E[φ_s²] ds` as an *explicit* Lean term (the Fubini split
   of the product integral) is described in prose but not formalised as a standalone
   corollary — a cheap future add if a consumer needs it.

Cold `lake build` 8724 jobs green, axioms-clean; ledger 281/281 fresh; router/values
pytest green.

## 2026-06-12 — commit 5f41a11 — corpus 280

**Scope**: this session's Summit B / B1b deliverable —
`MathFin/Foundations/ItoIntegralProcessGeneral.lean` (the **general-integrand**
Itô integral `(φ●B)_t = ∫₀ᵗ φ dB` for `φ ∈ L2Predictable[0,T]` as a continuous L²
martingale on `[0,T]`: `itoProcessCLM` via `extendOfNorm` along `simpleAssembly_T`,
the definitional bridge to B1a, the key identity `(φ●B)_t = condExpL2 𝓕_t
(∫₀ᵀ φ dB)`, a.e.-adaptedness, the L² martingale property, the contraction
`‖(φ●B)_t‖ ≤ ‖φ‖`, the terminal isometry `‖(φ●B)_T‖ = ‖φ‖`, and L²-continuity) plus
its 3 new `full` corpus entries (`sc-ito-general-martingale` /
`-terminal-isometry` / `-l2-continuity`). The explicit per-t isometry
`E[(φ●B)_t²] = ∫₀ᵗ E[φ²] ds` is deliberately deferred (the band-over-trimmed-measure
computation) — openly flagged.

**Panel**: 3 independent agents, the eight lenses split among them, reading the new
file + its dependencies + the corpus prose (read-only, no Lean).

**Per-lens verdicts — all PASS**:
1. *Inspired math* — the L² Itô integral of a *general* predictable integrand as a
   continuous L² martingale; closes the density gap B1a left (simple integrands
   only). The load-bearing fact behind continuous-time pricing/hedging.
2. *Mathlib/Degenne coherence* — pure consumption: `condExpL2` +
   `MemLp.condExpL2_ae_eq_condExp`, `mem_lpMeas_iff_aestronglyMeasurable`,
   `condExp_condExp_of_le`, `DenseRange.equalizer`, `TendstoUniformly.continuous`,
   `eLpNorm_condExp_le`, plus B1a + `itoIntegralCLM_T`. The consumed surface was
   verified to exist upstream; nothing reproved.
3. *Zero slop* — every declaration load-bearing; the two helpers
   (`condExp_itoSimple_eq`, `itoIntegralCLM_T_simpleAssembly_T`) earn their place
   (no upstream duplicate; each discharges a real `extendOfNorm_eq`/martingale
   obligation, not a thin wrapper).
4. *Architectural ingenuity* — `itoProcessCLM := itoProcessLM.extendOfNorm
   simpleAssembly_T` reuses the exact recipe that builds `itoIntegralCLM_T`, making
   the bridge to B1a definitional (`rfl` after `extendOfNorm_eq`); the key identity
   collapses martingale/adaptedness/contraction/terminal-isometry into corollaries
   of ONE identity; the t-uniform contraction reused for
   continuity-via-`TendstoUniformly`. No simpler architecture found by the panel.
5. *First principles* — derived from B1a's martingale + the condExp tower + the
   terminal isometry + the real `simpleAssembly_T_denseRange`; no hypothesis
   smuggles the conclusion (`hBmeas`, T-boundedness are honest side-conditions).
6. *Idiomatic register* — disciplined `simp only` (always an explicit lemma list),
   `calc`/`filter_upwards`, B1a-consistent naming (`_norm_le`, `_isMartingale`,
   `_eq_condExpL2`, `_l2_continuous`), no hammer/omega/native_decide.
7. *Concept clarity* — statements + per-theorem docstrings model-grade (after the
   blocking fix below).
8. *Beautiful/elegant math* — the key identity is the spine; the five properties
   read off as short corollaries; the `(μ := μ)` ascriptions are load-bearing
   (implicit-`variable` disambiguation), not noise.

**Blocking finding (fixed before this verdict)**:
- The file-level docstring (lines 16-17) overclaimed the **deferred** per-t
  isometry `E[(φ●B)_t²] = ∫₀ᵗ E[φ²] ds` as delivered, contradicting the file's own
  theorems (only the contraction + terminal isometry are proved) and the honest
  corpus prose. **Fixed** in 5f41a11: the header now states the contraction +
  terminal isometry and marks the per-t isometry as the deferred refinement — the
  `.lean` header brought back into sync with the (already-honest) corpus JSON.

**Recorded actions / non-blocking notes**:
1. *(nit, open)* `condExp_itoSimple_eq` overlaps in content with the inline
   `hT'eq`/`hcond` block inside `itoSimpleProcessLp_norm_le` (the same
   B1a-martingale-to-terminal fact, once as an inequality-feeder, once as a
   reusable `=ᵐ`). Defensible (distinct downstream shapes); a future tidy could
   route the bound through the extracted lemma. Cosmetic — next touch of the file.
2. *(scope, accepted)* the per-t isometry is the genuine remaining gap (the file
   proves the L²-energy law only as the one-sided contraction off the horizon,
   exact at the terminal); openly flagged in the header + all 3 corpus scopes. The
   band-over-trimmed-measure computation (a `restrict`∘`trim`∘`prod` rectTerm
   integral mirroring `simpleProcessL2_norm_sq`) is the B1b follow-up / B2.

## 2026-06-10 — commit c288861 — corpus 277

**Scope**: this session's B1a deliverable — `MathFin/Foundations/ItoIntegralProcessMartingale.lean`
(the elementary Itô integral as a *process*: adaptedness, the conditional martingale-difference,
the martingale property, the time-indexed isometry, L²-continuity) plus its 3 new `full` corpus
entries `sc-ito-simple-process-{martingale,isometry,l2-continuity}`. Machine gates green before the
panel (cold build 8709 jobs, pytest 19, ledger 277).
**Panel**: three independent agents — (zero slop + idiomatic register), (Mathlib/Degenne coherence
+ concept clarity), (the four judgment lenses: inspired / architecture / first principles / elegance).

| lens | panel verdict | after fixes |
|---|---|---|
| inspired math quality | PASS | PASS |
| Mathlib/BrownianMotion coherence | PASS-WITH-NOTES | PASS |
| zero slop | PASS-WITH-NOTES | PASS |
| architectural ingenuity | PASS | PASS |
| first principles | PASS | PASS |
| idiomatic register | PASS-WITH-NOTES | PASS |
| concept clarity | PASS-WITH-NOTES | PASS |
| beautiful, elegant math | PASS | PASS |

**Blocking findings**: none.

**The convergent finding (all three reviewers, non-blocking)**: `condExp_adapted_mul_increment` —
the conditional martingale-difference — was framed as "the crux" but `itoSimpleProcess_isMartingale`
does not call it (it applies the same set-integral characterisation directly per `𝓕_s`-set), leaving
the lemma as unconsumed, over-sold public surface. **Resolved by reframing, not refactoring**: the
direct set-integral martingale proof is cleaner than routing through the condExp tower, and the lemma
legitimately *completes the conditional/unconditional API pair* with the public
`integral_adapted_mul_increment` (and is the natural form the gated Girsanov/Lévy/martingale-rep
cluster will consume). Fixed: the module docstring and the lemma's own docstring now state it is the
reusable conditional sibling, with the martingale established directly; the benchmark scope matches.

**Other fixes (minor, this round)**:
- The isometry docstring + benchmark scope implied the proof *delegates* to `itoSimple_sq_integral`;
  reworded to "mirrors" its structure, with the terminal isometry *mathematically recovered* (not a
  proof step) when `t` is past every right endpoint.
- Corpus `sc-ito-simple-process-martingale` called the martingale "the defining property" → "a
  fundamental property" (the L²-limit/isometry construction is the standard "defining" one).
- Documented the deliberate coercion-after-min ascription at the isometry RHS (prevents a future
  "cleanup" that would break the `rect_increment_pairing` match).

**Checks that mattered**: the truncated-isometry "rectangle past `t`" case is genuinely correct
(both the term and the overlap factor vanish — `min(t,·) ≤ t ≤ max(t,·)`), not a fudge; the
√-Hölder continuity bound honestly *bounds* (Cauchy–Schwarz over the finite support + the
single-increment isometry `integral_adapted_sq_mul_increment_sq`) rather than *computes* — no
spurious cross-term claim, and the docstring says so; `clamped_increment_eq`'s `grind` close is over
an exhaustive 16-way `le_total` split; the three `full` re-exports carry genuine proofs (no
rfl-tripwire), axioms-clean.

**Recorded actions (non-blocking, next cleanup pass)**:
1. `memLp_truncated_term` (private, this file) duplicates the per-term case split of
   `ItoIntegralProcess.memLp_itoSimpleProcess`; hoist it public into `ItoIntegralProcess.lean` and
   reimplement the loop body via it (~15 lines, removes the drift).
2. `hVL2` (`∀ p, MemLp (V.value p) 2 μ`) is re-derived identically in the martingale and continuity
   proofs; hoist to one `have`/private lemma.
3. Four `funext ω; by_cases h : ω ∈ s <;> simp [h]` indicator steps have direct Mathlib lemmas
   (`Set.indicator_one_mul` / `_mul_left`); fold on next touch.

## 2026-06-09 (round 6) — WHOLE-REPO values review — corpus 274

**Scope**: at the user's request, a second full-repo panel two days after round 5 — **eight
reviewers, one per lens**, with the round-5-unreviewed delta (`c3a3498`/`d2cb7bd`/`3a25518`/`bde8f24`)
reviewed in full and the whole-repo budget pointed at the **long tail** (Actuarial / DeFi /
Performance / Portfolio / FixedIncome / Futures / Binomial / RiskMeasures + older Foundations),
since the FK/Itô/Merton headliners had four recent reviews. Machine gates green before the panel
(19 pytest, ledger 273/273).

| lens | panel verdict | after fixes |
|---|---|---|
| inspired math quality | BLOCKING (2) | PASS |
| Mathlib/BrownianMotion coherence | PASS-WITH-NOTES | PASS |
| zero slop | PASS-WITH-NOTES | PASS |
| architectural ingenuity | PASS-WITH-NOTES | PASS |
| first principles | BLOCKING (1) | PASS |
| idiomatic register | PASS-WITH-NOTES | PASS |
| concept clarity | BLOCKING (1, same as first-principles') | PASS |
| beautiful, elegant math | PASS-WITH-NOTES | PASS |

**Blocking findings (3, all fixed this round):**

1. **`sc-thm-8.2.5` was uninhabitable** (first principles + concept clarity, found *independently*
   by two reviewers; then machine-confirmed by a daemon-checked refutation
   `SDEExistenceUniqueness → False`). The round-5 follow-up rewrite (`3a25518`) quantified the
   uniqueness candidate's diffusion integral `IσY` freely, so every process discharges the solution
   premise by taking its own residual as the "integral" — the field collapses to "every process
   started at `η` equals `X`", refuted inside any inhabitant by `Y := X + t`. The spec encoded a
   contradiction; `unique_strong_solution` was a theorem about an empty type. **Fix**: an opaque
   integral-**operator** encoding `Iσ : (ℝ → Ω → ℝ) → ℝ → Ω → ℝ`, consumed as `Iσ X` (solution)
   and `Iσ Y` (uniqueness premise) — candidates genuinely pinned to the same equation; the
   uniqueness conclusion scoped to `0 ≤ t` (the synthesizer found the unscoped `∀ t` conclusion
   left candidates free at negative times — a second uninhabitability the panel itself missed);
   a `: Prop` ascription (register corroboration); and an **in-snippet inhabitant `example`**, so
   non-vacuity is machine-guarded permanently. Corollary corrections in `coverage.md`.
2. **`FixedIncome/Vasicek.lean` claimed an unproved limit theorem** ("limiting value `r(∞) = θ`" —
   no `Tendsto` existed in FixedIncome). **Fixed in the strong direction**:
   `vasicekDeterministic_tendsto_mean` added (exponential mean reversion, consuming `hκ` exactly
   as the docstring advertised), making the claim true rather than deleting it.
3. **`Performance/RatiosExtended.lean` claimed an unproved `Var(R_p − R_b)` expansion** for
   `trackingErrorSq`. **Fix**: de-claimed — the def is the model definition, the variance-level
   identity honestly out of scope; `trackingErrorSq_self`'s "decomposition" header retitled.

**Fixed minors (the round's main wave):**

- *PricingKernel recomposed* (3 lenses converged): `statePrices_two_state` is now **defined** as
  `e^{−rT} · emmWeight{Up,Down}` — the Phase-37 weights, newly **named** in `FTAPTwoState` and
  consumed by `emm_of_signs` — and `pricingKernel_two_state` is defined as the two-state
  `statePricePricing` instance, so `_linear`/`_bond`/`_nonneg` genuinely consume `StatePrices`
  and the "via state-price linearity" docstring describes the actual proof (the round-5-era
  "via Greeks" fiction class, eliminated structurally). Phantom Results name fixed; `⟨0, by omega⟩`
  statement literals → vector literals. `FTAPTwoState`'s own Results list had two more phantom
  names (`signs_of_noArbitrage`, `ftap_two_state`) — rewritten with an honest not-formalized note.
- *FTAPMultiState*: misleading "backward direction" title fixed (the file proves the **forward**
  direction); the zero-consumer constructor-adapter `hasEMM_multi_of_candidate` (bold-titled
  "Backward FTAP" over an anonymous-constructor application) deleted; closing `linarith` → the
  pointed `h_sum_pos.ne' h_zero`.
- *VarianceSwapEquivalence*: split `(T ≠ 0) + (0 ≤ T)` merged to the memorable `(hT : 0 < T)`
  (+ snippet); intro-docstring normalization inconsistency fixed.
- *André's reflection principle wired* (the round's inverted-weight repair): `PathReflection.lean`'s
  stale "the hitting-time bijection is downstream work" de-staled (the bijection was *in the file*),
  Results list completed, and the counting form wired as **`mf-reflection-principle-counting`**
  (`Nat.card_congr` over `reflectionPrincipleEquiv_below`) with a curated AxiomAudit pin — the
  library's best long-tail mathematics now has corpus existence.
- *Coherence cites*: `herfindahl_card_inv_le_of_sum_one` now consumes Mathlib's
  `sq_sum_le_card_mul_sum_sq` (was hand-reconstructed; a pre-existing dead `have` went with it);
  `net_premium_principle := (eq_div_iff hA).symm`; `max_sub_max_neg :=
  max_zero_sub_max_neg_zero_eq_self` (kept under its finance name as the file's conceptual pivot,
  with the upstream cite documented).
- *Register*: `annuityDueValue` → `annuityDue_closed_form` (+ snippet); `IsBLPosteriorMean_unique`
  → dot-notation `IsBLPosteriorMean.unique`; CAPM's `a = b ↔ a − b = 0` anti-shape replaced by a
  real `jensenAlpha` def + `jensenAlpha_eq_zero_iff := sub_eq_zero`; DeFi `swap_output_lt_y`
  strengthened from `lt ∨ y = 0` to the honest `0 < y ⟹ lt` (named product certificate);
  `cml_decomposition_unique`'s misnomer resolved by **adding the uniqueness direction**
  (`cml_weight_unique := (eq_div_iff hσ_t).mpr`) so the entry's name became true — the snippet now
  exports recovery ∧ uniqueness.
- *Spectral*: the title promised monotonicity that did not exist — the real `spectralRisk_mono`
  added (the file's first contentful inequality); Results list fixed.
- *Stale-docstring batch*: 8 phantom identifiers fixed across DriftLimit / ForwardRate / CAPM(3) /
  Markowitz / MarkowitzLagrangian / SharpeFOCDerivation (+ American's loose `BinomialModel` ref,
  CAPMEquilibrium cross-ref; the Markowitz bullet also claimed positivity hypotheses the lemma
  does not take).
- *Corpus honesty*: `mf-compound-poisson-mgf` demoted `full` → `reduced_core` (the exp-algebra core
  of the named MGF identity — the taxonomy's own definition; the Kelly-demotion pattern one notch
  above `rfl`, exactly what the judgment layer exists to catch); `mf-credit-spread-time-avg-hazard`
  upgraded honestly (the definitional spread identity now *paired with* the substantive FTC
  recovery `hazard_eq_neg_log_deriv_survival`, both exported, the scope note splitting
  definitional-vs-derived); `gir-thm-9.1.7`'s scope note now states exactly what the L¹-bound
  field does and does not encode (no `θ`, no `B`, not Novikov's condition) + Doléans–Dade spelling;
  10 scope notes' stale "toolchain v4.18.0" → pin-stable wording; `mart-thm-2.6.7`'s pre-strip
  "inlined helper" provenance fixed; `mf-cds-fair-spread` abstract-annuity-factor disclosure.
- *Docs*: `bridges.md` `||`-merged rows 42/40 split (the Phase-40 row had been invisible in
  rendered markdown since 2026-05-30); row 42's wrong "discrete-Lagrangian" gloss and its mention
  of the deleted adapter fixed; the CondExpJensen audit row annotated **DELETED** (it said "NOT
  duplicate" about a file deleted as a duplicate); `ConvexPricingFunctional` got its missing
  catalogue row (53a, recording its layering exception); `blueprint.md`'s prose walk caught up to
  the generated spine (4 sections: FK heat flow, Markov path law, **BS PDE from Feynman–Kac**,
  Merton dominance, + cross-link from the Itô 🚧 section); `roadmap.md`'s same-day-stale "next
  candidates" fixed; `patterns.md` now declares the canonical `exp (-(r * τ))` form for new files;
  `coverage.md` live-status pointer + the 8.2.5 round-6 correction note; **README's Reproducibility
  pins were ALL stale** (toolchain rc1→rc2, Mathlib `f23306…`→`c87cc97…`, BM `16d15e…`→`fa590b1…`)
  — a panel miss caught in the follow-up sweep, fixed.
- *Repo hygiene*: the tracked-but-gitignored `docs/superpowers/specs/…` design spec untracked
  (`git rm --cached`; the dir is deliberately private); `docs/README.md`'s links into that dir
  removed and a `values-review.md` row added.

**Declined / corrected reviewer claims**: lens 3's "tracked stale HF snapshot jsonl" was wrong on
git status — the jsonl is untracked (local-only, no public exposure); the genuinely tracked-but-
ignored file was the reorg spec (fixed above). Elegance refactors of sound, heavily-reviewed proofs
were deferred with sketches recorded rather than churned (below), per the panel's own
keep-deferred recommendations.

**Recorded actions (deferred, owner = next session touching those files):**
1. *(elegance, sketched in the panel reports)* `NewtonConvergence` mirrored case duplication
   (~30 lines) → one `abs_integral_le_sq` helper; `SharpeFOCDerivation`'s 4× spelled-out derivative
   numerator → rewrite-through-factorization (~50→15 lines); `UtilityDerivation` have-pyramid →
   `calc` (+ canonical `ConcaveOn` hypothesis).
2. *(slop, catalogued)* dedup pairs: `ItoIntegralRiemannBridge`/`TD` (accepted-debt class, fold
   with the SimpleProcess/L2Predictable unification); `Immunization`/`ConvexityImmunization`
   shared weighted-exponential-sum `HasDerivAt` skeleton; `integrable_payoff_mul_d{t,x}K` stays
   deferred (fold when the general-`g` FK PDE lands); `MertonClassicDisplay`'s twice-proved
   rate-shift identity → private lemma.
3. *(elegance, assessed and closed)* the exp-sign convention split is **accepted permanently**;
   the canonical form for new files is now in `patterns.md`.
4. *(slop, Lean-gated)* dead `set … with` bindings: the two reviewers' static lists disagree
   (8 vs 7, overlap 4) — itself proof the item needs per-case Lean confirmation; batch into
   sessions already touching those files.
5. *(register, recorded)* `HasEMM_*_state` hybrid casing kept (coherent in-repo family);
   finance-acronym name parts (`_FOC`, `_SML`, `_QV_`) kept; ASCII-vs-unicode subscript census
   recorded; `swap_output_*` family naming; `VasicekSDE`/`MertonAmericanCallTree` `exp_zero`-show
   one-liners; `Phi_neg`'s `Iio_ae_eq_Iic` polish.
6. *(infrastructure, noted)* `AxiomAuditGen` pins only head-position constants of snippet proofs —
   compound proofs (`Nat.card_congr (…)`, anonymous constructors) contribute nothing; the
   reflection keystone is pinned in the **curated** audit instead. Consider a generator extension.
7. *(corpus, judgment note)* the long-tail trivia cluster (`mf-tracking-error-self`,
   `mf-triangle-arbitrage-unique`, `mf-log-forward-bsTerminal`, `mf-sortino-translation`) stays
   honest-but-thin `full`; upgrade toward the real theorems when those files are next touched.

**Positive exemplars recorded by the panel**: `Portfolio/CovariancePSD` (the docstring's story IS
the certificate), `Futures/Black76Greeks` (structural reduction made visible),
`RiskMeasures/RockafellarUryasev` (certificate-first elegance), `RiskMeasures/UtilityDerivation`
(the coherent axioms given content from a primitive), `Foundations/CarrMadan` (the model
upstream-coherence note), `FixedIncome/KMVMerton` (structural-identity honesty),
`pp-prop-3.3.6`'s scope note (the model reduced_core disclosure), and the snippet corpus's
mechanically perfect import discipline (0 blanket-Mathlib violations in 235 MathFin-importing
snippets).

**Verdict**: **PASS after fixes** — all three blockers repaired and machine-verified (the 8.2.5
refutation AND the repaired spec's inhabitant were both daemon-checked; the inhabitant ships
inside the snippet as a permanent non-vacuity guard). Net: corpus 273 → **274**
(+`mf-reflection-principle-counting`), **full 239** (−1 compound-poisson demotion, +1 reflection
wire), wrappers 18, reduced 17, delivery-ready **257**/274. lake build **8708 jobs green**,
MathFin sorry-free, axiom-clean (generated audit regenerated + a new curated pin); ledger
**274/274 fresh**; **19 pytest gates green**. Shipped alongside: the repo-presentation upgrade
(README landmark-results table + how-verification-works section + the stale Reproducibility pins
fixed; GitHub description/topics; docs index repaired).

## 2026-06-08 (round 5) — WHOLE-REPO values review — corpus 270

**Scope**: at the user's request, a full-repo panel (not just the Feynman–Kac keystone) — **six**
reviewers: two deep on the keystone tower, plus one each on `MathFin/Foundations/`, the pricing modules
(`BlackScholes`/`Futures`/`Binomial`/`FixedIncome`/`Portfolio`/`Performance`/`RiskMeasures`/`Actuarial`/`DeFi`),
the benchmark corpus (all 270 entries), and `docs/` + repo-meta.

**Headline**: the library is in **excellent shape**. No forbidden tactics anywhere; no proof smuggling;
no `rfl`/`trivial`-in-disguise `full` entry; every `library_wrapper` is a genuine Mathlib/Degenne
re-export; the `full`/`wrapper`/`reduced` split (236/18/16) is **honest**; coherence with the pinned
Mathlib/Degenne is real (no reproving of pinned lemmas); the Itô-formula ladder and the FK keystone are
principled, not redundant; `RockafellarUryasev`, the BS "magic identity" Greeks, Merton dominance, and the
dividend-Greek reparametrization are genuinely elegant. **The findings are honesty-of-claims drift (stale
docs/docstrings after the keystone landed) + a few pre-existing orphans + minor faithfulness/nits — no
blocking findings.**

**Applied this round** (public-facing honesty, no rebuild): README counts → 270/236/254/16, "What's not
done" corrected (dropped the now-`full` time-dependent Itô; Markov 6→5), the FK→BS-PDE keystone surfaced
in "What's covered"; CITATION.cff 251→254; `sc-thm-9.2.1` scope note (metadata **and** in-snippet)
de-staled — the "~300–500 lines left as upstream work" claim was false (that infra is built and consumed
by `sc-bs-pde-feynman-kac`); coverage.md round record. **PASS 2** (Lean rebuild) then fixed the
keystone-tower docstring drift: `PDEFromFeynmanKac` ("Only step 4 remains" → step 4 is the capstone;
"(until now consumed by nothing)" → load-bearing; wrong `Foundations.` qualifier on opened lemmas; step
numbering) and `FeynmanKacHeatEquation` (three stale "deferred heat-PDE direction" notes — the work is in
the file; the "Main results" block now lists `hasFDerivAt_heatKernel` + the `feynmanU` derivatives/heat
equation; the `heatKernel_t_eq_half_y_y` docstring, which wrongly said "not consumed" when
`feynmanU_heat_equation` consumes it) — all now honest that the keystone is complete and the heat flow
load-bearing.

**Orphans — REFLECTED, kept** (per the user's "always reflect if orphans will be used later", which
flipped a too-aggressive "delete"):
- `hasDerivAt_feynmanU_t` has zero *code* consumers (only docstring mentions) but is **kept public**: it
  is the `∂_t` building block the still-open fully-general-`g` PDE + uniqueness will consume, and it
  completes the natural `∂_t / ∂_x / ∂_xx` heat-flow API triple. Privating it would be wrong.
- The 3 `unfold;ring` lemmas in `PDEFromIto.lean` (`bsItoDrift_eq_itoDrift2D`,
  `bsItoDrift_no_time_eq_itoDrift`, `bs_pde_lhs_eq_drift_minus_rV`) are **kept**: they are the named
  coherence bridges that file exists to state (the bespoke BS drift *is* the general 1D/2D Itô drift
  specialised; the PDE LHS = drift − rV), carrying real conceptual content, and the file's own deferred
  martingale-route continuation (discounted price is a `Q`-martingale ⟹ driftless) consumes them. Not slop.

**Deferred, prioritized** (catalogued so nothing is lost — a clean follow-up cleanup):
- *[Lean, umbrella] Foundations orphan modules* (~700 lines, zero consumers): `VarianceSwapEquivalence`
  (a literal re-export anti-wrapper), `StochasticInterval` (the abandoned upstream-PR body), `PricingKernel`,
  `FTAPMultiState` → wire to a benchmark or delete. (`PricingFromBrownian` is intentional BM-grounding — keep.)
- *[corpus] `sc-thm-8.2.5`* (reduced_core): the SDE structure encodes a Lebesgue `∫σ ds`, not Itô `∫σ dB`
  (the `B` parameter is dead) → use an opaque adapted stochastic-integral field, mirroring `sc-thm-7.5.2`.
  `sc-thm-9.2.1` name/description state the full PDE+uniqueness (disclosed in scope) → optionally narrow.
- *[docs] roadmap.md / bridges.md / blueprint.md*: log the FK round, add the FK→BS-PDE bridge row, and
  regenerate the blueprint spine (tag the keystone `@[blueprint]`); `feynman-kac-growth-deferred.md` add a
  "superseded — a kernel-differentiation FK route landed" note.
- *[style, declined/deferred]*: ~159 `Real.` qualifiers under `open Real` — **declined** (the file
  consistently qualifies; low-value, high-churn, disambiguation-fragile); the `integrable_payoff_mul_d{t,x}K`
  / `curve_*` boilerplate dedup; 8 dead `set … with h…_def` binding names; 9 honestly-labeled re-export
  shim files; DeFi `internalPrice`/`arbitragePresent` + a `Performance/Ratios` docstring word.

**Verdict**: PASS. No blocking findings; the proofs across the whole repo are sound, elegant, and honest.
The remaining work is honesty-drift cleanup + pre-existing orphan housekeeping, fully catalogued above.

**Follow-up execution (2026-06-09)** — the catalogued deferred items above were executed (housekeeping of
panel-vetted "wire or delete" items, no fresh mathematical content, so no new panel):
- *docs*: the FK round logged in `roadmap.md` (new phase), `bridges.md` (the "FK" bridge row), and
  `feynman-kac-growth-deferred.md` (SUPERSEDED banner — its "deferred, not needed ever" kernel-
  differentiation route is exactly what shipped).
- *corpus faithfulness*: `sc-thm-8.2.5` SDE diffusion `∫σ ds` (dead `B`) → opaque adapted Itô integral
  `IσX`, mirroring `sc-thm-7.5.2`. Stays `reduced_core`, now faithful.
- *orphans, reflected per [[feedback_orphan_future_use]]*: `FTAPMultiState` (Phase 42 forward),
  `PricingKernel` (Phase 53 butterfly), and `VarianceSwapEquivalence` (Phase 45 equivalence) **wired** to
  new `full` corpus entries (`mf-ftap-multi-state-forward` / `mf-pricing-kernel-butterfly` /
  `mf-variance-swap-equivalence`); the literal anti-wrapper `varianceSwap_equivalence` removed (subsumed by
  the genuine two-functional theorem). `StochasticInterval` **kept** — Degenne #440 upstream-PR body,
  two-AxiomAudit-anchored, named `ElementaryPredictableSet` gap in the deferred Itô-CLM record.
- *blueprint*: the keystone `bsV_satisfies_bs_pde_via_feynmanKac` + the kernel heat equation
  `feynmanU_heat_equation` are now `@[blueprint]` spine nodes (curated AxiomAudit guards added; spine
  regenerated — the FK tower links into the existing `bsCall` node).

Net: corpus 270 → **273**, full 236 → **239**, delivery-ready **257**/273, 16 reduced. lake build 8708
jobs axiom-clean; AxiomAuditGen 226 guards; ledger 273/273 fresh; 19 gate tests green. Still-open
(unchanged): the fully-general continuous-`g` FK PDE + uniqueness; variable-coefficient FK (local-vol/
Heston) on the general-Itô layer; the Markov renewal/spectral cluster; P1 the CRR→BS error-constant paper.

## 2026-06-08 (round 4) — the keystone complete: BS PDE from Feynman–Kac — corpus 269

**Scope**: step 4 — `bsV_satisfies_bs_pde_via_feynmanKac`: the Black–Scholes PDE
`−∂_τV + ½σ²S²∂_SSV + rS∂_SV − rV = 0` derived *independently* from the Feynman–Kac representation,
closing the two-tower gap. Plus `hasDerivAt_bsV_SS_fk` (Gamma via FK) and the two integrability helpers
(`integrable_payoff_mul_d{t,x}K`). The whole chain — `hasFDerivAt_heatKernel → hasDerivAt_heatKernel_comp
→ hasDerivAt_feynmanU_comp → {Δ,Γ,Θ Greeks} → the PDE` — is now consumed end-to-end; `feynmanU` is
load-bearing for the PDE.

**Panel**: one adversarial reviewer (try-to-refute + no-smuggling audit), synthesised with Opus judgment.
**No blocking findings.** Verified the proof is honest: it genuinely rests on `feynmanU_heat_equation`
(the kernel identity `∂_t K = ½ ∂_xx K`) + the exact drift cancellation (`U_x` coeff
`−(r−σ²/2)−½σ²+r = 0`, `U_xx` coeff `−½σ²+½σ²=0`), with the DCT/uniform-domination content living in the
already-proved `hasDerivAt_feynmanU_comp` — no smuggling.

**Findings applied** (2): dropped an unused `with hc₀`; docstring clarified that the hard
differentiability work is in `feynmanU_comp` and `feynmanU_heat_equation` is only the algebraic kernel
identity. **Declined**: (a) the reviewer's "`hSne` is dead" — false, it is used by the final `field_simp`
to clear the `S`-powers (kept); (b) the reviewer's idiom suggestion `simp only []`→`dsimp only` —
*tried and reverted*: `dsimp only` does **not** beta-reduce the `feynmanU_heat_equation` `h z`-redex here
(it broke the build), so `simp only []` is the correct tactic. **Deferred**: the ~10-line copy-paste
between `integrable_payoff_mul_d{t,x}K` (a future unified skeleton); and **benchmark wiring** — the public
keystone theorem is not yet cited by a corpus entry (the only substantive open item; adding one triggers
an axiom-audit regen + ledger, deferred at this budget) — flagged as the immediate follow-up.

**Verdict**: PASS — the four-step keystone (kernel heat equation → FK price representation → discounted
heat flow → PDE) is complete, sound, axiom-clean. lake build green, 19 pytest, ledger 269/269 fresh.

## 2026-06-08 (round 3) — ∂_τ landed (Theta via Feynman–Kac) — corpus 269

**Scope**: the Black–Scholes `τ`-derivative via Feynman–Kac — the result that defeated several prior
attempts (the uniform domination kept hitting Lean's 200k-heartbeat `nlinarith`/`whnf` wall). The
four-step tower (all green): `hasFDerivAt_heatKernel` (heat kernel jointly Fréchet-differentiable) →
`hasDerivAt_heatKernel_comp` (curve chain rule) → `hasDerivAt_feynmanU_comp` (∂_τ of the FK function) →
`hasDerivAt_bsV_tau_fk` (the price's Theta). The breakthrough: **(1)** isolate the polynomial bracket
bounds (`curve_sq_ratio_le` / `curve_abs_ratio_le`) as standalone lemmas with the moving denominator
replaced by the constant `v₀` — in isolation `nlinarith` elaborates (the inline failure was the
`whnf`/`isDefEq` blow-up on a single mega-constant, not the math); **(2)** dominate by a **sum of two
Gaussian-moment envelopes** (one per kernel-derivative term), never a single mega-constant.

**Panel**: one adversarial reviewer (try-to-refute "net improvement"), synthesised with Opus judgment.

**Findings applied** (2): (a) **[blocking]** the `PDEFromFeynmanKac` module docstring still declared the
`τ`-derivative "deferred … the same nlinarith/heartbeat wall" — now false (`hasDerivAt_bsV_tau_fk` is
proved); rewritten to the honest status (Theta landed, only the step-4 PDE assembly remains); (b)
[minor slop] an unreduced beta-redex `(fun ξ => …) z` in `bsV_tau_fk`'s stated value → `max (e^z−K) 0`.

**Findings accepted / declined**: `hasDerivAt_bsV_tau_fk` is private with no consumer yet — accepted as
an in-progress Greek awaiting the step-4 PDE assembly, exactly as the already-committed
`hasDerivAt_bsV_S_fk` (Delta) was; the `sc-thm-9.2.1` benchmark scope-note overclaim ("~300–500 lines
upstream") is now mildly stale but left untouched (editing a benchmark re-stales the ledger + forces an
axiom-audit regen for a narrative note; flagged for a future benchmark pass). All other lenses PASS
(inspired math, idiomatic register, Mathlib coherence, elegance, concept clarity, architectural
ingenuity — the one genuinely-2D ingredient `hasFDerivAt_heatKernel` makes a single chain rule available).

**Verdict**: PASS. `feynmanU` is now load-bearing for the Black–Scholes time-derivative; the C¹ tower is
fully consumed. Lean: `lake build` green (no MathFin errors), 19 pytest, ledger 269/269 fresh,
axiom-clean. Remaining for the full keystone: `∂_SS` via FK + the PDE-operator assembly (step 4).

## 2026-06-08 (round 2) — parametric unification — corpus 269

**Scope**: the parametric unification of the heat-kernel differentiate-under-the-integral lemmas in
`Foundations/FeynmanKacHeatEquation` — new skeleton `hasDerivAt_integral_mul_kernelFamily` + extracted
`heatKernel_temporal_le` / `sq_sub_div_le` / `integrable_payoff_mul_heatKernel`, with `hasDerivAt_phi`
and `hasDerivAt_feynmanU_{t,x,xx}` refactored to route through it (net ≈ −55 lines); the
`exp_mul_heatKernel` docstring made honest. The timed-out ∂_τ tower (the heat kernel's joint Fréchet
derivative + its curve derivative + `feynmanU_comp`) was *validated* but **removed**: its uniform
domination hits the 200k-heartbeat wall — the same obstacle as the earlier brute force — so it was kept
zero-orphan rather than shipped behind a `maxHeartbeats` discharge (which would itself be slop).

**Panel**: three reviewers — (1) zero-slop / idiomatic register / Mathlib coherence; (2) elegance /
concept clarity / architecture; (3) adversarial abstraction audit (try to refute "net improvement").
**No blocking findings — all three judged it a net improvement.**

**Findings applied** (3): (a) stale cross-ref in `heatKernel_shift_le` (`hasDerivAt_phi` →
`heatKernel_temporal_le`); (b) `integrable_payoff_mul_heatKernel` docstring overclaim ("every
diff-under-integral lemma" → the `_t`/`_x` lemmas, since `_phi` uses the Gaussian-integrability route
and `_xx` a first-derivative integrand); (c) **[adversarial, deepest]** the temporal polynomial-ratio
bound `|w²−s|/(2s²) ≤ 2(w²+3t/2)/t²` was still duplicated verbatim (modulo `y` vs `z−x`) between
`hasDerivAt_phi` and `_t` — extracted as the private `sq_sub_div_le`, so the shared estimate is now
named and the per-lemma dominations are genuinely distinct (making the skeleton docstring's claim true).

**Findings declined** (with reason): "remove the named `hs_pos`" — load-bearing via `positivity`'s
context search, removing it breaks the build; param-lemma arg reorder + skeleton rename — subjective
idiom not worth touching four green call sites; restore "Cameron–Martin" to the `exp_mul_heatKernel`
title — honesty wins (it is the completing-the-square real-analysis identity, *not* the measure change;
the Cameron–Martin/Girsanov connection stays in the body); `_xx`'s interleaved `?_` argument
ergonomics — an honest, accepted cost (its base point is a first-derivative integrand, not a raw
kernel product, so it cannot use `integrable_payoff_mul_heatKernel`).

**Verdict**: PASS. The unification is elegant, fully consumed (4 callers + shared helpers), and reduces
duplication without hiding the genuinely-distinct dominations. Lean: `lake build` green (no MathFin
errors), 19 pytest pass, ledger 269/269 fresh, axiom-clean.

## 2026-06-08 — commit 3beb170 — corpus 269

**Scope**: the Feynman–Kac → BS-PDE *keystone core* — step 1 (kernel-side heat equation
`∂_t U = ½ ∂_xx U` for sub-Gaussian payoffs, in `Foundations/FeynmanKacHeatEquation`: the
completing-the-square mean-shift, the sub-Gaussian envelope, the spatial kernel bound, three
diff-under-integral derivatives, the `feynmanU_heat_equation` identity) + the bridge
`bsV_eq_discount_feynmanU` (bsV = discounted heat flow, making `feynmanU` load-bearing for pricing)
and Delta-via-FK `hasDerivAt_bsV_S_fk` (in `BlackScholes/PDEFromFeynmanKac`). The full `∂_τ`/PDE
assembly is deferred (its brute-force domination is infeasible — see below).
**Panel**: three Sonnet reviewers (coherence+idiomatic · zero-slop+architecture ·
inspired-math+first-principles+clarity+beauty) reading the diff, + Opus synthesis and judgment.

| lens | verdict |
|---|---|
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS-WITH-NOTES |
| zero slop | PASS-WITH-NOTES |
| architectural ingenuity | PASS-WITH-NOTES |
| first principles | PASS |
| idiomatic register | PASS-WITH-NOTES |
| concept clarity | PASS-WITH-NOTES |
| beautiful, elegant math | PASS-WITH-NOTES |

**Blocking finding (fixed in this commit's follow-up)**: `PDEFromFeynmanKac` carried ~112 lines of
orphaned, never-consumed `∂_τ` domination scaffolding (`hasDerivAt_kernelCurve`, `heatKernel_curve_le`,
`integrable_tau_bound`) — machinery for a brute-force differentiate-under-the-integral that
heartbeat-times-out and is being abandoned for a leaner route. Removed (recoverable from `3beb170`);
the file now holds only the FK representation, the bridge, and the FK-Delta, with an honest module
docstring.

**Recorded actions (deferred to the next FK round, batched to avoid re-staling the ledger)**:
1. *(top priority — leaner + elegant + architecture; all three panels)* `hasDerivAt_phi`,
   `hasDerivAt_feynmanU_t/_x/_xx` are the same dominated-convergence proof at different parameters;
   unify into ONE parametric `hasDerivAt_feynmanU_param` (≈200 → ≈100 lines).
2. failing 1, extract the verbatim-duplicated `heatKernel_temporal_le`, polynomial-bound, and
   `hFt_int` blocks as shared private helpers (≈35 lines).
3. *(concept clarity)* `exp_mul_heatKernel` docstring over-claims "Cameron–Martin mean shift" — it is
   the completing-the-square identity (the *analytic core* of the shift, not the measure-change
   theorem); retitle honestly.
4. *(idiomatic)* `open Real` is declared but `Real.` is qualified ~200×; drop it.
5. *(architecture)* `callPayoff_continuous`/`le_exp` are call-payoff facts → `BlackScholes/Call.lean`.
6. *(zero slop)* `hasDerivAt_feynmanU_xx`'s closing `linarith [show … ring]` should mirror `_x`'s
   clean `calc … ring`.

**Declined (Sonnet suggestions overruled on the math)**:
- "compose `hasDerivAt_kernelCurve` from the `∂_t` + `∂_y` partials" — wrong: the curve moves both
  kernel arguments, so total = sum-of-partials ONLY under joint differentiability, which the
  partial-`HasDerivAt`s do not provide; the from-scratch differentiation of the explicit kernel is
  the correct route.
- "`heatKernel_shift_le` without variance-widening (same-`t` bound)" — false: `K(t,z−x)/K(t,z−x₀)`
  is unbounded in `z`; widening to `2t` is essential for the domination.

**Verdict**: the keystone core is sound, honest, and largely elegant — the inspired ideas
(kernel-side differentiation, the mean-shift, the heat-equation collapse) are present and correct.
The first-try slop (the duplicated diff-under-integral template; the brute-force `∂_τ` scaffolding) is
the natural debris of a large climb: the scaffolding is removed here, the duplication is scheduled for
a parametric pass.

## 2026-06-07 — commit 321eb4f — corpus 269

**Scope**: commit `321eb4f` — `bsV_eq_feynmanU` (the Feynman–Kac representation of
the Black–Scholes call price) in the new bridge module
`MathFin/BlackScholes/PDEFromFeynmanKac.lean`, plus its umbrella import. This is
step 2 of the Feynman–Kac → BS PDE keystone (which makes the previously
consumer-less `Foundations.FeynmanKacHeatEquation.feynmanU` load-bearing for
pricing); steps 1 (kernel-side heat equation), 3 (change of variables) and 4
(assembly) remain in progress.
**Panel**: three Sonnet agents on the mechanical lenses — (coherence + idiomatic
register), (zero slop + dead-code/forbidden-text), (architecture + first-principles
+ docstring fidelity) — and Opus on the judgment lenses (inspired math, first
principles, concept clarity, beauty).

| lens | verdict |
|---|---|
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS-WITH-NOTES |
| zero slop | PASS |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS (after the fix below) |
| beautiful, elegant math | PASS |

**Blocking findings**: one, fixed before this verdict. The theorem docstring's
"Proof chain" described a *two-step* route (`feynmanU_eq_integral_of_map` with
`B = id` over `gaussianReal 0 (σ²τ)`, then a **separate** `integral_map` rescale)
that was never written: the actual proof is a *single* `feynmanU_eq_integral_of_map`
with `B = (σ√τ · ·)` over the standard normal, the variance rescale discharged as
its hypothesis `hmap`. The docstring — the concept-clarity instrument — was
rewritten to describe the one-step proof that exists.

**Checks that mattered**: all four hypotheses are consumed (`hS` via
`Real.exp_log` and the `BSCallHyp` constructor; `hK`/`hσ` via `BSCallHyp`; `hτ`
via `Real.sq_sqrt` and `BSCallHyp`) — no dead binders; forbidden-text scan clean
(no `sorry`/`native_decide`/`?`-tactics/etc.); the statement is a genuine identity,
not a disguised `rfl` (the closed-form `bsV` and the integral `feynmanU` are
definitionally distinct) and not vacuous; it consumes the canonical upstream API
(`gaussianReal_map_const_mul`, `feynmanU_eq_integral_of_map`, `bs_call_formula`,
`HasLaw.id`) with no thin wrappers or re-derivations; the NNReal-coercion block and
the two `neg_mul` reconciliations are load-bearing glue, not slop; correct
file/layer (a `BlackScholes/` bridge over the Foundations FK layer) at the right
generality (the concrete call payoff baked in, not over-abstracted).

**Declined reviewer flags** (with reason):
1. *(minor)* "redundant `public import MathFin.BlackScholes.Call`" — declined: this
   file directly consumes `bs_call_formula`/`bsTerminal`/`BSCallHyp`, so the
   explicit import is correct direct-dependency hygiene; the file's transitive-import
   comment scopes only the Mathlib base, not directly-used modules.
2. *(minor)* "`NNReal.coe_mk` is deprecated" — declined: the pinned-Mathlib build is
   warning-clean, so this is the documented public-Mathlib-newer-than-pin artifact
   (the same class as the `abs_sub` false positive in the `14ca008` review).
3. *(nit)* "'until now consumed by nothing' is stale" — declined: "until now
   consumed by nothing, becomes load-bearing" is self-consistent and correct.

**Recorded actions**:
1. *(minor, out of scope — future cleanup)* the exp-sign convention mismatch
   between `Call.lean` (`Real.exp (-r * T)`) and `PDE.lean` (`Real.exp (-(r * τ))`)
   forces two cosmetic `neg_mul` reconciliations in this file; unify the convention
   in a pass over the lower BS modules.

## 2026-06-07 — commit 14ca008 — corpus 269

**Scope**: commit `14ca008` — Summit A′ (the time-dependent Itô formula:
three new Foundations modules + the process-weight generalization of
`WeightedQuadraticVariation`), the Kelly n-period iid model re-promotion,
and the wiring (`sc-thm-7.1.2` + `mf-kelly-n-periods-linearity` → `full`,
AxiomAudit Summit A′ section, blueprint spine node, docs).
**Panel**: three agents — (coherence + idiomatic), (slop + first principles
+ architecture), (clarity + inspired math + beauty).

| lens | verdict |
|---|---|
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS-WITH-NOTES |
| zero slop | PASS-WITH-NOTES |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS-WITH-NOTES |
| concept clarity | PASS-WITH-NOTES |
| beautiful, elegant math | PASS |

**Blocking findings**: none.

**Checks that mattered**: the boundary-cancellation algebra of the named-limit
core was verified symbolically — the discrete 2D identity makes the unbounded
`f(T,B_T) − f(0,B₀)` cancel, so "the L² estimate only ever sees three
vanishing terms" is literally true, not prose; the Kelly repair is genuine
first principles (`integral_log_kellyReturnMeasure` *computes* the two-point
integral, `kellyGrowth_n_periods` is real linearity of expectation over
`Measure.pi` — no step is `rfl`); a dead-hypothesis sweep over every new
public theorem found every binder consumed (including both joint-continuity
hypotheses of the CLM theorem); every `nlinarith` carries certificate hints
(the `(u+v+w)² ≤ 3(u²+v²+w²)` step via the three cross-difference squares);
no Mathlib lemma yields joint continuity from bounded one-variable partials,
so the corner-split Lipschitz route of `continuous_uncurry_of_bdd_partials`
is canonical, and `tendsto_riemann_L2_process` duplicates no Mathlib
Riemann-DCT result (bespoke `NNReal` `timeMeasure`); the `sc-thm-7.1.2`
snippet matches `ito_formula_td_L2_bddDeriv` hypothesis-for-hypothesis, and
the unbounded-coefficient gap is named everywhere it matters.

**Fixed before this verdict** (triaged minor, fixed in `14ca008`):
1. `integral_increment_sq` duplication — the TDRemainder copy re-derived
   `ItoIsometryAdapted.integral_increment_sq` at the bare `MathFin` namespace
   (a latent ambiguity trap since `ItoFormulaTD` opens that namespace);
   deleted, the call site consumes the existing lemma, the genuinely-new
   `integrable_increment_sq` companion stays.
2. Three dead nonneg `have`s in `tendsto_ito_remainder_td` left by the
   memLp hoist (self-caught pre-panel, confirmed by the panel's sweep).
3. `tendsto_riemann_continuous` had been widened to public with a docstring
   claiming the Itô layers consume it — they consume the L² wrappers;
   reverted to `private` with the honest description.
4. `docs/blueprint.md` BS-PDE section still called `sc-thm-7.1.2` "still
   `reduced_core`"; rewritten to the bounded-regime status (the deferral
   argument stands: the BS value function's Γ is unbounded as `S → 0`).
5. Kelly horizon-binder drift (`T : ℕ` vs the file's new `n : ℕ` register)
   in `kelly_n_periods_deriv_at_kelly` + its benchmark snippet.

**Recorded actions**:
1. *(minor, DONE same day — consolidation follow-up commit)*
   increment-second-moment fact consolidated: `ItoIsometryAdapted` now
   imports `WienerIntegralL2` (acyclic) and `integral_increment_sq` /
   `integral_two_increment` are one-step instances of
   `covariance_increment_aux` (diagonal and shared-start), `hBmeas` dropped
   from both signatures as dead; module docstring's stale "(non-`module`)
   file" re-derivation apology rewritten. The `SimpleProcess`/`L2Predictable`
   unification remains the only deferred item of that paragraph.
2. *(minor, DONE same day — same commit)* the Term-II scaffolding hoist
   completed: private `measurable_pathIntegral` + `abs_pathIntegral_le` are
   the single home of the path-integral measurability/bound, consumed by
   `tendsto_riemann_L2_process`, the new per-`n` companion
   `integrable_riemann_defect_sq`, and `memLp_pathIntegral_process`;
   `tendsto_weighted_qv_process` lost its 19-line duplicate block.
3. *(nit, RESOLVED — no action at this pin)* `abs_sub` is **not** deprecated
   in the pinned Mathlib: it is the live `to_additive` companion of
   `theorem mabs_div` (`Algebra/Order/Group/Abs.lean:81`), and the bridges
   elaborate with zero deprecation warnings. The reviewer's claim was a
   newer-Mathlib artifact — the documented public-loogle-vs-pin caveat.
   Re-check at the next toolchain bump.
4. *(nit, accepted)* `coverage.md`'s "pre-re-audit historical record" line is
   deliberately stale provenance; the panel flagged it, the file already
   frames it as such — no action.
5. *(nit, DONE same day — same commit)* `PoissonCounting`'s two unused-`hr`
   warnings (pre-existing, surfaced by the consolidation rebuild) pruned as
   a dead-positivity cascade: three private Gamma-CDF calculus lemmas
   (`hasDerivAt_gamma_antideriv`, `integral_gammaPDFReal_sub_succ`,
   `integral_gammaPDFReal_one`) never needed `0 < r` — the telescoping
   antiderivative identities are formal algebra; public signatures
   untouched.

## 2026-06-06 — commit f1b0dcd — corpus 269

**Scope**: commits `9db04f8` (Merton dominance + classic display + Markov
path law), `aec693d` (values-gates round), `f1b0dcd` (HF publish CI) — four
new Lean modules, one bridge lemma, the enforcement tooling.
**Panel**: three agents — (coherence + idiomatic), (slop + first principles
+ architecture), (clarity + inspired math + prose honesty).

| lens | verdict |
|---|---|
| inspired math quality | PASS |
| Mathlib/BrownianMotion coherence | PASS |
| zero slop | PASS |
| architectural ingenuity | PASS |
| first principles | PASS |
| idiomatic register | PASS |
| concept clarity | PASS-WITH-NOTES |
| beautiful, elegant math | PASS |

**Blocking findings**: none.

**Checks that mattered**: `bsV_spot_tangent_le` duplicates no Mathlib
support-line lemma (it is the delta-substituted form, needing the
closed-form Greek); the Markov factorization is genuinely derived (base
case computes through `traj_map_frestrictLe` + `partialTraj_self` +
`piUnique`; inductive step through the comp-product marginal recursion —
no step smuggles the conclusion); `mertonCallTerm_eq_bsV`'s trivial proof
is a feature (it validates the definition is the BS value, and two modules
consume it); "jump risk is never free" is an exact gloss of the inequality
under its hypotheses; the classic display matches Merton (1976) eq. (16)
weights/rates/vols precisely; the converse direction of the Markov
characterization is nowhere claimed.

**Recorded actions**:
1. *(done in this commit)* corpus-iteration was triplicated across
   `axiom_audit_gen.py` / `hf_dataset.py` / `ledger.py` — extracted
   `tools/verify/corpus.py`; the two new tools now share it. `ledger.py`
   deliberately untouched (verified load-bearing hashing code) — fold into
   its next structural pass.
2. *(nit, open)* `MertonClassicDisplay.lean` docstring: "absorbs the jump
   factor" is terse about the mechanism (the rate-shift identity supplies
   it two paragraphs later); sharpen on next touch of the file.
3. *(nit, accepted)* the rfl-tripwire's tail regex is documented
   "good enough" in-file; a Lean-aware scanner is not worth its weight while
   the catch rate is this good (1 for 1 on first run).
