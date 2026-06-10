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
