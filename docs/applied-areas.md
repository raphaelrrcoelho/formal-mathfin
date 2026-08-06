# Applied-areas scouting — where a sibling library has room

**Date:** 2026-08-06 · **Status:** scoping study, no Lean written · **Mathlib pin audited:**
`81a5d257c8e410db227a6665ed08f64fea08e997` (2026-07-13), the exact rev in
`lake-manifest.json`.

The question this answers: *is there space to replicate what `formal-mathfin` did
for another applied field — a "formal-mathecon", econometrics, or similar?*

**Verdict.** Yes, but not where the name suggests. The obvious economics targets
were claimed between April and July 2026 by two funded groups. The open ground is
**econometric identification** and **time-series econometrics**, with **recursive
macro dynamics** as a strong second. General equilibrium is open but gated behind a
missing Mathlib prerequisite that makes it a much larger bet than it looks.

The reasoning below is in three parts: who already holds what (§1), what Mathlib
can actually carry today (§2 — the original work here, a grep audit at our exact
pin), and the resulting ranked territories with a pillar/bridge architecture (§3–§5).

---

## 1. The competitive map

| Territory | Holder | State as of 2026-08 |
|---|---|---|
| Game theory · mechanism design · social choice · matching · fair division | Two independent projects both named **EconCSLib** — [Bei–Ma–Jing–Fu–Tang, arXiv:2606.16144](https://arxiv.org/abs/2606.16144) (40k lines, 1300+ theorems, no extra axioms) and [Garg, arXiv:2606.13306](https://github.com/nikhgarg/EconCSLib) (20 formalized papers + 4 partial) | **Closed.** Nash, VCG, Myerson, Shapley, Arrow, Zermelo all done |
| Asymptotic statistics (the math layer under econometric *theory*) | [junwei-lu/Lean-Asymptotic-Statistical-Theory](https://github.com/junwei-lu/Lean-Asymptotic-Statistical-Theory) — van der Vaart 1998: LAN, Hájek–Le Cam convolution, Donsker, semiparametric efficient influence functions. Plus [StatLib](https://stat-lib.github.io/), [StatsMLlib](https://statsmllib.github.io/), [lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) (ICML 2026) | **Closing fast** — four libraries inside twelve months |
| Decision theory | vNM ([2506.07066](https://arxiv.org/pdf/2506.07066)), Wakker–Debreu–Koopmans ([2606.08902](https://arxiv.org/pdf/2606.08902)), stochastic dominance ([2505.12840](https://arxiv.org/pdf/2505.12840), [2507.07052](https://arxiv.org/pdf/2507.07052)) | Scattered single-paper drops, **no library**; Mathlib itself now carries `Probability/Decision/` |
| Fixed points → Nash | [Scarf, Brouwer, Nash in Lean](https://arxiv.org/pdf/2607.05987) | Done (and see §2 — they had to build Brouwer themselves) |
| Causal inference | Causalean (do-calculus + potential outcomes), [cubical d-separation](https://arxiv.org/pdf/2606.20351), CausalLib.agda, CausalForge | **Early, fragmented across four proof assistants** |
| Auctions · Arrow/Gibbard–Satterthwaite · binomial pricing | Isabelle/AFP — [Nipkow](https://isabelle.in.tum.de/~nipkow/pubs/arrow.pdf), Kerber–Lange–Rowat, Echenim | Legacy, not Lean |

Two things follow. First, "formal-mathecon" as a broad banner would collide head-on
with EconCSLib on its home turf, where we would lose on volume. Second — and this is
the opening — **every one of these projects is on the *theory* side. Nobody is
formalizing what applied econometrics actually argues about.**

---

## 2. Mathlib substrate audit at our pin

Grepped against a shallow checkout of `81a5d257c8` — declaration-level, not
vibes. This is the table that decides what is buildable in year one.

### Present, load-bearing

| Result | Where |
|---|---|
| **Central limit theorem** (iid real, `charFun` route) | `Probability/CentralLimitTheorem.lean` — `tendstoInDistribution_inv_sqrt_mul_sum` |
| **Strong law of large numbers** (Banach-valued) | `Probability/StrongLaw.lean` — `strong_law_ae` |
| **Conditional expectation as L² projection** | `MeasureTheory/Function/ConditionalExpectation/` — `condExpL2`, `MemLp.condExpL2_ae_eq_condExp'` |
| **Covariance as a continuous bilinear form** | `Probability/Moments/CovarianceBilin.lean`, `CovarianceBilinDual.lean` |
| **Martingale theory** — convergence, optional stopping/sampling, Doob, upcrossings | `Probability/Martingale/` |
| **Markov kernels** — invariance, φ-irreducibility, Ionescu–Tulcea, disintegration | `Probability/Kernel/` (`Invariance.lean`, `Irreducible.lean`) |
| **Statistical decision theory** — `avgRisk`, `bayesRisk`, `minimaxRisk`, data-processing inequality | `Probability/Decision/Risk/` |
| **Geometric Hahn–Banach** (full separation suite, incl. compact/closed) | `Analysis/LocallyConvex/Separation.lean` |
| **Krein–Milman**, extreme/exposed points | `Analysis/Convex/KreinMilman.lean` |
| **Banach contraction mapping** | `Topology/MetricSpace/Contracting.lean` — `ContractingWith` |
| **von Neumann *mean* ergodic theorem** (L², Hilbert) | `Analysis/InnerProductSpace/MeanErgodic.lean` — `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` |
| Birkhoff sum/average infrastructure, `Ergodic`/`PreErgodic`/`QuasiErgodic` | `Dynamics/BirkhoffSum/`, `Dynamics/Ergodic/` |

### Absent — verified, not assumed

| Missing | Consequence |
|---|---|
| **Brouwer fixed point.** Grep for `brouwer` returns only *Brouwer algebras* (Heyting/co-Heyting). No no-retraction theorem, no simplex retraction. The only fixed-point theorems in the library are Banach contraction and the 1-D IVT (`exists_mem_Icc_isFixedPt_of_mapsTo`). | **Gates all of general equilibrium.** Arrow–Debreu existence is not a year-one target |
| **Kakutani** (correspondence-valued), **Schauder** | Same gate; Kakutani is what GE existence actually needs |
| **Pointwise (Birkhoff) ergodic theorem** — only the *mean* L² version exists | a.s. ergodic LLN unavailable; see §3.2 for why this is survivable and even clarifying |
| **Donsker / functional CLT / empirical processes** | Unit-root asymptotics (Dickey–Fuller limits) out of reach without building it |
| **Mixing conditions** (α/β/φ-mixing), CLT for dependent data | Must be built for time series |
| **Least squares / normal equations / regression** — zero hits repo-wide | OLS algebra is greenfield (but easy: `condExpL2` + orthogonal projection do the work) |
| **Herglotz / spectral representation of a stationary process** | Spectral time series must be built on `fourierIntegral` |
| **Any economic vocabulary at all** — no preference relation, utility representation, Debreu, Walras | Definitional layer is entirely ours to design |

### The two findings that reorder everything

**(a) No Brouwer means GE is a two-year project, not a one-year one.** Arrow–Debreu
existence, the second welfare theorem's converse direction, Sonnenschein–Mantel–Debreu
— all sit behind Kakutani, which sits behind Brouwer, which does not exist. The
Scarf→Brouwer→Nash paper confirms the cost is real: building that route *was* their
paper. Anyone entering GE pays that toll first. **Demote GE.**

**(b) The missing pointwise ergodic theorem is a feature, not a bug — it picks the
spine for us.** Classical time-series econometrics is built on *covariance*
stationarity and mean-square convergence, not on almost-sure ergodicity. And the
von Neumann mean ergodic theorem in `MeanErgodic.lean` is *exactly* the L² statement
needed: the ergodic LLN for a covariance-stationary process is the Birkhoff average
of the shift operator on `L²` converging to the projection onto the invariant
subspace. **The one theorem Mathlib does have is the one the field actually uses.**
That is a genuine architectural gift — the L² route is both available and the
conceptually right one, and it is the same Hilbert-space projection machinery
already load-bearing in `Foundations/ItoIntegralL2`.

Critically, **the identification territory (§3.1) needs no fixed-point theory
whatsoever.** It is conditional expectation, orthogonal projection, and linear
algebra — every piece of which Mathlib has today.

---

## 3. The open territories, ranked

### 3.1 Econometric **identification** — rank 1

Not estimation, not asymptotics: *identification*. The question of whether a
parameter is pinned down by the observable distribution at all, before any sample
exists. This is where informal econometrics is at its sloppiest and where a formal
treatment has the most obvious reason to exist. Nothing found in any proof assistant.

| Target | Mathlib readiness |
|---|---|
| Linear projection: existence/uniqueness, normal equations, orthogonality | **Ready** — `condExpL2`, orthogonal projection |
| Frisch–Waugh–Lovell (partialling out) | **Ready** — projection algebra |
| Omitted-variable bias formula | **Ready** |
| IV: exclusion + relevance ⇒ identification; Wald estimator; 2SLS as projection | **Ready** |
| LATE (Imbens–Angrist): independence + monotonicity + relevance ⇒ Wald ratio = LATE | **Ready** — needs a potential-outcomes definitional layer |
| GMM global identification from moment conditions | **Ready** |
| DiD: parallel trends ⇒ ATT identified | **Ready** |
| RDD: continuity of potential-outcome CEFs at the cutoff ⇒ sharp RD identifies the local ATE; fuzzy RD | **Ready** — continuity + limits |
| Panel: within-transformation annihilates the fixed effect; FE identification | **Ready** |
| Selection / control function (Heckman) | **Ready** |
| Partial identification: Manski bounds, sharp bounds under monotonicity | **Ready** |

Every row is buildable at the current pin. The intellectual work is the
*definitional layer* — potential outcomes, treatment assignment, the estimand
algebra — not the analysis.

### 3.2 Time-series econometrics — rank 2

| Target | Mathlib readiness |
|---|---|
| Covariance stationarity, autocovariance function | Definitional — greenfield |
| **Mean-square ergodic LLN** for covariance-stationary processes | **Ready via `MeanErgodic.lean`** — the keystone (see §2b) |
| Wold decomposition | Buildable — Hilbert projection onto the closed span of the past |
| ARMA causality/invertibility (roots outside the unit circle) | Buildable — power series / `Analysis` |
| Yule–Walker equations | **Ready** — projection |
| Herglotz / spectral representation | Must build on `fourierIntegral` — **medium cost** |
| Granger representation theorem (cointegration ⟺ ECM) | Buildable — linear algebra + Wold |
| Mixing conditions, CLT under dependence | **Must build** — high cost |
| Unit-root asymptotics (Dickey–Fuller) | **Blocked** on functional CLT — defer |

Note the natural connection to our own corpus: `benchmarks/markov_chains.json`
carries `mc-thm-1.4.32` (ergodic theorem for Markov chains), `mc-thm-1.4.25`
(stationary distribution uniqueness) and `mc-thm-1.4.40` (convergence to stationary
distribution) — all currently `reduced_core`. A time-series library needs exactly
those upgraded to `full`. **The investment is shared, not duplicated.**

### 3.3 Recursive macro dynamics (Stokey–Lucas–Prescott) — rank 3

Zero hits in any proof assistant. A genuine *theory* — one principle (contraction)
whose consequences are the models — which is precisely the architecture-first shape
that made `formal-mathfin` work.

| Target | Mathlib readiness |
|---|---|
| Bellman operator is a contraction; value function exists and is unique | **Ready** — `ContractingWith` |
| Blackwell's sufficient conditions (monotonicity + discounting) | **Ready** |
| Principle of optimality (SLP Thm 4.2–4.5) | **Ready** |
| Value-function concavity/monotonicity; policy correspondence | **Ready** — `Analysis/Convex` |
| Envelope theorem (Benveniste–Scheinkman) | **Ready** |
| Transversality sufficiency | **Ready** |
| Stochastic dynamic programming; invariant distribution existence | **Partly** — `Kernel.Invariant` present; existence needs work |
| Optimal growth / Ramsey; turnpike | **Ready** once the above land |
| Policy-function iteration convergence | **Ready** |

Cheapest substrate of the four — nearly everything reduces to a fixed point of a
contraction, which Mathlib has. Weakness: less overlap with our existing
`Foundations/`, so less reuse.

### 3.4 General equilibrium — rank 4, deferred

Arrow–Debreu existence, welfare theorems, Debreu–Scarf core convergence,
Sonnenschein–Mantel–Debreu. Open, important — and **gated behind building Brouwer
and Kakutani from scratch** (§2a). The second welfare theorem alone is reachable
today (it is separating-hyperplane, and `geometric_hahn_banach_compact_closed` is
right there), which makes it a good *flag-plant* entry. But the existence half is a
different order of investment.

If the Brouwer/Kakutani prerequisite is built, it should be built **as a Mathlib
upstream contribution**, not as library-local code — which is also the highest-value
version of that work.

---

## 4. Recommended architecture — `formal-econometrics`

Scope: identification + time series, with macro dynamics as declared phase 3.
Following the MathFin pattern — pillars are principles, and the bridges are where
the depth lives.

### Pillars

| Pillar | The principle | First modules |
|---|---|---|
| **I — Identification as projection** | an estimand is identified iff it is a functional of the observable distribution; the linear case *is* the L² projection | `Identification/LinearProjection`, `FWL`, `OmittedVariable` |
| **II — Exogeneity as conditional independence** | every design (IV, DiD, RDD, panel) is one conditional-independence restriction plus a continuity or monotonicity condition | `Identification/PotentialOutcomes`, `IV`, `LATE`, `DiD`, `RDD` |
| **III — Stationarity as an invariant subspace** | the shift operator on L²; ergodicity is the invariant subspace being trivial | `TimeSeries/Stationary`, `ErgodicLLN`, `Wold` |
| **IV — Dependence as a spectral object** | autocovariance and spectral density are one Fourier pair | `TimeSeries/Spectral`, `Herglotz`, `ARMA` |

### Bridges — each makes two pillars one theorem

| Bridge | Connects | Why it is the depth |
|---|---|---|
| **Wold = projection onto the past** | I ⟷ III | the same orthogonal projection that gives OLS gives the Wold innovation representation — one theorem, two fields |
| **Ergodic LLN ⇒ consistency under dependence** | III ⟷ I | the mean ergodic theorem is what licenses estimating a projection from one realization |
| **Granger representation** | III ⟷ IV | cointegration rank ⟺ ECM ⟺ spectral density singularity at frequency zero |
| **LATE = a Wald ratio = an IV projection** | II ⟷ I | monotonicity turns a causal object into a linear-projection object |
| **Bellman ⟷ invariant distribution** (phase 3) | macro ⟷ III | the policy function induces the Markov kernel whose invariant measure is the stationary equilibrium |

The first bridge is the one to prove early: it is a single Hilbert-space projection
argument that makes the identification pillar and the time-series pillar the same
mathematics. That is the "architecture is the artifact" claim in one theorem.

---

## 5. What transfers from `formal-mathfin`

**The apparatus, which is the real moat.** Not theorem count — we would lose that
race to EconCSLib's 40k lines. What transfers is the honesty machinery: per-entry
`formalization_status` (`full`/`library_wrapper`/`reduced_core`/`placeholder`), the
input-hash verification ledger, `#print axioms` pinning via `AxiomAudit`, the
blueprint spine, the values review on a CI-enforced cadence, the
no-`sorry`/no-`native_decide` gates. EconCSLib's faithfulness check is explicitly
LLM-as-judge; ours is a kernel invariant plus a declared-scope contract. **In a field
whose entire subject matter is "that empirical claim was overstated", an
honesty-first library is a defensible position a larger, looser library cannot
take.**

**The foundry.** `mathfin-foundry`'s pipeline (Claude specifies → Claude formalizes
agentically against lean-lsp → depth gate → triviality gate → kernel gates →
Leanstral proves → refinery → human-merged PR) is domain-agnostic. Retargeting is
swapping the pointer modules and the house doctrine. **Marginal cost of library two
is far below library one** — this is probably the single strongest argument for
doing it at all.

**Substrate modules.** `Foundations/ItoIntegralL2` (Hilbert projection machinery),
`ConvexSeparation` and `ConvexDuality` (Hahn–Banach applications — directly reusable
for the second welfare theorem), the conditional-expectation and martingale wrappers,
and the Markov-chain entries noted in §3.2.

**Not transferable:** the Itô tower, Girsanov, the Poisson layer, the pricing
modules. Roughly 60% of `MathFin/`'s 264 files and 55k lines are finance-specific.

---

## 6. Phase plan

- **Phase 0 (2 weeks) — probe, do not commit.** Stand up a bare Lake project, write
  the `PotentialOutcomes` definitional layer and *one* theorem end-to-end:
  parallel trends ⇒ ATT identified. This is the cheapest possible test of whether
  the definitional layer is idiomatic. If it comes out ugly, the whole territory is
  worth re-examining before more is spent.
- **Phase 1 (~3 months) — the identification spine.** Pillars I and II: linear
  projection, FWL, OVB, IV, LATE, DiD, RDD, panel FE. Every row in §3.1 marked
  Ready. Ship with ledger + axiom audit + coverage report from day one.
- **Phase 2 (~4 months) — the time-series spine.** Pillars III and IV, keystone
  first: mean-square ergodic LLN from `MeanErgodic.lean`, then Wold, then the
  Wold-as-projection bridge. Upgrade the three `reduced_core` Markov entries in
  `formal-mathfin` as shared work.
- **Phase 3 — macro dynamics**, or the Brouwer/Kakutani upstream contribution if GE
  becomes the priority instead. Decide on evidence from phases 1–2, not now.

## 7. Risks and kill criteria

1. **The window is months, not years.** Statistics went from empty to four libraries
   in twelve months. If identification is still empty in six months that is luck, not
   a moat. *Mitigation: phase 0 immediately; publish the scope claim early.*
2. **The definitional layer is the whole bet.** If potential outcomes/treatment
   assignment cannot be stated idiomatically over Mathlib's measure theory, phases 1–2
   inherit the ugliness. *Kill criterion: if phase 0's DiD theorem needs bespoke
   scaffolding rather than consuming `condExp` directly, stop and redesign.*
3. **Two libraries, one maintainer, one 10 GB box.** The memory doctrine in
   `CLAUDE.md` already binds one Lean process at a time. A second corpus does not get
   a second slot. *Mitigation: the foundry's remote-daemon flag; corpus-scale work on
   GitHub runners.*
4. **EconCSLib expansion.** They are LLM-assisted and moving fast; nothing stops them
   entering identification. *Mitigation: compete on the faithfulness contract, which
   is the thing their workflow structurally cannot match, not on volume.*

---

## Appendix — reproducing the audit

```bash
mkdir -p /tmp/mathlib-pin && cd /tmp/mathlib-pin && git init -q
git remote add origin https://github.com/leanprover-community/mathlib4
git fetch --depth 1 origin $(python3 -c "import json;print([p['rev'] for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])")
git checkout -q FETCH_HEAD
# then grep Mathlib/ at declaration level, e.g.
grep -rniw brouwer --include='*.lean' Mathlib/     # → only Brouwer *algebras*
```

Re-run after any Mathlib pin bump: §2's absent-list is the part that decays.
