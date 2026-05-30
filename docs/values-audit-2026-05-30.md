# Values audit — 2026-05-30

A full-repository audit against the project's quality bar — inspired math,
Mathlib/BrownianMotion coherence, zero slop, architectural ingenuity, first
principles, Mathlib idiom, concept clarity — run as a **13-lens reviewer
panel**: seven region reviewers (Itô construction; Itô consumers / QV /
Feynman–Kac; CRR→BS + daemon; Black-Scholes / Futures; finance-foundations;
applied modules; docs / JSON / honesty) plus six cross-cutting reviewers
(slop; Mathlib/Degenne idiom + coherence; first-principles; inspired-math /
triviality; architectural ingenuity; concept-clarity).

## Verdict

The library is **fundamentally sound, honest, idiomatic, genuinely
first-principles, architecturally near-optimal, and low-slop** — confirming
the prior (2026-05-26 / 2026-05-29) audits. No unsoundness; no
`sorry`/`admit`/`axiom`; no stray `#eval`/`#check`/`set_option` debug residue.
The Itô isometry is *independently computed* on both sides (not smuggled);
static Girsanov genuinely *derives* the EMM. The real deviations were bounded
and clustered, and are remediated below.

## Remediation

**A. Docs lagging the code** (the dominant cluster — the library was *more*
finished than its docs claimed):
- README headline counts corrected to the authoritative **204 full / 19
  library_wrapper / 28 reduced_core** (223 delivery-ready); the inflated
  `211 / 24 / 16` removed, and "what's not done" rewritten with the real
  per-area `reduced_core` split.
- The continuous `[0,T]` Itô-integral CLM (`itoIntegralCLM_T`, built and
  AxiomAudit-pinned) was presented as *unbuilt / future-work* in README,
  `blueprint.md` (DAG `:::gated` while the prose said `✅`), and `roadmap.md` —
  all corrected to DONE, leaving only the genuinely-open pathwise-Itô / Lévy /
  SDE layer (and the separate infinite-horizon variant) as the frontier.
- Five stale `Binomial/` docstrings called the now-proven
  `binomialPrice_call_tendsto_bs` "deferred / upstream-gated"; repointed.
- `ito-integral-clm-deferred.md` banner clarifies it tracks only the
  infinite-horizon variant. `coverage.md` trimmed 577→82 lines (pre-2026-05
  hybrid-era session logs moved to git history). `docs/README.md` gains the
  blueprint row.

**B. SymPy + Isabelle backends stripped entirely** (maintainer directive — the
project is Lean-only). Removed `sympy_verifier.py`; the `Backend.SYMPY` /
`Backend.ISABELLE` enum members and every branch (`confidence.py`'s
`annotate_cross_validation`, `orchestrator.py`'s SymPy registration + the
unused `ThreadPoolExecutor`, `coverage_report.py`'s counters); the SymPy
dependency (`requirements.txt`, `pyproject.toml`, the dead `max_workers`
plumbing); the 25 `code.isabelle` blocks, ~115 `cas_reference` / `isabelle_*`
metadata keys, and the dead-backend narrative in benchmark
`formalization_scope` values; and the SymPy/Isabelle sections of `CLAUDE.md` +
`AGENTS.md`. Added a no-non-lean-code / no-dropped-backend-residue guardrail to
`test_router.py` + `coverage_report.py`.

**C. Dead code + duplication.** Deleted the dead `ItoIntegralSimple.lean`
(112 lines, 0 consumers, self-admittedly superseded) + its umbrella import +
doc references; deleted the dead `tendsto_sq_nhds_within_ne` and a shadowed
duplicate `h_exp_id`; deduplicated the byte-for-byte-tripled standard-normal-PDF
derivative helper into one public `hasDerivAt_gaussianPDFReal_zero_one` in
`Bachelier.lean`.

**D. Phantom / overclaiming docstrings + catalogue rows.** Removed the
non-existent `triangleNoArb_inverse_consistency` and
`stockNumeraireMeasure_isProbabilityMeasure` docstring claims; fixed
`WienerIntegralL2`'s stale "extends `wiener_finset_isometry`" lineage; retitled
`VasicekSDE` ("closed-form solution" → "terminal-distribution form, stated not
derived") and fixed its citation of the deleted file; removed two phantom
`bridges.md` rows referencing never-committed files
(`CRRConvergenceTransfer.lean`, `DoobLpApplications.lean`).

**E. Benchmark honesty.** The Gaussian VaR/CVaR descriptions reframed from "the
axiom of coherent risk measures" to "the closed-form Gaussian VaR/CVaR
functional satisfies …" (the affine identities verify the axiom *for the closed
form*, not the general theorem).

## Found already-done

The "BM-under-use" gap (idiom reviewer) is already closed:
`Foundations/PricingFromBrownian.lean` provides 11 `…_via_brownian` corollaries
(call, put, parity, Bachelier, digitals, power, dividends, stock-numeraire, KMV,
Merton) routing the flagship prices through `BSCallHyp.of_isPreBrownian`. No new
corollaries were built.

## Adjudicated defensible (not changed)

The density-form Gaussian MGF (routing through Mathlib's `mgf_id_gaussianReal`
*adds* a measure-conversion hop — 3 reviewers concur); the L¹/L² quadratic-
variation split (distinct benchmark deliverables, not accidental duplication);
`MarkowitzNAsset`'s Finset-form variance; `PDEFromIto`'s `ring`-closed theorem
names (docstrings are exemplary and the 2026-05-29 review adjudicated "keep").

## Deferred (minor clarity/style nits)

A few `FixedIncome` docstring sibling-filename references, three "see also"
signpost pointers (`FTAP` / `Kelly` / `ItoIntegralL2`), a `natFiltration`
shadow rename, a `ProbabilityTheory.NNReal.…` namespace-path nit, the
density-form CRR→BS closed-form landing corollary, and 7 files' header-style
uniformity — all reviewer-rated nit, tracked for a follow-up.

## Verification

Full `lake build` green; `pytest tests/test_router.py`; the coverage-report
guardrail (Lean-only `code`, no dropped-backend residue, every theorem carries
a `formalization_status`).
