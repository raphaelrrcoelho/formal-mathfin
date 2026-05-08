# Faithful Formalization Audit Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Separate "the active prover code checks" from "the textbook theorem is faithfully formalized" so delivery claims are honest and mechanically reportable.

**Architecture:** Add a benchmark status schema under theorem metadata, update the coverage report to count formalization faithfulness, and add tests that prevent placeholders from being counted as full theorem coverage. Keep active Lean/Isabelle verification unchanged unless a placeholder is being removed or demoted.

**Tech Stack:** Python stdlib JSON/Counter, existing benchmark JSON files, pytest, existing Docker Lean/Isabelle verifier.

---

### Task 1: Status Schema and Tests

**Files:**
- Modify: `tests/test_router.py`

- [ ] **Step 1: Add allowed status checks**

Add tests requiring every theorem to declare `metadata.formalization_status` as one of:
`full`, `library_wrapper`, `reduced_core`, or `placeholder`.

- [ ] **Step 2: Add placeholder guard**

Add tests requiring obvious placeholder patterns in active code to be classified as `placeholder`, and requiring entries classified as `full` or `library_wrapper` not to contain those patterns.

- [ ] **Step 3: Run test to verify it fails before metadata is complete**

Run: `python3 -m pytest tests/test_router.py`

Expected before metadata migration: failure naming theorem entries without `formalization_status`.

### Task 2: Metadata Migration

**Files:**
- Modify: `benchmarks/*.json`

- [ ] **Step 1: Add conservative formalization statuses**

Bulk edit benchmark metadata:
- `library_wrapper`: code directly invokes a named Lean/Isabelle theorem matching the course theorem.
- `full`: code proves a faithful theorem statement without relying merely on `True`, `rfl`, or algebra-only reductions.
- `reduced_core`: code proves a genuine but narrower algebraic/probabilistic proof obligation.
- `placeholder`: code verifies but does not encode a meaningful theorem statement.

- [ ] **Step 2: Preserve existing CAS quarantine**

Do not move `metadata.cas_reference.sympy` back into active `code`.

### Task 3: Strict Coverage Report

**Files:**
- Modify: `python/coverage_report.py`

- [ ] **Step 1: Count faithfulness statuses**

Print totals for `full`, `library_wrapper`, `reduced_core`, and `placeholder` separately from active backend counts.

- [ ] **Step 2: Fail on missing or invalid status**

Return nonzero if any theorem lacks a valid status.

- [ ] **Step 3: Print delivery-safe headline**

Report `delivery_claim_ready = full + library_wrapper`, not total active prover entries.

### Task 4: Documentation

**Files:**
- Create: `FORMALIZATION_STATUS.md`
- Modify: `AGENTS.md`
- Modify: `CLAUDE.md`

- [ ] **Step 1: Document the status vocabulary**

Explain which statuses count toward a strong theorem-proof claim.

- [ ] **Step 2: Document current coverage and caveats**

State the current counts and the exact command to refresh them.

### Task 5: Verification

**Files:**
- Test: `tests/test_router.py`
- Runtime: `python/coverage_report.py`

- [ ] **Step 1: Run fast tests**

Run: `python3 -m pytest tests/test_router.py`

- [ ] **Step 2: Run coverage report**

Run: `python3 -m python.coverage_report`

- [ ] **Step 3: Run Docker verifier if active code changed**

Run: `docker compose -f docker/docker-compose.yml run --rm verify benchmarks/<changed>.json --config hybrid_verify.toml --timeout 120`

Expected: no partials or failures for changed active code.
