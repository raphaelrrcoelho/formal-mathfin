## Summary

<!-- One paragraph: what theorem / doc / tooling change does this add, and why. -->

## Checklist

### For Lean proof contributions

- [ ] Proof lives in `MathFin/<Section>/<Module>.lean`, not inlined in JSON (unless it's a single-line library wrapper).
- [ ] `@[expose] public section` present in the module after the docstring.
- [ ] `#print axioms <myTheorem>` shows only `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
- [ ] `lake build` exits cleanly.
- [ ] `./scripts/lean-check.sh MathFin/<Section>/<Module>.lean` returns `"success": true`.
- [ ] Benchmark re-export shim added (or updated) in `benchmarks/*.json`.
- [ ] `metadata.formalization_status` set to `full` / `library_wrapper` / `reduced_core` (never `placeholder` to merge).
- [ ] `docs/coverage.md` row added / updated.
- [ ] `python3 -m tools.verify.axiom_audit_gen --write` re-run (regenerates `MathFin/AxiomAuditGen.lean`).
- [ ] `python3 -m tools.verify.ledger status` exits 0 (all entries fresh).
- [ ] `docker compose -f docker/docker-compose.yml run --rm --entrypoint python3 verify -m pytest tests/ -q` passes.

### For documentation contributions

- [ ] No dead relative links introduced.
- [ ] File referenced from `docs/README.md` or the appropriate index if it is new.

### For Python tooling contributions

- [ ] Host-side, Python stdlib only (no new deps unless discussed).
- [ ] `pytest tests/` passes.

## Related issues

Closes #
