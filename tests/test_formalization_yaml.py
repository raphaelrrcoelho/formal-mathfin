"""Freshness + independence gate for the generated formalization.yaml
(mathlib-initiative v0.3 self-report).

1. ``test_formalization_yaml_is_fresh`` — the committed file is byte-identical
   to the generator's output (a generated artifact is never hand-edited;
   regeneration is a no-op). Mirrors ``test_axiom_audit_gen_is_fresh``.
2. ``test_generator_is_foundry_independent`` — the generator reads only
   main-repo sources; it imports nothing from the foundry and builds a complete
   document with no foundry present. The main repo self-reports on its own.
3. ``test_report_matches_corpus`` — the mechanical numbers (theorem count,
   axioms, sorry=0) track the live corpus.
"""

import os

from tools import formalization_yaml as F

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def test_formalization_yaml_is_fresh():
    generated = F.emit_yaml(F.build_doc(ROOT))
    path = os.path.join(ROOT, "formalization.yaml")
    assert os.path.isfile(path), "formalization.yaml missing — run --write"
    current = open(path, encoding="utf-8").read()
    assert current == generated, (
        "formalization.yaml is stale — run "
        "`python3 -m tools.formalization_yaml --write`")


def test_generator_is_foundry_independent():
    # the generator's own source imports nothing from the foundry
    src = open(os.path.join(ROOT, "tools", "formalization_yaml.py"), encoding="utf-8").read()
    assert "import foundry" not in src and "mathfin_foundry" not in src
    # and it builds a full document from main-repo data alone
    doc = F.build_doc(ROOT)
    assert doc["version"] == "v0.3"
    assert set(doc) >= {"project", "sources", "status", "automation",
                        "fidelity", "review", "alignment"}


def test_report_matches_corpus():
    doc = F.build_doc(ROOT)
    assert doc["status"]["axioms"] == ["propext", "Classical.choice", "Quot.sound"]
    assert doc["status"]["sorry_count"] == 0
    # theorem count = number of alignment rows' statements, and appears in scope
    total = sum(int(s["lean"].split()[0]) for s in doc["alignment"]["statements"])
    assert str(total) in doc["status"]["scope"]
    # automation honestly names the scout
    methods = doc["automation"]["methods"]
    assert any("labs-leanstral-1-5" in m.get("models", []) for m in methods)
