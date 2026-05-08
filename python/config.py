"""TOML configuration loader."""

from __future__ import annotations

import tomllib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class LeanRequireSpec:
    """A Lean dependency spec for `lean-interact`'s `TempRequireProject`."""

    name: str
    git: str
    rev: str | None = None


@dataclass
class LeanConfig:
    version: str = "v4.30.0-rc1"
    mathlib: bool = True
    # Optional commit pin for Mathlib. When set, lean-interact pulls Mathlib at
    # exactly this commit instead of resolving the string "mathlib" to whatever
    # master is at fetch time. Required when a vendored library (e.g. Degenne's
    # brownian-motion) was tested against a specific Mathlib snapshot and would
    # break against a newer master.
    mathlib_rev: str | None = None
    # Additional Lean dependencies beyond Mathlib. Each entry becomes a
    # `lean_interact.LeanRequire` and is appended to the `require` list of the
    # `TempRequireProject`. Use this for vendored libraries like
    # RemyDegenne/brownian-motion that are not in Mathlib master yet.
    extra_requires: list[LeanRequireSpec] = field(default_factory=list)

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> LeanConfig:
        raw = d.get("extra_requires", []) or []
        extras = [
            LeanRequireSpec(
                name=r["name"],
                git=r["git"],
                rev=r.get("rev"),
            )
            for r in raw
        ]
        return cls(
            version=d.get("version", cls.version),
            mathlib=d.get("mathlib", cls.mathlib),
            mathlib_rev=d.get("mathlib_rev"),
            extra_requires=extras,
        )


@dataclass
class IsabelleConfig:
    session: str = "HOL-Probability"
    # Optional secondary session (typically a HybridVerifyAFP heap that
    # bundles Ergodic_Theory / Markov_Models). Theorems can opt into it via
    # metadata.isabelle_session, or by importing an AFP-namespaced theory.
    afp_session: str | None = None
    use_connector: bool = True

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> IsabelleConfig:
        return cls(
            session=d.get("session", cls.session),
            afp_session=d.get("afp_session", cls.afp_session),
            use_connector=d.get("use_connector", cls.use_connector),
        )


@dataclass
class OrchestratorConfig:
    max_workers: int = 3
    default_timeout: float = 60.0

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> OrchestratorConfig:
        return cls(
            max_workers=d.get("max_workers", cls.max_workers),
            default_timeout=d.get("default_timeout", cls.default_timeout),
        )


@dataclass
class HybridVerifyConfig:
    lean: LeanConfig = field(default_factory=LeanConfig)
    isabelle: IsabelleConfig = field(default_factory=IsabelleConfig)
    orchestrator: OrchestratorConfig = field(default_factory=OrchestratorConfig)

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> HybridVerifyConfig:
        return cls(
            lean=LeanConfig.from_dict(d.get("lean", {})),
            isabelle=IsabelleConfig.from_dict(d.get("isabelle", {})),
            orchestrator=OrchestratorConfig.from_dict(d.get("orchestrator", {})),
        )


def load_config(path: str | Path | None = None) -> HybridVerifyConfig:
    """Load configuration from a TOML file.

    Falls back to defaults if no path is provided or file doesn't exist.
    """
    if path is None:
        # Check default locations
        for candidate in ["hybrid_verify.toml", "pyproject.toml"]:
            p = Path(candidate)
            if p.exists():
                path = p
                break

    if path is None:
        return HybridVerifyConfig()

    path = Path(path)
    if not path.exists():
        return HybridVerifyConfig()

    with open(path, "rb") as f:
        raw = tomllib.load(f)

    # Support both standalone toml and [tool.hybrid-verify] in pyproject.toml
    if "tool" in raw and "hybrid-verify" in raw["tool"]:
        data = raw["tool"]["hybrid-verify"]
    elif "hybrid-verify" in raw:
        data = raw["hybrid-verify"]
    else:
        data = raw

    return HybridVerifyConfig.from_dict(data)
