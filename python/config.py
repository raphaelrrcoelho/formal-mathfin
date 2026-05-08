"""TOML configuration loader."""

from __future__ import annotations

import tomllib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


@dataclass
class LeanConfig:
    version: str = "v4.18.0"
    mathlib: bool = True

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> LeanConfig:
        return cls(
            version=d.get("version", cls.version),
            mathlib=d.get("mathlib", cls.mathlib),
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
