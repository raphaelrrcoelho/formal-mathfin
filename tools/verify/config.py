"""TOML configuration loader."""

from __future__ import annotations

import tomllib
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


@dataclass
class LeanConfig:
    # Path to the in-repo Lake project that the Lean backend elaborates
    # against. The project's own ``lakefile.lean`` + ``lake-manifest.json`` +
    # ``lean-toolchain`` are authoritative for Mathlib/Lean versions and
    # transitive deps; benchmark snippets just `import QuantFin.X` and
    # reference compiled lemmas by name.
    #
    # Path is relative to the CWD when the verifier runs (in Docker that's
    # ``/app``, which is the repo root with ``lakefile.lean`` + ``QuantFin/``
    # directly under it).
    local_project: str = "."

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> LeanConfig:
        return cls(local_project=d.get("local_project", cls.local_project))


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
class QuantFinConfig:
    lean: LeanConfig = field(default_factory=LeanConfig)
    orchestrator: OrchestratorConfig = field(default_factory=OrchestratorConfig)

    @classmethod
    def from_dict(cls, d: dict[str, Any]) -> QuantFinConfig:
        return cls(
            lean=LeanConfig.from_dict(d.get("lean", {})),
            orchestrator=OrchestratorConfig.from_dict(d.get("orchestrator", {})),
        )


def load_config(path: str | Path | None = None) -> QuantFinConfig:
    """Load configuration from a TOML file.

    Falls back to defaults if no path is provided or file doesn't exist.
    """
    if path is None:
        for candidate in ["quantfin.toml", "pyproject.toml"]:
            p = Path(candidate)
            if p.exists():
                path = p
                break

    if path is None:
        return QuantFinConfig()

    path = Path(path)
    if not path.exists():
        return QuantFinConfig()

    with open(path, "rb") as f:
        raw = tomllib.load(f)

    if "tool" in raw and "quantfin" in raw["tool"]:
        data = raw["tool"]["quantfin"]
    elif "quantfin" in raw:
        data = raw["quantfin"]
    else:
        data = raw

    return QuantFinConfig.from_dict(data)
