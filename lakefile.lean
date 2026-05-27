import Lake
open Lake DSL

package QuantFin where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Library `QuantFin` lives at `QuantFin/*.lean` (default srcDir = ".").
-- `globs := .andSubmodules` builds the umbrella `QuantFin` *and every*
-- `QuantFin.*` submodule, not just those reachable from the umbrella's
-- imports. This guarantees `lake build` compiles every file under
-- `QuantFin/` — including leaf modules nothing imports, such as
-- `QuantFin.AxiomAudit` (the build-enforced axioms-clean harness) and
-- `QuantFin.Examples` (the curated tour). Without it, an unimported file
-- could rot silently.
@[default_target]
lean_lib QuantFin where
  globs := #[.andSubmodules `QuantFin]

-- Pinned to Degenne brownian-motion's lake-manifest commit (so all transitive
-- versions resolve consistently). Bump together with the BrownianMotion pin.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "c87cc975222146012dc1c942c109f2decf536045"

-- RemyDegenne/brownian-motion: Brownian motion construction, multivariate
-- Gaussian, Kolmogorov-Chentsov continuity, Doob's L^p inequality, stochastic
-- integral approximation. Pinned to a specific commit so toolchain bumps stay
-- deterministic. The repo-root lakefile.lean + lake-manifest.json +
-- lean-toolchain are authoritative (quantfin.toml just sets local_project = ".").
require BrownianMotion from git
  "https://github.com/RemyDegenne/brownian-motion.git" @
  "fa590b1a198cb464357c5b773c7451da941acb43"
