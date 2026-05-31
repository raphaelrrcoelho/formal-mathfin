import Lake
open Lake DSL

package MathFin where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Library `MathFin` lives at `MathFin/*.lean` (default srcDir = ".").
-- `globs := .andSubmodules` builds the umbrella `MathFin` *and every*
-- `MathFin.*` submodule, not just those reachable from the umbrella's
-- imports. This guarantees `lake build` compiles every file under
-- `MathFin/` — including leaf modules nothing imports, such as
-- `MathFin.AxiomAudit` (the build-enforced axioms-clean harness) and
-- `MathFin.Examples` (the curated tour). Without it, an unimported file
-- could rot silently.
@[default_target]
lean_lib MathFin where
  globs := #[.andSubmodules `MathFin]

-- Pinned to Degenne brownian-motion's lake-manifest commit (so all transitive
-- versions resolve consistently). Bump together with the BrownianMotion pin.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "c87cc975222146012dc1c942c109f2decf536045"

-- RemyDegenne/brownian-motion: Brownian motion construction, multivariate
-- Gaussian, Kolmogorov-Chentsov continuity, Doob's L^p inequality, stochastic
-- integral approximation. Pinned to a specific commit so toolchain bumps stay
-- deterministic. The repo-root lakefile.lean + lake-manifest.json +
-- lean-toolchain are authoritative (mathfin.toml just sets local_project = ".").
require BrownianMotion from git
  "https://github.com/RemyDegenne/brownian-motion.git" @
  "fa590b1a198cb464357c5b773c7451da941acb43"
