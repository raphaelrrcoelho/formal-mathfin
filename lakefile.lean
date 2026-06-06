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

-- Blueprint JSON emitter with *inferred* dependency edges (LeanArchitect's
-- own `--json` path omits them; see MathFin/Blueprint/Export.lean). Used by
-- `tools/blueprint_render.py` to regenerate the docs/blueprint.md spine.
lean_exe blueprint_export where
  root := `MathFin.Blueprint.Export
  supportInterpreter := true

-- hanwenzhu/LeanArchitect: blueprint extraction directly from Lean source.
-- `@[blueprint]`-annotated (or post-hoc `attribute [blueprint]`-tagged)
-- declarations are exported with auto-inferred dependency edges via the
-- `blueprintJson` lake facet; `docs/blueprint.md`'s graph is GENERATED from
-- that JSON (no hand-maintained DAG). Tag tracks our exact toolchain; its
-- own deps are batteries + Cli only. Declared BEFORE mathlib: Lake gives
-- later requires precedence on transitive conflicts, so mathlib-last keeps
-- batteries/Cli at *Mathlib's* pinned revs (LeanArchitect builds against
-- them; a batteries drift would invalidate the entire baked Mathlib build).
require LeanArchitect from git
  "https://github.com/hanwenzhu/LeanArchitect.git" @
  "v4.30.0-rc2"

-- RemyDegenne/brownian-motion: Brownian motion construction, multivariate
-- Gaussian, Kolmogorov-Chentsov continuity, Doob's L^p inequality, stochastic
-- integral approximation. Pinned to a specific commit so toolchain bumps stay
-- deterministic. The repo-root lakefile.lean + lake-manifest.json +
-- lean-toolchain are authoritative (mathfin.toml just sets local_project = ".").
require BrownianMotion from git
  "https://github.com/RemyDegenne/brownian-motion.git" @
  "fa590b1a198cb464357c5b773c7451da941acb43"

-- Pinned to Degenne brownian-motion's lake-manifest commit (so all transitive
-- versions resolve consistently). Bump together with the BrownianMotion pin.
-- KEEP LAST: Lake resolves transitive-dependency conflicts in favor of later
-- requires, so mathlib-last pins batteries/Cli/etc. at Mathlib's revs.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "c87cc975222146012dc1c942c109f2decf536045"
