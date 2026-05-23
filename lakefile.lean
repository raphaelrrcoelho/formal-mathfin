import Lake
open Lake DSL

package QuantFin where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Library `QuantFin` lives at `QuantFin/*.lean` (default srcDir = ".").
@[default_target]
lean_lib QuantFin where

-- Pinned to Degenne brownian-motion's lake-manifest commit (so all transitive
-- versions resolve consistently). Bump together with the BrownianMotion pin.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "f23306121184"

-- RemyDegenne/brownian-motion: Brownian motion construction, multivariate
-- Gaussian, Kolmogorov-Chentsov continuity, Doob's L^p inequality, stochastic
-- integral approximation. Pinned to a specific commit so toolchain bumps stay
-- deterministic. Mirrored in quantfin.toml's
-- [[quantfin.lean.extra_requires]] so lean-interact also sees it.
require BrownianMotion from git
  "https://github.com/RemyDegenne/brownian-motion.git" @
  "16d15eb42c8c4a612bd0aacb28078c1802597216"
