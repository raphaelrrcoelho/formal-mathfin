import Lake
open Lake DSL

package HybridVerify where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib HybridVerify where
  srcDir := "HybridVerify"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

-- RemyDegenne/brownian-motion: Brownian motion construction, multivariate
-- Gaussian, Kolmogorov-Chentsov continuity, Doob's L^p inequality, stochastic
-- integral approximation. Pinned to a specific commit so toolchain bumps stay
-- deterministic. Mirrored in hybrid_verify.toml's
-- [[hybrid-verify.lean.extra_requires]] so lean-interact also sees it.
require BrownianMotion from git
  "https://github.com/RemyDegenne/brownian-motion.git" @
  "51807683c5130238fd4013b2fbee314135e3d8d9"
