import Lake
open Lake DSL

package HybridVerify where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Library `HybridVerify` lives at `HybridVerify/*.lean` (default srcDir = ".").
@[default_target]
lean_lib HybridVerify where

-- Pinned to Degenne brownian-motion's lake-manifest commit (so all transitive
-- versions resolve consistently). Bump together with the BrownianMotion pin.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "f23306121184"

-- RemyDegenne/brownian-motion: Brownian motion construction, multivariate
-- Gaussian, Kolmogorov-Chentsov continuity, Doob's L^p inequality, stochastic
-- integral approximation. Pinned to a specific commit so toolchain bumps stay
-- deterministic. Mirrored in hybrid_verify.toml's
-- [[hybrid-verify.lean.extra_requires]] so lean-interact also sees it.
require BrownianMotion from git
  "https://github.com/RemyDegenne/brownian-motion.git" @
  "51807683c5130238fd4013b2fbee314135e3d8d9"
