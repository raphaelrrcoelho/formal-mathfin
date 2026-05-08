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
