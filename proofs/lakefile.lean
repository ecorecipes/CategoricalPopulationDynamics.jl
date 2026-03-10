import Lake
open Lake DSL

package "CpmProofs" where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require "leanprover-community" / "mathlib"

require mdgen from git
  "https://github.com/Seasawher/mdgen" @ "main"

@[default_target]
lean_lib «CpmProofs» where
  globs := #[.submodules `CpmProofs]
