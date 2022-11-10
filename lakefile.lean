import Lake
open Lake DSL

package Polylean {
  precompileModules := true
}

@[default_target]
lean_lib Polylean

@[default_target]
lean_exe polymath

@[default_target]
lean_lib GardamTheorem

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"
