import Lake
open Lake DSL

package Polylean {
  precompileModules := true
}

@[default_target]
lean_lib UnitConjecture

@[default_target]
lean_lib ConjInvLength

lean_lib Complexes

lean_lib Experiments

@[default_target]
lean_exe polymath

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4.git" @ "main"
