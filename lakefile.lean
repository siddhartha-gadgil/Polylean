import Lake
open Lake DSL

package Polylean {
  precompileModules := true
}

@[defaultTarget]
lean_lib Polylean

@[defaultTarget]
lean_exe polymath

@[defaultTarget]
lean_lib GardamTheorem

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"a4369ab32fb20b9bd33f5064032ff2b2e2f67abe"

require std from git
  "https://github.com/leanprover/std4"@"735cbeae0fe896a7029d616b651e6a71e27653f8"
