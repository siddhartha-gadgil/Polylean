import Lake
open Lake DSL

package polylean

@[defaultTarget]
lean_lib GardamTheorem

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"