import Lake
open Lake DSL

package polylean

@[default_target]
lean_lib GardamTheorem

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.9.0"
