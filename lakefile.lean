import Lake
open Lake DSL

package polylean {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "9c54c410ebcd03ebecb4f8b0e510735088dd5412"
  }],

}
