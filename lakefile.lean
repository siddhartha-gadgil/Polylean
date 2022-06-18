import Lake
open Lake DSL

package polylean {
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "9c54c410ebcd03ebecb4f8b0e510735088dd5412"
  },
  { name := `aesop
    src := Source.git "https://github.com/JLimperg/aesop" "3d7ae7fa4a1ddb3ae0448d82d65c0acf2e031351" }
],
}
