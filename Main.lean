import Polylean
import Polylean.LengthBound
import Polylean.ProvedBound
import Polylean.MemoLength
open Letter

def main : IO Unit := do
  let n := 7
  let w := [α, α, β, α!, β!]^n
  let l ← memoLength w 
  IO.println s!"Length of [α, α, β, α!, β!]^{n}, {l}"
  