import Polylean
import Polylean.LengthBound
import Polylean.Length
import Polylean.ProvedBound
import Polylean.MemoLength
open Letter

def main : IO Unit := do
  let n := 7
  let w := [α, α, β, α!, β!]^n
  let l ← wordLength w 
  IO.println s!"Length of [α, α, β, α!, β!]^{n}, {l}"
  