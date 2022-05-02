import Polylean
import Polylean.LengthBound
import Polylean.Length
import Polylean.ProvedBound
import Polylean.MemoLength
open Letter

def main(args: List String) : IO Unit := do
  let n : Nat := 
    match args.head? with
    | none => 7 
    | some s =>
      match s.toNat? with
      | some n => n
      | none => 7
  let w := [α, α, β, α!, β!]^n
  let l ← wordLength w 
  IO.println s!"Length of [α, α, β, α!, β!]^{n}, {l}"
  