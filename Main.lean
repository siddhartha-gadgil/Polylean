import Polylean
import Polylean.LengthBound
import Polylean.Length
import Polylean.ProvedBound
import Polylean.MemoLength
import Polylean.LengthNode
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
  let l' ← lengthNodes w
  IO.println s!"Length of [α, α, β, α!, β!]^{n}, {l} (= {l'})"
  IO.println s!"Nodes generated: {(← proofCache.get).size}"
  let (ns, ws) ← resolveProof w
  IO.println s!"Resolved proof; nodes: {ns.eraseDups.length}, base: {ws.length}"
  IO.println s!"derived length: {(← derivedLength! w)}"
  for k in [1, 2, 6] do
    let w := [α, β, α!, β!]^k ++ [α]
    IO.println s!"computing length via powers of {w}"
    for n in [1:21] do
      let l ← powerLength w n
      IO.println s!"length of {w} from power {n}: {l}"
  let w := [α, β, α!, β!] 
  IO.println s!"computing length via powers of the commutator {w}" 
  for n in [1:21] do
    let l ← powerLength w n
    IO.println s!"length of {w} from power {n}: {l}"
  let l ← lengthNodes w
  IO.println s!"length of {w}: {l}"
  IO.println s!"derived length: {(← derivedLength! w)}"

