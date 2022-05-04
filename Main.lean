import Polylean
import Polylean.LengthBound
import Polylean.Length
import Polylean.ProvedBound
import Polylean.MemoLength
import Polylean.LengthNode
open Letter

def main(args: List String) : IO Unit := do
  for k in [1, 2, 6] do
    let w := #[α, β, α!, β!]^k ++ #[α]
    IO.println s!"computing length via powers of {w}"
    for n in [1:21] do
      let l ← powerLength w n
      IO.println s!"length of {w} from power {n}: {l}"
  let w := #[α, β, α!, β!] 
  IO.println s!"computing length via powers of the commutator {w}" 
  for n in [1:21] do
    let l ← powerLength w n
    IO.println s!"length of {w} from power {n}: {l}"
  let l ← lengthNodes w
  IO.println s!"length of {w}: {l}"
  IO.println s!"derived length: {(← derivedLength! w)}"
  let (l₀, ns) ← derivedProof! w
  let ns := ns.eraseDups
  let mut j := 0
  for node in ns do
    j := j + 1
    let w := node.top
    let l ← lengthNodes w
    IO.println s!"Lemma {j}: l({w}) ≤ {l}"
    IO.println s!"Proof: apply {node}"
    for w in node.base do
      let l ← lengthNodes w
      IO.println s!"  using l({w}) ≤ {l}"
    IO.println ""
