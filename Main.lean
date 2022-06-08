import Polylean
import Polylean.UnitConjecture
import Polylean.ConjInvLength.LengthBound
import Polylean.ConjInvLength.Length
import Polylean.ConjInvLength.ProvedBound
import Polylean.ConjInvLength.MemoLength
import Polylean.ConjInvLength.LengthNode

/-
open Letter in
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
-/

open Murray in
def main : IO Unit := do
  let x : Bool := α * α' == (1 : RP)
  IO.println s!"{x}"
  return ()
