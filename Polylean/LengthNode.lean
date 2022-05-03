import Polylean.LengthBound
import Polylean.ProvedBound
import Std 
open Std

inductive ProofNode :   Type
| empty : ProofNode
| gen: (l : Letter) → ProofNode
| triang: (w₁ w₂ : Word) → ProofNode 
| conj : (l: Letter) → (w: Word) → ProofNode 
| power : (n: Nat) →  (w: Word) → ProofNode 
deriving Repr, BEq

open ProofNode
def ProofNode.top: ProofNode → Word
| empty => []
| gen l => [l]
| triang w₁ w₂ => w₁ ++ w₂
| conj l w => w ^ l
| power n w => w ^ n

def ProofNode.base: ProofNode → List Word
| empty => []
| gen l => []
| triang w₁ w₂ => [w₁, w₂]
| conj l w => [w]
| power n w => [w ^ n]


def ProofNode.baseLength: ProofNode → Option Nat
| empty => some 0
| gen l => some 1
| _ => none


initialize floatNormCache : 
    IO.Ref (HashMap Word Float) ← IO.mkRef (HashMap.empty)

initialize proofCache : 
    IO.Ref (HashMap Word ProofNode) ← IO.mkRef (HashMap.empty)

def cacheLength?(w: Word) : IO (Option Float) :=
    do
    let cache ← floatNormCache.get
    match cache.find? w with
    | some n => pure (some n)
    | none => pure none 

-- nodes saved as a side effect of the computation
def lengthNodes : Word → IO Float := fun w => do
  match ← cacheLength? w with
  | some n => 
      pure n
  | none =>
    match w with  
    | [] => 
      floatNormCache.set <| (← floatNormCache.get).insert [] 0
      proofCache.set <| (← proofCache.get).insert [] empty
      return 0
    | x :: ys => do
      let base := 1 + (← lengthNodes ys)
      let derived ←  (splits x⁻¹ ys).mapM fun ⟨(fst, snd), h⟩ => do
        have h : fst.length + snd.length < ys.length + 1 := Nat.lt_trans h (Nat.lt_succ_self _)
        have h1 : snd.length < ys.length + 1  := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h
        have h2 : fst.length < ys.length + 1 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h
        return ((← lengthNodes fst) + (← lengthNodes snd), fst, snd)
      let (res, nodes) := derived.foldl (
          fun (l₁, ns) (l₂, fst, snd) => 
            if l₂ < l₁ then (l₂, [triang (fst^x) snd, conj x fst]) else (l₁, ns)
      ) (base, [gen x, triang [x] ys]) 
      floatNormCache.set <| (← floatNormCache.get).insert w res
      for node in nodes do
        proofCache.set <| (← proofCache.get).insert (node.top) node
      return res
termination_by _ l => l.length

partial def resolveProof(w: Word) : IO ((List ProofNode) × (List Word)) := do 
  let cache ← proofCache.get
  match cache.find? w with
  | none => return ([], [w])
  | some node => 
    let ws := node.base
    let offspring ←  ws.mapM resolveProof
    return offspring.foldl (fun (ns, ws) (ns', ws') => (ns ++ ns', ws ++ ws') ) ([node], [])

partial def derivedLength!(w: Word) : IO Float := do
  let cache ← proofCache.get
  match cache.find? w with
  | none => panic! s!"no cached node for {w}"
  | some node => 
    match node.baseLength with
    | some n => pure n.toFloat
    | none => 
      let offspring ←  node.base.mapM (derivedLength!)
      return offspring.foldl (fun l₁ l₂ => l₁ + l₂) 0
