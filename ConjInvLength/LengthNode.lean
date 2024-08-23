import ConjInvLength.Length
import Batteries
open Batteries

inductive ProofNode :   Type
| empty : ProofNode
| gen: (l : Letter) → ProofNode
| triang: (w₁ w₂ : Wrd) → ProofNode
| conj : (l: Letter) → (w: Wrd) → ProofNode
| power : (n: Nat) →  (w: Wrd) → ProofNode
deriving Repr, BEq

open ProofNode


def ProofNode.top: ProofNode → Wrd
| empty => #[]
| gen l => #[l]
| triang w₁ w₂ => w₁ ++ w₂
| conj l w => w ^ l
| power n w => w

def ProofNode.toString : ProofNode → String
| empty => "l(e) = 0 (trivial word)"
| gen l => s!"l({l}) = 1 (normalization)"
| triang w₁ w₂ => s!"l({w₁ ++ w₂}) ≤ l({w₁}) + l({w₂}) (triangle inequality)"
| conj l w => s!"l({w}^{l}) = l({w}) (conjugacy invariance)"
| power n w => s!"l(w) ≤  l({w^n})/{n} (homogeneity)"

instance : ToString ProofNode := ⟨ProofNode.toString⟩

def ProofNode.base: ProofNode → List Wrd
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
    IO.Ref (HashMap Wrd Float) ← IO.mkRef (HashMap.empty)

initialize proofCache :
    IO.Ref (HashMap Wrd ProofNode) ← IO.mkRef (HashMap.empty)

def cacheLength?(w: Wrd) : IO (Option Float) :=
    do
    let cache ← floatNormCache.get
    match cache.find? w with
    | some n => pure (some n)
    | none => pure none

-- nodes are saved as a side effect of the computation
partial def lengthNodes : Wrd → IO Float := fun w => do
  match ← cacheLength? w with
  | some n =>
      pure n
  | none =>
    if w.size =0 then
      floatNormCache.set <| (← floatNormCache.get).insert #[] 0
      proofCache.set <| (← proofCache.get).insert #[] empty
      return 0
    else do
      let x := w.back
      let ys : Wrd := w.pop
      let base := 1 + (← lengthNodes ys)
      let derived ←  (ys.splits x⁻¹).mapM fun ⟨(fst, snd), h⟩ => do
        have h : fst.size + snd.size < ys.size + 1 := Nat.lt_trans h (Nat.lt_succ_self _)
        have h1 : snd.size < ys.size + 1  := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h
        have h2 : fst.size < ys.size + 1 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h
        return ((← lengthNodes fst) + (← lengthNodes snd), fst, snd)
      let (res, nodes) := derived.foldl (
          fun (l₁, ns) (l₂, fst, snd) =>
            if l₂ < l₁ then (l₂, [triang fst (snd^(x⁻¹)), conj (x⁻¹) snd]) else (l₁, ns)
      ) (base, [gen x, triang ys #[x]])
      floatNormCache.set <| (← floatNormCache.get).insert w res
      for node in nodes do
        proofCache.set <| (← proofCache.get).insert (node.top) node
      return res

def powerLength : Wrd → Nat → IO Float
| w, n => do
  let pl ← lengthNodes (w ^ n)
  let res := pl / n.toFloat
  match ← cacheLength? w with
  | none =>
    floatNormCache.set <| (← floatNormCache.get).insert w res
    if n >1 then
      proofCache.set <| (← proofCache.get).insert w (power n w)
    return res
  | some l₀ =>
    if res < l₀ then
      IO.println s!"updated cache for {w}"
      floatNormCache.set <| (← floatNormCache.get).insert w res
      if n >1 then
        proofCache.set <| (← proofCache.get).insert w (power n w)
      return res
    else
      return l₀

partial def resolveProof(w: Wrd) : IO ((List ProofNode) × (List Wrd)) := do
  let cache ← proofCache.get
  match cache.find? w with
  | none => return ([], [w])
  | some node =>
    let ws := node.base
    let offspring ←  ws.mapM resolveProof
    return offspring.foldl (fun (ns, ws) (ns', ws') => (ns ++ ns', ws ++ ws') ) ([node], [])

partial def derivedLength!(w: Wrd) : IO Float := do
  let cache ← proofCache.get
  match cache.find? w with
  | none => panic! s!"no cached node for {w}"
  | some node =>
    match node with
    | empty => return 0.0
    | gen l => return 1.0
    | triang w₁ w₂ => return (← derivedLength! w₁) + (← derivedLength! w₂)
    | conj l w => derivedLength! w
    | power n w => return (← derivedLength! (w^n)) / n.toFloat

partial def derivedProof!(w: Wrd) : IO (Float × (List ProofNode)) := do
  let cache ← proofCache.get
  match cache.find? w with
  | none => panic! s!"no cached node for {w}"
  | some node =>
    match node with
    | empty => return (0.0, [empty])
    | gen l => return (1.0, [gen l])
    | triang w₁ w₂ =>
      let (l₁, ns₁) ← derivedProof! w₁
      let (l₂, ns₂) ← derivedProof! w₂
      return (l₁ + l₂, ns₁ ++ ns₂ ++ [triang w₁ w₂])
    | conj l w =>
      let (l₀, ns) ← derivedProof! w
      return (l₀, ns ++ [conj l w])
    | power n w =>
      let (l₀, ns) ← derivedProof! (w^n)
      return (l₀ / n.toFloat, ns ++ [power n w])
