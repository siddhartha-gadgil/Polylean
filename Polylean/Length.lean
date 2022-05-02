import Std 
import Polylean.LengthBound
open Std
open Letter

def Letter.int : Letter → Int
  | α => 1
  | β => 2
  | α! => -1
  | β! => -2 

abbrev Wrd := Array Int

def Word.wrd (w: Word) : Wrd := w.toArray.map <| fun l => l.int

universe u

instance{α : Type u}[Hashable α] : Hashable (Array α) :=
  ⟨fun arr => hash arr.data⟩

namespace Wrd

initialize normCache : IO.Ref (HashMap Wrd Nat) ← IO.mkRef (HashMap.empty)

def splits(w: Wrd)(l : Int) : IO <| Array (Wrd × Wrd) := do
  let mut tail := w.eraseIdx 0
  let mut init : Wrd := #[]
  let mut accum : Array (Wrd × Wrd) := #[]
  for j in [0:w.size] do
    if l = w[j] then
      accum := accum.push (init, tail)
    init := init.push w[j]
    tail := tail.eraseIdx 0
  return accum

partial def length : Wrd →  IO Nat := fun w =>
do
  let cache ← normCache.get
  match cache.find? w with
  | some n => 
      pure n
  | none =>
    let res ← 
      match w.size with
      | 0 => pure 0
      | k + 1 => do
        let mut l := 1 + (← length <| w.eraseIdx 0)
        let x := w[0]
        let ys := w.eraseIdx 0
        let pairs ←  splits ys (-x)
        for (fst, snd) in pairs do
          let pl := (← length <| fst) + (← length <| snd)
          if pl < l then
            l := pl
        pure l
    normCache.set <| cache.insert w res
    return res

end Wrd

def wordLength(w: Word):IO Nat :=
  Wrd.length <| Word.wrd w

#eval (Word.wrd ([α, α, β, α!, α,  β!])).splits (1)
