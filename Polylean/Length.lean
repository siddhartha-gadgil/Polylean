import Std 
import Polylean.LengthBound
open Std
open Letter

def Letter.int : Letter → Int
  | α => 1
  | β => 2
  | α! => -1
  | β! => -2 

abbrev Wrd := Array Letter

def Word.wrd (w: Word) : Wrd := w.toArray -- .map <| fun l => l.int

universe u

namespace Wrd

def hashfn (w: Wrd) : UInt64 := 
  w.foldl (fun h i => mixHash h (hash i)) 7

instance : Hashable Wrd := ⟨hashfn⟩

initialize normCache : IO.Ref (HashMap Wrd Nat) ← IO.mkRef (HashMap.empty)

def splits(w: Wrd)(l : Letter) : IO <| Array (Wrd × Wrd) := do
  let mut tail := w.eraseIdx 0
  let mut init : Wrd := #[]
  let mut accum : Array (Wrd × Wrd) := #[]
  for x in w do
    if l = x then
      accum := accum.push (init, tail)
    init := init.push x
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
        let ys := w.pop
        let x := w.back
        let mut l := 1 + (← length <| ys)
        let pairs ←  splits ys (x.inv)
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

#eval (Word.wrd ([α, α, β, α!, α,  β!])).splits (α)

#check Array.reverse
