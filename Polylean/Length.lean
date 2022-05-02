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

partial def splits(l : Letter) : (w : Wrd) → Array (Wrd × Wrd) := fun w =>
  match w.size, w with
  | 0, _ => #[]
  | m + 1 , _ =>
    let x := w.back
    let ys := w.pop
    let tailSplits := (splits l ys).map fun (fst, snd) =>
      (fst, snd.push x)
    if x = l then tailSplits.push (ys, #[]) else tailSplits

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
        let pairs :=  splits (x.inv) ys
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
