import Std 
import Polylean.LengthBound
open Std

initialize normCache : IO.Ref (HashMap Word Nat) ← IO.mkRef (HashMap.empty)

partial def memoLength : Word → IO Nat := fun w => do
  let cache ← normCache.get
  match cache.find? w with
  | some n => 
      pure n
  | none =>
    match w with  
    | [] => return 0
    | x :: ys => do
      let base := 1 + (← memoLength ys)
      let derived : List Nat ←  (splits x⁻¹ ys).mapM 
            (fun (fst, snd) => do (← memoLength fst) + (←  memoLength snd)) 
      let res := derived.foldl min base -- minimum of base and elements of derived
      normCache.set <| cache.insert w res
      return res
