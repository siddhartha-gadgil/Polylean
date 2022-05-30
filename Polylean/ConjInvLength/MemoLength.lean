import Std 
import Polylean.ConjInvLength.LengthBound
open Std

initialize normCache : IO.Ref (HashMap Word Nat) ← IO.mkRef (HashMap.empty)

def memoLength : Word → IO Nat := fun w => do
  let cache ← normCache.get
  match cache.find? w with
  | some n => 
      pure n
  | none =>
    match w with  
    | [] => return 0
    | x :: ys => do
      let base := 1 + (← memoLength ys)
      let derived ←  (splits x⁻¹ ys).mapM fun ⟨(fst, snd), h⟩ => do
        have h : fst.length + snd.length < ys.length + 1 := Nat.lt_trans h (Nat.lt_succ_self _)
        have h1 : snd.length < ys.length + 1  := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h
        have h2 : fst.length < ys.length + 1 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h
        return (← memoLength fst) + (← memoLength snd)
      let res := derived.foldl min base -- minimum of base and elements of derived
      normCache.set <| (← normCache.get).insert w res
      return res
termination_by _ l => l.length

#check Array.eraseIdx'

#check -1

#eval #[1, 3, 5].eraseIdx' (0: Fin 3)