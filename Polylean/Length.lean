import Std 
import Polylean.LengthBound
open Std
open Letter

def Letter.int : Letter → Int
  | α => 1
  | β => 2
  | α! => -1
  | β! => -2 

open Letter

instance : Pow Word Nat where
  pow w n := w.pow n

abbrev Wrd := Array Letter

def Word.wrd (w: Word) : Wrd := w.toArray -- .map <| fun l => l.int

def Wrd.toString(w: Wrd) := w.foldl (fun x y => s!"{x}{y}") ""

instance : ToString Wrd := ⟨Wrd.toString⟩

def Wrd.pow : Wrd → Nat → Wrd 
  | w, 0 => #[]
  | w, Nat.succ m => w ++ (pow w m)

instance : Pow Wrd Nat where
  pow w n := w.pow n
namespace Wrd

def hashfn (w: Wrd) : UInt64 := 
  w.foldl (fun h i => mixHash h (hash i)) 7

instance : Hashable Wrd := ⟨hashfn⟩

initialize normCache : IO.Ref (HashMap Wrd Nat) ← IO.mkRef (HashMap.empty)

def splits(l : Letter) : (w : Wrd) → Array {p : Wrd × Wrd // p.1.size + p.2.size < w.size} := fun w =>
  match h:w.size with
  | 0 => #[]
  | m + 1  =>    
    let x := w.back
    have lll : w.size -1 < w.size := by
      rw [h] 
      apply Nat.le_refl
    let ys := w.pop
    have ysize : ys.size = m := by
      rw [Array.size_pop, h]
      rfl
    let tailSplits := (splits l ys).map fun ⟨(fst, snd), h⟩ =>
      ⟨(fst, snd.push x), by 
        rw [Array.size_push]
        rw [ysize] at h
        simp [Nat.add_succ, Nat.succ_lt_succ h]⟩
    if x = l then tailSplits.push ⟨(ys, #[]), 
      by 
        rw [ysize]
        apply Nat.le_refl⟩ else tailSplits
termination_by _ l w => w.size

def length(w : Wrd) :  IO Nat := 
do
  let cache ← normCache.get
  match cache.find? w with
  | some n => 
      pure n
  | none =>
    let res ← 
      match h:w.size with
      | 0 => pure 0
      | m + 1 => do
        let ys := w.pop
        let x := w.back
        have lll : w.size -1 < w.size := by
          rw [h] 
          apply Nat.le_refl
        let base := 1 + (← length <| ys)
        let derived ←  (splits x⁻¹ ys).mapM fun ⟨(fst, snd), h0⟩ => 
          have ysize : ys.size = m := by
            rw [Array.size_pop, h]
            rfl
          have h0 : fst.size + snd.size < w.size := by
            rw [h]
            rw [← ysize]
            apply Nat.lt_trans h0 (Nat.lt_succ_self _)
          have h1 : snd.size < w.size  := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h0
          have h2 : fst.size < w.size := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h0
          return (← length fst) + (← length snd)
        derived.foldl (fun x y => do return min (← x) y) (pure base)
    normCache.set <| (← normCache.get).insert w res
    return res
termination_by _ w => w.size

end Wrd

def wordLength(w: Word):IO Nat :=
  Wrd.length <| Word.wrd w

def Wrd.conj: Wrd → Letter → Wrd := fun w l => #[l] ++ w ++ #[l⁻¹]

instance: Pow Wrd Letter where
  pow w l := w.conj l

#eval (Word.wrd ([α, α, β, α!, α,  β!])).splits (α)

#check Array.size_push

#check Nat.pred