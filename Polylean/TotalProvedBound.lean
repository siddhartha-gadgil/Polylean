import Polylean.LengthBound
import Polylean.ProvedBound
open Letter
open Nat

theorem splitFirst{l: Letter}{w: Word}(ps: ProvedSplit l w): 
          ps.fst.length + 1 ≤ w.length :=
          by
            let lem : (ps.fst ++ [l] ++ ps.snd).length = 
                (ps.fst ++ [l]).length + ps.snd.length := by apply List.length_append
            rw [← ps.proof] at lem  
            rw [lem]
            have lem2 : List.length (ps.fst ++ [l]) = ps.fst.length + 1 := by 
                apply List.length_append
            rw [lem2]
            apply Nat.le_add_right

theorem splitSecond{l: Letter}{w: Word}(ps: ProvedSplit l w): 
          ps.snd.length + 1 ≤ w.length :=
          by
            let lem : (ps.fst ++ [l] ++ ps.snd).length = 
                (ps.fst ++ [l]).length + ps.snd.length := by apply List.length_append
            rw [← ps.proof] at lem  
            rw [lem]
            have lem2 : List.length (ps.fst ++ [l]) = ps.fst.length + 1 := by 
                apply List.length_append
            rw [lem2]
            rw [Nat.add_assoc]
            rw [Nat.add_comm]
            apply Nat.le_add_left

def totalProvedBound(n: Nat) : (w: Word) → (w.length ≤ n) →  ProvedBound w := fun w =>
  match n with
  | 0 => 
    match w with
    | [] => fun _ => ProvedBound.emptyWord
    | x :: ys => by 
      intro wit
      have lem : 0 < List.length (x :: ys) := by apply Nat.succ_pos
      have lem2: 0 < 0 := Nat.lt_of_lt_of_le lem wit
      exact False.elim (Nat.lt_irrefl 0 lem2)
  | m + 1 =>
    match w with
    | [] => fun _ => ProvedBound.emptyWord
    | x :: ys => fun wit =>
      have lem : ys.length ≤ m := by
          have lm : List.length (x :: ys) = ys.length + 1 := rfl
          rw [lm] at wit
          apply Nat.le_of_succ_le_succ
          exact wit
      let head := ProvedBound.prepend x (totalProvedBound m ys lem)
      let splits := provedSplits x⁻¹  ys
      let tail := splits.map (fun ps => 
        let fstBound : ps.fst.length ≤ m := by
              have lm := splitFirst ps
              apply Nat.le_of_succ_le_succ
              apply Nat.le_trans lm
              have lm2: List.length (x :: ys) = ys.length + 1 := rfl
              rw [lm2] at wit
              apply Nat.le_of_succ_le_succ
              apply Nat.le_trans wit
              apply Nat.le_succ
        let sndBound : ps.snd.length ≤ m := by
              have lm := splitSecond ps
              apply Nat.le_of_succ_le_succ
              apply Nat.le_trans lm
              have lm2: List.length (x :: ys) = ys.length + 1 := rfl
              rw [lm2] at wit
              apply Nat.le_of_succ_le_succ
              apply Nat.le_trans wit
              apply Nat.le_succ
        ProvedBound.headMatches x ys ps.fst ps.snd ps.proof 
          (totalProvedBound m ps.fst fstBound ) 
          (totalProvedBound m ps.snd sndBound ))
      ProvedBound.min head tail

#eval (totalProvedBound 5 ([α, α, β, α!, β!]) (by decide)).bound

#eval (totalProvedBound 10 ([α, α, β, α!, β!]^2) (by decide)).bound
