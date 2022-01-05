import Polylean.LengthBound
import Polylean.ProvedBound
open Letter
open Nat

theorem appendLengths{α : Type}(fst: List α)(snd: List α): 
          (fst ++ snd).length = fst.length + snd.length :=
          match fst with
          | [] => by 
              have prep : [] ++ snd = snd := by rfl
              rw [prep]
              have nl : List.length ([] : List α) = 0 := by rfl
              rw [nl]
              apply Eq.symm
              apply Nat.zero_add
          | (x::xs) => by 
                have lhs : List.length (x :: xs ++ snd) = List.length (xs ++ snd) + 1 := by rfl
                rw [lhs]
                have ht : List.length (x :: xs) = List.length xs + 1 := by rfl
                rw [ht]
                rw [appendLengths xs snd]
                rw [Nat.add_assoc]
                rw [Nat.add_assoc]
                apply congrArg (fun n => xs.length + n)
                apply Nat.add_comm
                 
theorem splitFirst{l: Letter}{w: Word}(ps: ProvedSplit l w): 
          ps.fst.length + 1 ≤ w.length :=
          by
            let lem := appendLengths (ps.fst ++ [l]) ps.snd
            rw [← ps.proof] at lem  
            rw [lem]
            have lem2 : List.length (ps.fst ++ [l]) = ps.fst.length + 1 := by 
                apply appendLengths
            rw [lem2]
            apply Nat.le_add_right

theorem splitSecond{l: Letter}{w: Word}(ps: ProvedSplit l w): 
          ps.snd.length + 1 ≤ w.length :=
          by
            let lem := appendLengths (ps.fst ++ [l]) ps.snd
            rw [← ps.proof] at lem  
            rw [lem]
            have lem2 : List.length (ps.fst ++ [l]) = ps.fst.length + 1 := by 
                apply appendLengths
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
  | Nat.succ j =>
    match w with
    | [] => fun _ => ProvedBound.emptyWord
    | x :: ys => fun wit =>
      have lem : ys.length ≤ j := by
          have lm : List.length (x :: ys) = ys.length + 1 := rfl
          rw [lm] at wit
          apply Nat.le_of_succ_le_succ
          exact wit
      let head := ProvedBound.prepend x (totalProvedBound j ys lem)
      let splits := provedSplits x⁻¹  ys
      let tail := splits.map (fun ps => 
        let fstBound : ps.fst.length ≤ j := by
              have lm := splitFirst ps
              apply Nat.le_of_succ_le_succ
              apply Nat.le_trans lm
              have lm2: List.length (x :: ys) = ys.length + 1 := rfl
              rw [lm2] at wit
              apply Nat.le_of_succ_le_succ
              apply Nat.le_trans wit
              apply Nat.le_succ
        let sndBound : ps.snd.length ≤ j := by
              have lm := splitSecond ps
              apply Nat.le_of_succ_le_succ
              apply Nat.le_trans lm
              have lm2: List.length (x :: ys) = ys.length + 1 := rfl
              rw [lm2] at wit
              apply Nat.le_of_succ_le_succ
              apply Nat.le_trans wit
              apply Nat.le_succ
        ProvedBound.headMatches x ys ps.fst ps.snd ps.proof 
          (totalProvedBound j ps.fst fstBound ) 
          (totalProvedBound j ps.snd sndBound ))
      ProvedBound.min head tail

#eval (totalProvedBound 5 ([α, α, β, α!, β!]) (by decide)).bound

#eval (totalProvedBound 10 ([α, α, β, α!, β!]^2) (by decide) ).bound
