import Mathlib.Algebra.Ring.Basic

open Nat Int

#check Nat.mul
#check Int.mul

theorem mul_succ_succ (n m: Nat) : (succ n) * (succ m) =
          succ ((succ n) * m + n) := by rfl

theorem nat_domain (n m: Nat) : n * m = 0 → n = 0 ∨ m = 0 := by
    cases n
    case zero =>
      intro hyp 
      apply Or.inl
      rfl
    case succ n' =>
      cases m
      case zero => 
        intro hyp
        apply Or.inr
        rfl
      case succ m' =>
        intro hyp 
        simp [mul_succ_succ] at hyp
        
