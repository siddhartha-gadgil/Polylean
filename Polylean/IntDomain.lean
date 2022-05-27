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
        
theorem int_mul_succ_succ (n m: Nat) : 
  (Int.ofNat (succ n)) * (Int.ofNat (succ m)) =
         Int.ofNat (succ ((succ n) * m + n)) := by rfl

theorem int_mul_succ_negsucc (n m: Nat) : 
  (Int.ofNat (succ n)) * (Int.negSucc m) =
         Int.negSucc ((succ n) * m + n) := by rfl

theorem int_mul_negsucc_negsucc (n m: Nat) : 
  (Int.negSucc n) * (Int.negSucc m) =
         Int.ofNat (succ ((succ n) * m + n)) := by rfl

theorem int_domain (n' m': Int) : n' * m' = 0 → n' = 0 ∨ m' = 0 := by
    cases n'
    case ofNat n => 
      cases m'
      case ofNat m =>
        cases n
        case zero =>
          intro hyp 
          apply Or.inl
          rfl
        case succ n'' =>
          cases m
          case zero => 
            intro hyp
            apply Or.inr
            rfl
          case succ m'' =>
            intro hyp 
            rw [int_mul_succ_succ] at hyp
            let hyp' : succ (succ n'' * m'' + n'') = 0 := by
              injection hyp
              assumption
            simp at hyp'  
      case negSucc m =>
        intro hyp
        cases n
        case zero => 
          apply Or.inl
          rfl
        case succ n' => 
          rw [int_mul_succ_negsucc] at hyp
          simp at hyp
    case negSucc n =>
      intro hyp
      cases m'
      case ofNat m'' => 
        rw [mul_comm] at hyp
        cases m''
        case zero => 
          apply Or.inr
          rfl
        case succ m''' => 
          rw [int_mul_succ_negsucc] at hyp
          simp at hyp
      case negSucc m'' =>
        rw [int_mul_negsucc_negsucc] at hyp
        let hyp' : succ (succ n * m'' + n) = 0 := by
          injection hyp
          assumption
        simp at hyp'      