import Mathlib.Algebra.Ring.Basic

/-! 
## `ℤ` as an integral domain

Proof that if the product of two integers (or natural numbers) is `0`, one of them is `0`. This is a rather low-level proof, using definitions of `Int` and the operations -/
open Nat Int

theorem mul_succ_succ (n m: Nat) : (succ n) * (succ m) =
          succ ((succ n) * m + n) := by rfl

/-- if the product of natural numbers is `0`, one of them is `0` -/
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
        
/-! some formulae for expanding multiplication -/
theorem int_mul_succ_succ (n m: Nat) : 
  (Int.ofNat (succ n)) * (Int.ofNat (succ m)) =
         Int.ofNat (succ ((succ n) * m + n)) := by rfl

theorem int_mul_succ_negsucc (n m: Nat) : 
  (Int.ofNat (succ n)) * (Int.negSucc m) =
         Int.negSucc ((succ n) * m + n) := by rfl

theorem int_mul_negsucc_negsucc (n m: Nat) : 
  (Int.negSucc n) * (Int.negSucc m) =
         Int.ofNat (succ ((succ n) * m + n)) := by rfl

/-- if the product of integers is `0`, one of them is `0` -/
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

lemma zero_of_double_zero : ∀ m : ℤ, m + m = 0 ↔ m = 0 := by
  intro m; apply Iff.intro
  · intro h
    have two_not_zero : ¬(2 = (0 : ℤ)) := by simp
    revert two_not_zero; rw [← or_iff_not_imp_left]
    apply int_domain
    show (1 + 1) * m = 0
    rw [add_mul, one_mul]
    assumption
  · intro h; subst h; rfl
