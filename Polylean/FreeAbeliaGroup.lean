import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
open SubNegMonoid

-- currently mainly experiments

variable {A : Type} [abg : AddCommGroup A]

def f (a: A) : ℤ → A := 
  fun n => abg.gsmul n a

theorem isHomPos (x : A) (n m: Nat) : f x (n + m) = f x n + f x m :=
  by 
    induction m with
    | zero =>
      simp [f]
      rw [abg.gsmul_zero']
      simp     
    | succ k ih =>
      simp [f]
      simp [f] at ih
      rw [← add_assoc]
      simp
      let l₁ := abg.gsmul_succ' k x
      simp at l₁
      rw [l₁]
      simp
      let l₂ := abg.gsmul_succ' (n + k) x
      simp at l₂
      rw [l₂] 
      rw [ih]
      simp
      conv =>
        lhs
        rw [← add_assoc]
        arg 1
        rw [add_comm]
      rw [← add_assoc]

