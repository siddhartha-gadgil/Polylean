import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Find

/-! Proof that if the product of two integers (or natural numbers) is `0`, one of them is `0`. This is a rather low-level proof, using definitions of `Int` and the operations -/

#find _ = 0 ∨ _ = 0
#check Int.mul_eq_zero

/-- If the product of integers is `0`, one of them is `0`. -/
theorem int_domain (n' m': Int) : n' * m' = 0 → n' = 0 ∨ m' = 0 := Int.mul_eq_zero.mp

@[simp] lemma zsmul_int (m n : ℤ) : m • n = m * n := by
  induction m with
    | ofNat m =>
      induction m with
        | zero =>
          show 0 = (0 : ℤ) * n
          rw [zero_mul]
        | succ m' ih =>
          show n + nsmulRec m' n = (m' + 1) * n
          have : nsmulRec m' n = m' * n := ih
          rw [this, add_mul, add_comm]
          simp
    | negSucc m =>
      induction m with
        | zero =>
          show -(n + 0) = -1 * n
          rw [_root_.add_zero, Int.neg_eq_neg_one_mul]
        | succ m' ih =>
          show -(n + (nsmulRec (succ m') n)) = -((m' + 1) + 1) * n
          have : -(nsmulRec (succ m') n) = -(m' + 1) * n := ih
          rw [Int.neg_add, this]
          simp [add_mul]
          apply Int.neg_eq_neg_one_mul
          -- ring -- possible bug in `ring`