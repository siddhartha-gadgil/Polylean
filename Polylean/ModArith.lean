import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.Group.Defs
import Aesop

/-
This section sets up the `modulo 2` homomorphism `ℤ → ℤ/2ℤ`.
-/

declare_aesop_rule_sets [ModArith]

@[aesop norm unfold (rule_sets [ModArith])]
def Int.modn (n : ℕ) [h : Fact (n ≠ 0)] : ℤ → Fin n
  | m => ⟨m.natMod n, Int.natMod_lt h.out⟩

@[aesop norm (rule_sets [ModArith])]
lemma mod2_succ : ∀ n : ℕ, (n.succ).mod2 = (1 : Fin 2) + n.mod2
  | 0 => rfl
  | 1 => rfl
  | .succ (.succ n) => by 
    have := mod2_succ n
    aesop (rule_sets [ModArith])

theorem Nat.mod2_add_dist : ∀ m n : ℕ, Nat.mod2 (m + n) = Nat.mod2 m + Nat.mod2 n
  | _, .zero => by aesop (rule_sets [ModArith])
  | a, .succ b => by
    rw [Nat.add_succ]
    simp only [mod2_succ]
    rw [Nat.mod2_add_dist a b, add_left_comm]

lemma Int.mod2_add_dist_cross : ∀ m n : ℕ, Int.mod2 (Int.ofNat m + Int.negSucc n) = Nat.mod2 m + ((1 : Fin 2) + Nat.mod2 n)
  | Nat.zero, Nat.zero => rfl
  | Nat.succ a, Nat.zero => by
    rw [← add_assoc _ 1 _, add_comm _ 1, ← mod2_succ]; show _ = Nat.mod2 a + (0 : Fin 2)
    have : Int.ofNat (Nat.succ a) + Int.negSucc Nat.zero = Int.ofNat a := by aesop
    rw [this, AddMonoid.add_zero]; rfl
  | Nat.zero, Nat.succ _ => by simp [mod2]; rw [← mod2_succ]; show _ = (0 : Fin 2) + _; rw [AddMonoid.zero_add]
  | Nat.succ a, Nat.succ b => by
    have : Int.ofNat a.succ + Int.negSucc b.succ = Int.ofNat a + Int.negSucc b := by rw [ofNat_succ, add_assoc, add_left_cancel_iff, negSucc_ofNat_coe', negSucc_ofNat_coe', sub_eq_add_neg, add_comm _ (-1), ← add_assoc, add_neg_self, zero_add, ofNat_succ, neg_hom, sub_eq_add_neg]
    rw [this, mod2_add_dist_cross a b, mod2_succ, mod2_succ]
    rw [add_assoc 1 _ _, ← add_assoc _ _ (1 + b.mod2), add_comm _ 1, add_assoc 1 a.mod2, ← add_assoc 1 1]
    have : 1 + 1 = (0 : Fin 2) := rfl; rw [this, AddMonoid.zero_add]

theorem Int.mod2_add_dist : ∀ m n : ℤ, Int.mod2 (m + n) = Int.mod2 m + Int.mod2 n
  | Int.ofNat m, Int.ofNat n => Nat.mod2_add_dist _ _
  | Int.ofNat m, Int.negSucc n => by rw [mod2_add_dist_cross]; simp [mod2]; rw [mod2_succ]
  | Int.negSucc m, Int.ofNat n => by rw [add_comm, mod2_add_dist_cross]; simp [mod2]; rw [add_comm, add_right_cancel_iff, mod2_succ]
  | Int.negSucc m, Int.negSucc n => by rw [Int.negSucc_ofNat_add_negSucc_ofNat]; simp [mod2]; rw [← Nat.succ_add, Nat.succ_add_eq_succ_add, ← Nat.succ_add, Nat.mod2_add_dist]

instance : AddCommGroup.Homomorphism (Int.mod2) where
  add_dist := Int.mod2_add_dist

end Mod2
