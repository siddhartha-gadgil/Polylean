import Polylean.GardamGroup

/-
This file contains a proof that the group `P` defined is in fact torsion-free.
 .
Roughly, the steps are as follows (further details can be found in the corresponding `.md` file):
1. Define a function `s : Q -> K -> K` taking a group element `(q, k)` to its square `(s q k, 0)`. This element lies in the kernel as the group `ℤ₂ × ℤ₂` is annihilated by `2`.
2. Show that elements of the form `((a, b, c), (0, 0))` do not have torsion. This argument requires proving (something very close to) the fact that `ℤ` is an integral domain.
3. Show that no element of `P` has order precisely `2`. This is an argument by cases on the `Q` part of elements of `P`.
4. Finally, if an element `g : P` is in the kernel of the `n`-th power homomorphism, then so is `g^2`. But from the above statements, we see that `g^2` is of the form `(k, 0)` and hence
   either `g^2 = e` or `n = 0` (as elements of this form cannot have torsion). If `g^2 = e`, then `g = e` as `P` does not contain any order `2` elements. Otherwise, `n = 0`.
5. Together, this shows that `P` is torsion-free.
-/

open P

def s : K → Q → K
  | (p, q, r), (⟨0, _⟩, ⟨0, _⟩) => (p + p, q + q, r + r)
  | (p, q, r), (⟨0, _⟩, ⟨1, _⟩) => (0, q + q + 1, 0)
  | (p, q, r), (⟨1, _⟩, ⟨0, _⟩) => (p + p + 1, 0, 0)
  | (p, q, r), (⟨1, _⟩, ⟨1, _⟩) => (0, 0, r + r + 1)

theorem s_square : ∀ g : P, g ^ 2 = (s g.fst g.snd, (⟨0, by decide⟩, ⟨0, by decide⟩)) := by
  intro ((p, q, r), x); revert x
  apply Q.rec <;> rw [← npow_eq_pow] <;>
  simp [s, Monoid.npow, npow_rec, P_mul] <;> simp [action, cocycle, prod, id, neg] <;> simp [K_add]


def torsion_free (G : Type _) [Group G] (g : G) := ∀ n : ℕ, g ^ n.succ = 1 → g = 1

/- -- eventually switch to this definition
class TorsionFree (G : Type _) [Group G] :=
  torsion_free : ∀ g : G, ∀ n : ℕ, g ^ n.succ = 1 → g = 1
-/

-- this is the most difficult part of the argument
theorem kernel_torsion_free : ∀  k : K, torsion_free P (k, 0) := sorry

section Mod2

def Nat.mod2 : ℕ → Fin 2
  | Nat.zero => ⟨0, by decide⟩
  | Nat.succ Nat.zero => ⟨1, by decide⟩
  | Nat.succ (Nat.succ n) => mod2 n

def Int.mod2 : ℤ → Fin 2
  | Int.ofNat n => n.mod2
  | Int.negSucc n => n.succ.mod2

theorem mod2_succ : ∀ n : ℕ, n.succ.mod2 = (1 : Fin 2) + n.mod2
  | Nat.zero => rfl
  | Nat.succ Nat.zero => rfl
  | Nat.succ (Nat.succ n) => by rw [Nat.mod2, Nat.mod2, ← Nat.succ_eq_add_one, mod2_succ n]

theorem Nat.mod2_add_dist : ∀ m n : ℕ, Nat.mod2 (m + n) = Nat.mod2 m + Nat.mod2 n
  | Nat.zero, Nat.zero => rfl
  | Nat.zero, Nat.succ _ => by
    simp [mod2, add_zero]
    show _ = (0 : Fin 2) + _
    rw [AddMonoid.zero_add]
  | Nat.succ _, Nat.zero => by
    simp [mod2, zero_add]
    show _ = _ + (0 : Fin 2)
    rw [AddMonoid.add_zero]
  | Nat.succ a, Nat.succ b => by
    rw [Nat.add_succ, Nat.succ_add, mod2, mod2_add_dist a b, mod2_succ, mod2_succ]
    rw [add_assoc, ← add_assoc _ 1 _, add_comm _ 1, ← add_assoc 1 _ _, ← add_assoc 1 _ _]
    have : (1 : Fin 2) + (1 : Fin 2) = (0 : Fin 2) := rfl
    rw [this, AddMonoid.zero_add]

theorem Int.mod2_add_dist_cross : ∀ m n : ℕ, Int.mod2 (Int.ofNat m + Int.negSucc n) = Nat.mod2 m + ((1 : Fin 2) + Nat.mod2 n)
  | Nat.zero, Nat.zero => rfl
  | Nat.succ a, Nat.zero => by
    rw [← add_assoc _ 1 _, add_comm _ 1, ← mod2_succ]; show _ = Nat.mod2 a + (0 : Fin 2)
    have : Int.ofNat (Nat.succ a) + Int.negSucc Nat.zero = Int.ofNat a := by rw [ofNat_succ, negSucc_ofNat_eq, ofNat_zero, zero_add, add_assoc, add_neg_self, add_zero]
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

theorem odd_ne_zero : {a : ℤ} → ¬(a + a + 1 = 0) := by
  intro a
  intro h
  have hyp := congrArg Int.mod2 h
  rw [Int.mod2_add_dist, Int.mod2_add_dist] at hyp
  have : (Int.mod2 a + Int.mod2 a) = (0 : Fin 2) :=
    match (Int.mod2 a) with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
  rw [this, AddMonoid.zero_add] at hyp
  contradiction

end Mod2

theorem square_free : ∀ g : P, g ^ 2 = 1 → g = 1 := by
  intro ⟨(p, q, r), x⟩
  apply Q.rec (λ x => ((p, q, r), x) ^ 2 = ((0, 0, 0), (⟨0, _⟩, ⟨0, _⟩)) → ((p, q, r), x) = ((0, 0, 0), (⟨0, _⟩, ⟨0, _⟩)))
  <;> rw [s_square, s] <;> simp <;> intro hyp <;> (try (exact odd_ne_zero hyp))
  · sorry -- showing `p + p = 0 → p = 0` needs the fact that ℤ is an integral domain

theorem torsion_implies_square_torsion : ∀ g : P, ∀ n : ℕ, g ^ n = 1 → (g ^ 2) ^ n = 1 :=
  λ g n g_tor =>
    calc (g ^ 2) ^ n = g ^ (2 * n) := by rw [← pow_mul]
              _      = g ^ (n * 2) := by rw [mul_comm]
              _      = (g ^ n) ^ 2 := by rw [pow_mul]
              _      = (1 : P) ^ 2 := by rw [← g_tor]
              _      = (1 : P)     := rfl

  theorem P_torsion_free : ∀ g : P, torsion_free P g := by
    intros g n g_tor
    have square_tor : (g ^ 2) ^ n.succ = 1 := torsion_implies_square_torsion g n.succ g_tor
    have square_eq : g ^ 2 = (s g.fst g.snd, 0) := s_square g
    rw [square_eq] at square_tor
    have square_zero : (s g.fst g.snd, (⟨0, by decide⟩, ⟨0, by decide⟩)) = ((0, 0) : P) := kernel_torsion_free (s g.fst g.snd) n square_tor
    rw [← s_square] at square_zero
    exact square_free g square_zero
