import Polylean.GardamGroup
import Polylean.IntDomain


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

-- the definition of a torsion-free group
class TorsionFree (G : Type _) [Group G] where
  torsion_free : ∀ g : G, ∀ n : ℕ, g ^ n.succ = 1 → g = 1

-- the same definition for additive groups
class TorsionFreeAdditive (A : Type _) [AddCommGroup A] where
  torsion_free : ∀ a : A, ∀ n : ℕ, SubNegMonoid.gsmul n.succ a = 0 → a = 0

-- ℤ is torsion-free, since it is an integral domain
instance : TorsionFreeAdditive ℤ where
  torsion_free := by
    intro a n
    show n.succ * a = 0 → a = 0
    intro h
    cases (int_domain _ _) h with
      | inl hyp =>
        have : Nat.succ n = (0 : Nat) := by injection hyp; assumption
        contradiction
      | inr _ => assumption

-- the product of torsion-free groups is torsion-free
instance {A B : Type _} [AddCommGroup A] [AddCommGroup B] [TorsionFreeAdditive A] [TorsionFreeAdditive B] :
  TorsionFreeAdditive (A × B) where
  torsion_free := by
    intro (a, b) n
    have : ∀ m : ℕ, SubNegMonoid.gsmul m (a, b) = (SubNegMonoid.gsmul m a, SubNegMonoid.gsmul m b) := by
      intro m
      induction m with
        | zero => simp [SubNegMonoid.gsmul_zero']; rfl
        | succ m ih => rw [← Int.ofNat_eq_cast, SubNegMonoid.gsmul_succ', Int.ofNat_eq_cast, ih, SubNegMonoid.gsmul_succ', SubNegMonoid.gsmul_succ', ← DirectSum.directSum_add]; rfl
    show (SubNegMonoid.gsmul n.succ (a, b)) = (0, 0) → ((a, b) = (0, 0))
    rw [this]; simp
    intro ha hb
    apply And.intro <;> apply TorsionFreeAdditive.torsion_free <;> assumption

-- a group isomorphic to a torsion-free group is torsion-free
instance iso_torsion_free {A B : Type _} [AddCommGroup A] [AddCommGroup B] [IsoAB : AddCommGroup.Isomorphism A B] [TorsionFreeAdditive A] : TorsionFreeAdditive B where
  torsion_free := by
    intro b n h
    have : SubNegMonoid.gsmul n.succ (IsoAB.inv b) = 0 := by rw [hom_mul, h, @zero_image B A _ _ IsoAB.inv IsoAB.invHom]
    have : (IsoAB.map ∘ IsoAB.inv) b = IsoAB.map 0 := congrArg IsoAB.map $ TorsionFreeAdditive.torsion_free (IsoAB.inv b) n this
    rw [IsoAB.idTgt, @zero_image A B _ _ IsoAB.map IsoAB.mapHom] at this
    assumption

open P

-- the function taking an element of `P` to its square, which lies in the kernel `K`
def s : P → (Metabelian.Kernel Q K)
  | ((p, q, r), (⟨0, _⟩, ⟨0, _⟩)) => ⟨((p + p, q + q, r + r), (⟨0, _⟩, ⟨0, _⟩)), rfl⟩
  | ((p, q, r), (⟨0, _⟩, ⟨1, _⟩)) => ⟨((0, q + q + 1, 0), (⟨0, _⟩, ⟨0, _⟩)), rfl⟩
  | ((p, q, r), (⟨1, _⟩, ⟨0, _⟩)) => ⟨((p + p + 1, 0, 0), (⟨0, _⟩, ⟨0, _⟩)), rfl⟩
  | ((p, q, r), (⟨1, _⟩, ⟨1, _⟩)) => ⟨((0, 0, r + r + 1), (⟨0, _⟩, ⟨0, _⟩)), rfl⟩

-- proof that the above function satsifies the property of taking an element to its square
theorem s_square : ∀ g : P, g ^ 2 = (s g).val := by
  intro ((p, q, r), x); revert x
  apply Q.rec <;> rw [← npow_eq_pow] <;>
  simp [s, Monoid.npow, npow_rec, P_mul] <;> simp [action, cocycle, prod, id, neg]

-- ℤ³ is torsion-free
instance torsionfreeℤ3 : TorsionFreeAdditive K := inferInstance

-- The kernel subgroup of `P` is isomorphic to `ℤ³`
instance isoℤ3kernel : AddCommGroup.Isomorphism K (Metabelian.Kernel Q K) := inferInstance

-- the kernel is torsion-free, as a corollary
instance kernel_torsion_free : TorsionFreeAdditive (Metabelian.Kernel Q K) := inferInstance
-- @iso_torsion_free (ℤ × ℤ × ℤ) (Metabelian.Kernel Q K) _ _ isoℤ3kernel torsionfreeℤ3

section Mod2

/-
This section sets up the `modulo 2` homomorphism `ℤ → ℤ/2ℤ`.
-/

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

-- a proof that an odd integer must be non-zero
theorem odd_ne_zero : {a : ℤ} → ¬(a + a + 1 = 0) := by
  intro a h
  have hyp := congrArg Int.mod2 h
  have : ∀ x : Fin 2, x + x = (0 : Fin 2) := fun | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
  simp [this] at hyp

end Mod2

-- the only element of `P` with order dividing `2` is the identity
theorem square_free : ∀ g : P, g ^ 2 = 1 → g = 1 := by
  intro ⟨(p, q, r), x⟩
  apply Q.rec (λ x => ((p, q, r), x) ^ 2 = ((0, 0, 0), (⟨0, _⟩, ⟨0, _⟩)) → ((p, q, r), x) = ((0, 0, 0), (⟨0, _⟩, ⟨0, _⟩)))
  <;> rw [s_square, s] <;> simp <;> intros <;> (try (apply odd_ne_zero; assumption))

  have zero_of_double_zero : ∀ m : ℤ, m + m = 0 → m = 0 := by
    intro m; have : m + m = SubNegMonoid.gsmul (Int.ofNat Nat.zero.succ.succ) m := by rw [SubNegMonoid.gsmul_succ', add_left_cancel_iff, SubNegMonoid.gsmul_succ', Int.ofNat_zero, SubNegMonoid.gsmul_zero', add_zero]
    rw [this]; apply TorsionFreeAdditive.torsion_free

  apply And.intro <;> (try apply And.intro) <;> apply zero_of_double_zero <;> assumption

-- if `g` is a torsion element, so is `g ^ 2`
theorem torsion_implies_square_torsion : ∀ g : P, ∀ n : ℕ, g ^ n = 1 → (g ^ 2) ^ n = 1 :=
  λ g n g_tor =>
    calc (g ^ 2) ^ n = g ^ (2 * n) := by rw [← pow_mul]
              _      = g ^ (n * 2) := by rw [mul_comm]
              _      = (g ^ n) ^ 2 := by rw [pow_mul]
              _      = (1 : P) ^ 2 := by rw [← g_tor]
              _      = (1 : P)     := rfl

-- `P` is torsion-free
instance P_torsion_free : TorsionFree P where
  torsion_free := by
    intros g n g_tor -- assume `g` is a torsion element
    -- then `g ^ 2` is also a torsion element
    have square_tor : (g ^ 2) ^ n.succ = 1 := torsion_implies_square_torsion g n.succ g_tor
    rw [s_square] at square_tor
    -- since `g ^ 2 = s g`, we have that `s g` is a torsion element
    have s_tor : (s g) ^ n.succ = 1 := by
      apply subType.eq_of_val_eq
      have subType_hom_pow {G : Type _} [Group G] (P : G → Prop) [subGroup P] (a : subType P) (n : ℕ) : (subType.val P a) ^ n = subType.val P (a ^ n) :=
        Group.Homomorphism.hom_pow
      rw [← subType_hom_pow, square_tor]
    -- converting from multiplicative to additive notation
    have mul_to_add (a : Metabelian.Kernel Q K) (n : ℕ) : a ^ n = SubNegMonoid.gsmul (Int.ofNat n) a := by
      induction n with | zero => rfl | succ m ih => rw [pow_succ', SubNegMonoid.gsmul_succ', ih]; rfl
    rw [mul_to_add] at s_tor
    -- since `s g` lies in the kernel and the kernel is torsion-free, `s g = 0`
    have square_zero : (s g).val = (0 : Metabelian.Kernel Q K).val := congrArg _ (kernel_torsion_free.torsion_free _ n s_tor)
    rw [← s_square] at square_zero
    -- this means `g ^ 2 = e`, and also `g = e` because `P` has no order 2 elements
    exact square_free g square_zero
