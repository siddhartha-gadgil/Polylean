import Polylean.GardamGroup
import Mathlib.Algebra.GroupPower.Basic

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

section TorsionFree

/-- the definition of a torsion-free group -/
class TorsionFree (G : Type _) [Group G] where
  torsion_free : ∀ g : G, ∀ n : ℕ, g ^ n.succ = 1 → g = 1

/-- the definition of torsion free additive groups -/
class AddTorsionFree (A : Type _) [AddGroup A] where
  torsion_free : ∀ a : A, ∀ n : ℕ, n.succ • a = 0 → a = 0

/-- ℤ is torsion-free, since it is an integral domain. -/
instance : AddTorsionFree ℤ where
  torsion_free := by
    intro a n (h : n.succ * a = 0)
    cases Int.mul_eq_zero.mp h with
    | inl hyp => injection hyp; contradiction
    | inr _ => assumption

/-- The product of torsion-free additive groups is torsion-free. -/
instance {A B : Type _} [AddGroup A] [AddGroup B] [AddTorsionFree A] [AddTorsionFree B] : AddTorsionFree (A × B) where
  torsion_free := by
    intro (a, b) n
    rw [show n.succ • (a, b) = (n.succ • a, n.succ • b) from rfl, Prod.ext_iff, Prod.ext_iff]
    intro ⟨_, _⟩; apply And.intro <;> 
      (apply AddTorsionFree.torsion_free; assumption)

/-- An additive group isomorphic to a torsion-free additive group is torsion-free. -/
instance iso_torsion_free {A B : Type _} [AddGroup A] [AddGroup B] (isoAB : A ≃+ B) [AddTorsionFree A] : AddTorsionFree B where
  torsion_free := by sorry

end TorsionFree


open P


/-- the function taking an element of `P` to its square, which lies in the kernel `K` -/
def s : P → (Metabelian.Kernel K Q)
  | ((p, q, r), (⟨0, _⟩, ⟨0, _⟩)) => ⟨((p + p, q + q, r + r), (⟨0, _⟩, ⟨0, _⟩)), rfl⟩
  | ((p, q, r), (⟨0, _⟩, ⟨1, _⟩)) => ⟨((0, q + q + 1, 0), (⟨0, _⟩, ⟨0, _⟩)), rfl⟩
  | ((p, q, r), (⟨1, _⟩, ⟨0, _⟩)) => ⟨((p + p + 1, 0, 0), (⟨0, _⟩, ⟨0, _⟩)), rfl⟩
  | ((p, q, r), (⟨1, _⟩, ⟨1, _⟩)) => ⟨((0, 0, r + r + 1), (⟨0, _⟩, ⟨0, _⟩)), rfl⟩

/-- proof that the above function satsifies the property of taking an element to its square -/
theorem s_square : ∀ g : P, g ^ 2 = (s g).val := by
  sorry 
  /- intro ((p, q, r), x); revert x
  have square_mul {G : Type} [Group G] (g : G) : g ^ 2 = g * g := by
    show g ^ (Nat.succ 1) = g * g; rw [pow_succ, pow_one
  fin_cases
  apply Q.rec <;> rw [s, square_mul, Pmul] <;> reduceGoal <;> simp only [id, DirectSum.add, add_zero, add_neg_self] <;> rfl -/

/-- ℤ³ is torsion-free -/
instance K.torsionfree : AddTorsionFree K := inferInstance

/-- The kernel subgroup of `P` is isomorphic to `ℤ³`-/
-- instance K.isokernel : K ≃+ (Metabelian.Kernel Q K) := inferInstance

-- /-- the kernel is torsion-free, as a corollary -/
-- instance kernel_torsion_free : AddTorsionFree (Metabelian.Kernel Q K) := inferInstance
-- @iso_torsion_free (ℤ × ℤ × ℤ) (Metabelian.Kernel Q K) _ _ isoℤ3kernel torsionfreeℤ3

-- /-- a proof that an odd integer must be non-zero -/
lemma odd_ne_zero : {a : ℤ} → ¬(a + a + 1 = 0)
  | .ofNat x => sorry
  | .negSucc x => sorry

/-- the only element of `P` with order dividing `2` is the identity -/
theorem square_free : ∀ g : P, g ^ 2 = 1 → g = 1 := by sorry
  /- intro ⟨(p, q, r), x⟩
  rw [s_square]

  apply Q.rec (λ x => ((p, q, r), x) ^ 2 = ((0, 0, 0), _) → ((p, q, r), x) = ((0, 0, 0), _))
  <;> rw [s_square, s] <;> simp only [subType.val, prod_eq, zero_of_double_zero, and_false, and_true, true_and] <;> try (apply odd_ne_zero)
  . exact id

  where
    zero_of_double_zero : ∀ m : ℤ, m + m = 0 ↔ m = 0 := by
    sorry
    intro m; apply Iff.intro
    · have : m + m = (Int.ofNat Nat.zero.succ.succ) • m := by show m + m = m + (m + 0); rw [add_zero]
      rw [this]; apply TorsionFreeAdditive.torsion_free
    · intro h; rw [h, add_zero] -/

/-- If `g` is a torsion element, so is `g ^ 2`. -/
theorem torsion_implies_square_torsion : ∀ g : P, ∀ n : ℕ, g ^ n = 1 → (g ^ 2) ^ n = 1 :=
  λ g n g_tor =>
    calc (g ^ 2) ^ n = g ^ (2 * n) := by rw [← pow_mul]
              _      = g ^ (n * 2) := by rw [mul_comm]
              _      = (g ^ n) ^ 2 := by rw [pow_mul]
              _      = (1 : P) ^ 2 := by rw [← g_tor]
              _      = (1 : P)     := by simp


/-- `P` is torsion-free -/
instance P_torsion_free : TorsionFree P where
  torsion_free := by sorry
    /- intros g n g_tor -- assume `g` is a torsion element
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
    have mul_to_add (a : Metabelian.Kernel Q K) (n : ℕ) : a ^ n = n • a := by
      induction n with | zero => rfl | succ m ih => rw [pow_succ'', ih]; rfl
    rw [mul_to_add] at s_tor
    -- since `s g` lies in the kernel and the kernel is torsion-free, `s g = 0`
    have square_zero : (s g).val = (0 : Metabelian.Kernel Q K).val := congrArg _ (kernel_torsion_free.torsion_free _ n s_tor)
    rw [← s_square] at square_zero
    -- this means `g ^ 2 = e`, and also `g = e` because `P` has no order 2 elements
    exact square_free g square_zero -/