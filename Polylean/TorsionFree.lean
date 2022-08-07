import Polylean.GardamGroup
import Polylean.IntDomain
import Polylean.ModArith
import Polylean.Tactics.ReduceGoal

/-!
## Torsion-freeness of `P`

This file contains a proof that the group `P` defined is in fact torsion-free.

Roughly, the steps are as follows (further details can be found in the corresponding `.md` file):
1. Define a function `s : Q -> K -> K` taking a group element `(q, k)` to its square `(s q k, 0)`. This element lies in the kernel as the group `ℤ₂ × ℤ₂` is annihilated by `2`.
2. Show that elements of the form `((a, b, c), (0, 0))` do not have torsion. This argument requires proving (something very close to) the fact that `ℤ` is an integral domain.
3. Show that no element of `P` has order precisely `2`. This is an argument by cases on the `Q` part of elements of `P`.
4. Finally, if an element `g : P` is in the kernel of the `n`-th power homomorphism, then so is `g^2`. But from the above statements, we see that `g^2` is of the form `(k, 0)` and hence
   either `g^2 = e` or `n = 0` (as elements of this form cannot have torsion). If `g^2 = e`, then `g = e` as `P` does not contain any order `2` elements. Otherwise, `n = 0`.
5. Together, this shows that `P` is torsion-free.
-/

section TorsionFree

/-- A typeclass for torsion-free groups -/
class TorsionFree (G : Type _) [Group G] where
  torsion_free : ∀ g : G, ∀ n : ℕ, g ^ n.succ = 1 → g = 1

/-- A typeclass for torsion-free *additive* groups -/
class TorsionFreeAdditive (A : Type _) [AddCommGroup A] where
  torsion_free : ∀ a : A, ∀ n : ℕ, n.succ • a = 0 → a = 0

/-- ℤ is torsion-free, since it is an integral domain -/
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

/-- The product of torsion-free groups is torsion-free -/
instance {A B : Type _} [AddCommGroup A] [AddCommGroup B] [TorsionFreeAdditive A] [TorsionFreeAdditive B] :
  TorsionFreeAdditive (A × B) where
  torsion_free := by
    intro (a, b) n
    rw [DirectSum.scal_mul_pair a b (Nat.succ n), DirectSum.zero_pair, prod_eq, prod_eq]
    intro ⟨_, _⟩; apply And.intro <;> (apply TorsionFreeAdditive.torsion_free; assumption)

/-- A group isomorphic to a torsion-free group is torsion-free -/
instance iso_torsion_free {A B : Type _} [AddCommGroup A] [AddCommGroup B] [IsoAB : AddCommGroup.Isomorphism A B] [TorsionFreeAdditive A] : TorsionFreeAdditive B where
  torsion_free := by
    intro b n h
    have : n.succ • (IsoAB.inv b) = 0 := by rw [hom_mul, h]; simp
    have : (IsoAB.map ∘ IsoAB.inv) b = IsoAB.map 0 := congrArg IsoAB.map $ TorsionFreeAdditive.torsion_free (IsoAB.inv b) n this
    rw [IsoAB.idTgt] at this; simp at this
    assumption

end TorsionFree


open P


/-- The function taking an element of the group `P` to its square, which lies in the kernel `K` -/
def s : P → (Metabelian.Kernel Q K)
  | ((p, q, r), e ) => ⟨((p + p, q + q, r + r), e), rfl⟩
  | ((p, _, _), a ) => ⟨((p + p + 1, 0, 0), e), rfl⟩
  | ((_, q, _), b ) => ⟨((0, q + q + 1, 0), e), rfl⟩
  | ((_, _, r), ab) => ⟨((0, 0, r + r + 1), e), rfl⟩


lemma square_mul {G : Type} [Group G] (g : G) : g ^ 2 = g * g := by
  show g ^ (Nat.succ 1) = g * g; rw [pow_succ, pow_one]

/-- A proof that the function `s` takes an element of `P` to its square -/
theorem s_square : ∀ g : P, g ^ 2 = (s g).val := by
  intro ((p, q, r), x)
  cases x using Q.rec <;>
  rw [s, square_mul, Pmul] <;> reduceGoal <;> simp only [id, DirectSum.add, add_zero, add_neg_self] <;> rfl


/-- ℤ³ is torsion-free -/
instance torsionfreeℤ3 : TorsionFreeAdditive K := inferInstance

/-- The kernel subgroup `K` of `P` is isomorphic to `ℤ³`-/
instance isoℤ3kernel : AddCommGroup.Isomorphism K (Metabelian.Kernel Q K) := inferInstance

/-- The subgroup `K` of `P` is torsion-free -/
instance kernel_torsion_free : TorsionFreeAdditive (Metabelian.Kernel Q K) := inferInstance
-- @iso_torsion_free (ℤ × ℤ × ℤ) (Metabelian.Kernel Q K) _ _ isoℤ3kernel torsionfreeℤ3


/-- The only element of `P` with order dividing `2` is the identity -/
theorem square_free : ∀ g : P, g ^ 2 = 1 → g = 1 := by
  intro ⟨(p, q, r), x⟩
  cases x using Q.rec <;>
  rw [P.one, s_square, s] <;> simp only [subType.val, prod_eq, zero_of_double_zero, and_false, and_true, true_and]
  <;> try (first | apply odd_ne_zero | apply id)

/-- If `g` is a torsion element, so is `g ^ 2` -/
theorem torsion_implies_square_torsion : ∀ g : P, ∀ n : ℕ, g ^ n = 1 → (g ^ 2) ^ n = 1 :=
  fun g n g_tor =>
    calc (g ^ 2) ^ n = g ^ (2 * n) := by rw [← pow_mul]
              _      = g ^ (n * 2) := by rw [mul_comm]
              _      = (g ^ n) ^ 2 := by rw [pow_mul]
              _      = (1 : P) ^ 2 := by rw [← g_tor]
              _      = (1 : P)     := rfl


/-- The group `P` is torsion-free -/
instance P_torsion_free : TorsionFree P where
  torsion_free := by
    intros g n g_tor -- assume `g` is a torsion element
    -- then `g ^ 2` is also a torsion element
    have square_tor : (g ^ 2) ^ n.succ = 1 := torsion_implies_square_torsion g n.succ g_tor
    rw [s_square] at square_tor
    -- since `g ^ 2 = s g`, we have that `s g` is a torsion element
    have s_tor : (s g) ^ n.succ = 1 := by
      apply subType.eq_of_val_eq; rw [← subType.hom_pow, square_tor]
    rw [mul_to_add] at s_tor -- converting from multiplicative to additive notation
    -- since `s g` lies in the kernel and the kernel is torsion-free, `s g = 0`
    have square_zero : (s g).val = (0 : Metabelian.Kernel Q K).val := congrArg _ (kernel_torsion_free.torsion_free _ n s_tor)
    rw [← s_square] at square_zero
    -- this means `g ^ 2 = e`, and also `g = e` because `P` has no order 2 elements
    exact square_free g square_zero

