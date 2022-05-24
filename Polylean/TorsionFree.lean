import Polylean.GardamGroup

/-
This file contains a proof that the group `P` defined is in fact torsion-free.

Roughly, the steps are as follows (further details can be found in the corresponding `.md` file):
1. Define a function `s : Q -> K -> K` taking a group element `(q, k)` to its square `(s q k, 0)`. This element lies in the kernel as the group `ℤ₂ × ℤ₂` is annihilated by `2`.
2. Show that elements of the form `((a, b, c), (0, 0))` do not have torsion. This argument requires proving (something very close to) the fact that `ℤ` is an integral domain.
3. Show that no element of `P` has order precisely `2`. This is an argument by cases on the `Q` part of elements of `P`.
4. Finally, if an element `g : P` is in the kernel of the `n`-th power homomorphism, then so is `g^2`. But from the above statements, we see that `g^2` is of the form `(k, 0)` and hence
   either `g^2 = e` or `n = 0` (as elements of this form cannot have torsion). If `g^2 = e`, then `g = e` as `P` does not contain any order `2` elements. Otherwise, `n = 0`.
5. Together, this shows that `P` is torsion-free.
-/

open P

def s : K → Q → K := sorry

theorem s_square : ∀ g : P, g * g = (s g.fst g.snd, 0) := sorry

-- needs slight rewording
def torsion_free (G : Type _) [Group G] (g : G) := ∀ n : ℕ, g ^ n.succ = 1 → g = 1

-- this is the most difficult part of the argument
theorem kernel_torsion_free : ∀ k : K, torsion_free P (k, 0) := sorry

theorem square_free : ∀ g : P, g * g = 1 → g = 1 := by
  intro ⟨k, q⟩
  revert q
  apply Q.rec (λ q => (k, q) * (k, q) = (0, 0) → (k, q) = (0, 0)) <;> intro hyp <;> simp
  · let g : P := (k, 0)
    have metabelian_mul : g * g = (k + (0 : Q) • k + cocycle 0 0, 0) := rfl
    rw [P_cocycle.cocycleId, add_zero, P_action.id_action] at metabelian_mul
    have : g = (k, (⟨0, by decide⟩, ⟨0, by decide⟩))  := rfl
    rw [← this] at hyp
    have : k + k = 0 := congrArg Prod.fst (Eq.trans (Eq.symm metabelian_mul) hyp)
    sorry -- completing this proof requires the fact that `K` is torsion-free
    sorry
  · sorry
  · sorry
  · sorry

theorem torsion_implies_square_torsion : ∀ g : P, ∀ n : ℕ, g ^ n = 1 → (g ^ 2) ^ n = 1 := sorry

theorem P_torsion_free : ∀ g : P, torsion_free P g := sorry
