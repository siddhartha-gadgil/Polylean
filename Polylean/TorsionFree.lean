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

-- needs slight rewording
def torsion_free (G : Type _) [Group G] (g : G) := ∀ n : ℕ, g ^ n.succ = 1 → g = 1

-- this is the most difficult part of the argument
theorem kernel_torsion_free : ∀  k : K, torsion_free P (k, 0) := sorry

theorem square_free : ∀ g : P, g ^ 2 = 1 → g = 1 := by
  intro ⟨(p, q, r), x⟩; revert x
  have sq (g : P) : g ^ 2 = g * g :=  by rw [← npow_eq_pow]; simp [Monoid.npow, npow_rec]
  apply Q.rec (λ x => ((p, q, r), x) ^ 2 = (0, 0) → ((p, q, r), x) = (0, 0))
  <;> intro hyp <;> rw [sq] at hyp <;> simp <;> rw [P_mul] at hyp <;> simp [action, cocycle, prod, id, neg, K_add] at hyp
  · sorry
  · sorry
  · sorry
  · sorry

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
