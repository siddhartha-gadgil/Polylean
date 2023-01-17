import UnitConjecture.FreeAbelianGroup

def induced_map {A : Type _} [AddCommGroup A] (x y z : A) : ℤ × ℤ × ℤ → A :=
 let f : Unit ⊕ Unit ⊕ Unit → A := (fun | Sum.inl _ => x | Sum.inr (Sum.inl _) => y | Sum.inr (Sum.inr _) => z)
 FreeAbelianGroup.inducedMap A f

theorem induced_ext {A : Type _} [AddCommGroup A] (x y z : A) :  ((induced_map x y z) (1, 0, 0) = x ∧ (induced_map x y z) (0, 1, 0) = y ∧ (induced_map x y z) (0, 0, 1) = z) :=
  let f : Unit ⊕ Unit ⊕ Unit → A := (fun | Sum.inl _ => x | Sum.inr (Sum.inl _) => y | Sum.inr (Sum.inr _) => z)
  let f_extends := FreeAbelianGroup.induced_extends f
  ⟨congrFun f_extends (Sum.inl ()), congrFun f_extends (Sum.inr (Sum.inl ())), congrFun f_extends (Sum.inr (Sum.inr ()))⟩

instance ind_hom {A : Type _} [AddCommGroup A] {x y z : A} : AddCommGroup.Homomorphism (induced_map x y z) := FreeAbelianGroup.induced_hom A _


def ν (A : Type) [AddCommGroup A] (x y z : A) := x + y + z + (-x + -z) = y

theorem eqn_iff_free_basis : (∀ (A : Type) [AddCommGroup A], ∀ x y z : A, (ν A x y z)) ↔ (ν (ℤ × ℤ × ℤ) (1, 0, 0) (0, 1, 0) (0, 0, 1)) := by
  apply Iff.intro
  · intro h
    apply h
  · intro h
    intro A _ x y z
    let ⟨hx, hy, hz⟩ := induced_ext x y z
    have eqn := congrArg (induced_map x y z) h
    simp only [AddCommGroup.Homomorphism.add_dist, AddCommGroup.Homomorphism.neg_push, hx, hy, hz] at eqn
    assumption

theorem eqn_check : ∀ (A : Type) [AddCommGroup A], ∀ x y z : A, ν A x y z :=
  Iff.mpr eqn_iff_free_basis rfl
