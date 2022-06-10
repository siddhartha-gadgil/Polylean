import Polylean.FreeAbelianGroup

abbrev e₁ : ℤ × ℤ × ℤ := (1, 0, 0)
abbrev e₂ : ℤ × ℤ × ℤ := (0, 1, 0)
abbrev e₃ : ℤ × ℤ × ℤ := (0, 0, 1)

instance ℤ3Free : FreeAbelianGroup (ℤ × ℤ × ℤ) (Unit ⊕ Unit ⊕ Unit) := inferInstance

def induced_map {A : Type _} [AddCommGroup A] (x y z : A) : ℤ × ℤ × ℤ → A :=
 let f : Unit ⊕ Unit ⊕ Unit → A := (fun | Sum.inl _ => x | Sum.inr (Sum.inl _) => y | Sum.inr (Sum.inr _) => z)
 FreeAbelianGroup.inducedMap A f

theorem induced_ext {A : Type _} [AddCommGroup A] (x y z : A) (ϕ : ℤ × ℤ × ℤ → A) (h : ϕ = induced_map x y z) :  (ϕ (1, 0, 0) = x ∧ ϕ (0, 1, 0) = y ∧ ϕ (0, 0, 1) = z) :=
  let f : Unit ⊕ Unit ⊕ Unit → A := (fun | Sum.inl _ => x | Sum.inr (Sum.inl _) => y | Sum.inr (Sum.inr _) => z)
  let f_extends := ℤ3Free.induced_extends f
  ⟨h ▸ congrFun f_extends (Sum.inl ()), h ▸ congrFun f_extends (Sum.inr (Sum.inl ())), h ▸ congrFun f_extends (Sum.inr (Sum.inr ()))⟩

instance ind_hom {A : Type _} [AddCommGroup A] {x y z : A} : AddCommGroup.Homomorphism (induced_map x y z) := ℤ3Free.induced_hom A _

example : (∀ (A : Type _) [AddCommGroup A], ∀ x y z : A, x + y + z + (-x + -z) = y) ↔ (e₁ + e₂ + e₃ + (-e₁ + -e₃) = e₂) := by
  apply Iff.intro
  · intro h
    apply h
  · intro h
    intro A _ x y z
    let ϕ := induced_map x y z
    let ⟨hx, hy, hz⟩ := induced_ext x y z ϕ rfl
    have eqn := congrArg ϕ h
    simp only [AddCommGroup.Homomorphism.add_dist, AddCommGroup.Homomorphism.neg_push, hx, hy, hz] at eqn
    assumption
