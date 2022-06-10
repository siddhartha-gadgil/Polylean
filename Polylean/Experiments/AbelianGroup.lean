import Polylean.FreeAbelianGroup

abbrev e₁ : ℤ × ℤ × ℤ := (1, 0, 0)
abbrev e₂ : ℤ × ℤ × ℤ := (0, 1, 0)
abbrev e₃ : ℤ × ℤ × ℤ := (0, 0, 1)

instance ℤ3Free : FreeAbelianGroup (ℤ × ℤ × ℤ) (Unit ⊕ Unit ⊕ Unit) := inferInstance

def induced_hom {A : Type _} [AddCommGroup A] (x y z : A) : {ϕ : ℤ × ℤ × ℤ → A // (ϕ (1, 0, 0) = x ∧ ϕ (0, 1, 0) = y ∧ ϕ (0, 0, 1) = z)} :=
 let f : Unit ⊕ Unit ⊕ Unit → A := (fun | Sum.inl _ => x | Sum.inr (Sum.inl _) => y | Sum.inr (Sum.inr _) => z)
 let f_extends := ℤ3Free.induced_extends f
 {
   val := FreeAbelianGroup.inducedMap A f
   property := ⟨congrFun f_extends (Sum.inl ()), congrFun f_extends (Sum.inr (Sum.inl ())), congrFun f_extends (Sum.inr (Sum.inr ()))⟩
 }

instance ind_hom {A : Type _} [AddCommGroup A] {x y z : A} : AddCommGroup.Homomorphism (induced_hom x y z).val := ℤ3Free.induced_hom A _

#check AddCommGroup.Homomorphism.add_dist

example : (∀ (A : Type _) [AddCommGroup A], ∀ x y z : A, x + y + z + (-x + -z) = y) ↔ (e₁ + e₂ + e₃ + (-e₁ + -e₃) = e₂) := by
  apply Iff.intro
  · intro h
    apply h
  · intro h
    intro A _ x y z
    let ⟨ϕ, ⟨hx, hy, hz⟩⟩ := induced_hom x y z
    let inst : AddCommGroup.Homomorphism ϕ := ℤ3Free.induced_hom A _
    have := congrArg ϕ h
    repeat (rw [← hx, ← hy, ← hz])
