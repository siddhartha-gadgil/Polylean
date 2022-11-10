import Polylean.Complexes.Structures.FreeGroupoid

instance Groupoid.Star {S : Sort _} [G : Groupoid S] (X : S) : Groupoid (Σ Y : S, X ⟶ Y) where
  hom := λ ⟨Y, g⟩ ⟨Z, h⟩ => {f : Y ⟶ Z // g ≫ f = h}
  id := λ {_} => ⟨𝟙, by simp⟩
  comp := λ ⟨g, gcomp⟩ ⟨h, hcomp⟩ => ⟨g ≫ h, by rw [← comp_assoc, gcomp, hcomp]⟩
  inv := λ ⟨g, gcomp⟩ => ⟨g⁻¹, by rw [← gcomp]; simp⟩

  id_comp := by
    intro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩
    apply Subtype.eq
    show 𝟙 ≫ _ = _
    simp      
  comp_id := by
    intro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩
    apply Subtype.eq
    show _ ≫ 𝟙 = _
    simp
  comp_assoc := by
    intro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩
    apply Subtype.eq
    show (_ ≫ _) ≫ _ = _ ≫ (_ ≫ _)
    simp
  inv_comp_id := by
    intro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩
    apply Subtype.eq
    show _⁻¹ ≫ _ = 𝟙
    simp
  comp_inv_id := by
    intro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩
    apply Subtype.eq
    show _ ≫ _⁻¹ = 𝟙
    simp

instance FreeGroupoid.UniversalQuiver 
    {S : Type _} [Q : Quiver S] [G : Groupoid S] (X : S) [FG : FreeGroupoid Q G]
    : Quiver (Σ Y : S, G.hom X Y) where
  hom := λ ⟨Y, g⟩ ⟨Z, h⟩ => {f : Q.hom Y Z // g ≫ (FG.map f) = h}

