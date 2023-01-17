import Complexes.Structures.Category

/-- An `Invertegory` is meant to be an intermediate between a `Category` and a `Groupoid`. 
  It is a category in which every morphism has a formal inverse, but the inverse is not required to satisfy any properties. 
  This is not a standard construction in the literature. -/
class Invertegory (Obj : Sort _) extends Category Obj where
  inv : {X Y : Obj} → (X ⟶ Y) → (Y ⟶ X)
  invInv : ∀ e : X ⟶ Y, inv (inv e) = e

/-- `Invertegory.Functor` is a morphism of `Invertegories` that preserves inverses. -/
structure Invertegory.Functor {C D : Sort _} (ℭ : Invertegory C) (𝔇 : Invertegory D) extends Category.Functor ℭ.toCategory 𝔇.toCategory where
  mapInv : {X Y : C} → {f : X ⟶ Y} → map (Invertegory.inv f) = Invertegory.inv (map f)

attribute [simp] Invertegory.Functor.mapInv