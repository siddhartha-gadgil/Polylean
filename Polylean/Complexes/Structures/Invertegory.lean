import Polylean.Complexes.Structures.Category

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

@[simp] protected def Invertegory.Functor.id (C : Sort _) [ℭ : Invertegory C] : Invertegory.Functor ℭ ℭ :=
-- TODO Use `..` notation
 { obj := id, map := id, mapId := λ _ => rfl, mapComp := λ _ _ => rfl, mapInv := rfl }

@[simp] def Invertegory.Functor.comp {C D E : Sort _} {ℭ : Invertegory C} {𝔇 : Invertegory D} {𝔈 : Invertegory E} (F : Invertegory.Functor ℭ 𝔇) (G : Invertegory.Functor 𝔇 𝔈) : Invertegory.Functor ℭ 𝔈 :=
-- TODO Use `..` notation
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map, mapId := by intro; simp, mapComp := by intros; simp, mapInv := by intros; simp }