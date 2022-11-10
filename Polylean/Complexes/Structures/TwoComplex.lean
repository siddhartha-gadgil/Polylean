import Polylean.Complexes.Structures.Groupoid

/-! 
  A two-complex is defined in terms of two pieces of data:
  - An underlying 1-complex, which is a `Quiver` (or `SerreGraph`)
  - A groupoid, whose morphisms represent the path-homotopy classes of the 1-complex
  - A `PreFunctor` from the `Quiver` to the `Groupoid`, sending each edge of the quiver to its path-homotopy class 
    (this pre-functor has a natural extension to the path category of the quiver)
  
  A further requirement is that the groupoid does not contain any "extra" edges, i.e., that the pre-functor is surjective.
  This can be re-stated in the form of a "recursion principle" that allows certain maps from the quiver to lift to maps from the groupoid.
 -/
class TwoComplex (V : Sort _) [Q : Quiver V] [H : Groupoid V] extends Quiver.PreFunctor Q H.toQuiver where
  lift : {W : Sort _} → [G : Groupoid W] → (F : Quiver.PreFunctor Q G.toQuiver) → 
    (∀ {X Y : V} {e e' : X ⟶ Y}, map e = map e' → F.map e = F.map e') →
      Groupoid.Functor H G
  lift_comp : {W : Sort _} → [G : Groupoid W] → (F : Quiver.PreFunctor Q G.toQuiver) → 
    (h : ∀ {X Y : V} {e e' : X ⟶ Y}, map e = map e' → F.map e = F.map e') →
      Quiver.PreFunctor.comp ⟨obj, map⟩ (lift F h).toPreFunctor = F