import Polylean.Complexes.Structures.Groupoid

/-- The definition of a free groupoid with basis `Q`. -/
class FreeGroupoid.Struct {S : Sort _} (Q : Quiver S) (G : Groupoid S) where
  map : {X Y : S} → (Q.hom X Y) → (G.hom X Y)
  induced_map : {S' : Sort _} → {G' : Groupoid S'} → 
          Quiver.PreFunctor Q G'.toQuiver → Groupoid.Functor G G'

def FreeGroupoid.ι {S : Sort _} (Q : Quiver S) (G : Groupoid S) [FreeGroupoid.Struct Q G] : 
  Quiver.PreFunctor Q G.toQuiver :=
  {obj := id, map := FreeGroupoid.Struct.map}

class FreeGroupoid {S : Sort _} (Q : Quiver S) (G : Groupoid S) extends FreeGroupoid.Struct Q G where
  induced_extends : {S' : Sort _} → {G' : Groupoid S'} → 
          (φ : Quiver.PreFunctor Q G'.toQuiver) → 
            Quiver.PreFunctor.comp (FreeGroupoid.ι Q G) (induced_map φ).toPreFunctor = φ
  induced_unique : {S' : Sort _} → {G' : Groupoid S'} →
          (Φ Ψ : Groupoid.Functor G G') → 
            Quiver.PreFunctor.comp (FreeGroupoid.ι Q G) Φ.toPreFunctor = 
            Quiver.PreFunctor.comp (FreeGroupoid.ι Q G) Ψ.toPreFunctor →
              Φ = Ψ