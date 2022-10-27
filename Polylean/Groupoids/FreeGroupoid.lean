import Polylean.Groupoids.Groupoid

structure FreeGroupoid {S : Sort _} (Q : Quiver S) (G : Groupoid S) where
  ι : Quiver.PreFunctor Q G.toQuiver
  induced_map : {S' : Sort _} → {G' : Groupoid S'} → 
          Quiver.PreFunctor Q G'.toQuiver → G ⥤ G'
  induced_extends : {S' : Sort _} → {G' : Groupoid S'} → 
          (φ : Quiver.PreFunctor Q G'.toQuiver) → 
            Quiver.PreFunctor.comp ι (induced_map φ).toPreFunctor = φ
  lift_unique : {S' : Sort _} → {G' : Groupoid S'} →
          (Φ Ψ : G ⥤ G') → 
            Quiver.PreFunctor.comp ι Φ.toPreFunctor = 
            Quiver.PreFunctor.comp ι Ψ.toPreFunctor →
              Φ = Ψ