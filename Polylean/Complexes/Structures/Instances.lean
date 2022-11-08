import Polylean.Complexes.Structures.Quiver
import Polylean.Complexes.Structures.SerreGraph
import Polylean.Complexes.Structures.Category
import Polylean.Complexes.Structures.Invertegory

/-- Paths in a quiver form a category under concatenation. -/
instance (priority := low) Quiver.Pathegory {V : Type _} (_ : Quiver V) : Category V where
  hom := Path
  id := Path.nil'
  comp := Path.append

  idComp := Path.nil_append
  compId := Path.append_nil
  compAssoc := Path.append_assoc

instance Invertegory.toSerreGraph {V : Type _} {_ : Invertegory V} : SerreGraph V where
  op := inv
  opInv := Invertegory.invInv

/-- Paths in a Serre graph form an invertegory under concatenation. -/
instance SerreGraph.Invertegraph {V : Type _} (_ : SerreGraph V) : Invertegory V where
  -- TODO Use `..` notation
  hom := Path
  id := Path.nil'
  comp := Path.append
  inv := Path.inverse

  idComp := Path.nil_append
  compId := Path.append_nil
  compAssoc := Path.append_assoc
  invInv := by simp

/-- Embedding of a `Quiver` into its category of paths. -/
instance {V : Type _} [Q : Quiver V] : Quiver.PreFunctor Q Q.Pathegory.toQuiver where
  obj := id
  map := Quiver.toPath
