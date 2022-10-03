/-- A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`.
It is a common generalisation of multigraphs and categories. This definition is taken from `mathlib`: https://leanprover-community.github.io/mathlib_docs/combinatorics/quiver/basic.html#quiver.-/
class Quiver (V : Type _) where
  hom : V → V → Sort _

infixr:10 " ⟶ " => Quiver.hom -- type using `\-->`


/-- A pre-functor is a morphism of quivers. -/
structure PreFunctor (V V' : Type _) [Q : Quiver V] [Q' : Quiver V'] where
  obj : V → V'
  map : {X Y : V} → (X ⟶ Y) → (obj X ⟶ obj Y)

/-- The identity morphism between quivers. -/
@[simp] def PreFunctor.ident (V : Type _) [Quiver V] : PreFunctor V V :=
{ obj := id, map := id }

instance (V : Type _) [Quiver V] : Inhabited (PreFunctor V V) := ⟨PreFunctor.ident V⟩

/-- Composition of morphisms between quivers. -/
@[simp] def PreFunctor.comp (U V W : Type _) [Quiver U] [Quiver V] [Quiver W]
  (F : PreFunctor U V) (G : PreFunctor V W) : PreFunctor U W :=
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map }


/-- Serre's definition of an undirected graph. -/
class SerreGraph (V : Type _) extends Quiver V where
  op : {A B : V} → (A ⟶ B) → (B ⟶ A)
  opop : {A B : V} → (e : A ⟶ B) → op (op e) = e
  opfree : {A : V} → {e : A ⟶ A} → op e ≠ e
