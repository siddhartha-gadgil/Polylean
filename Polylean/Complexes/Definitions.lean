section Structures

/-- A `Quiver` `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. It is a common generalisation of multigraphs and categories. This definition is taken from `mathlib`: https://leanprover-community.github.io/mathlib_docs/combinatorics/quiver/basic.html#quiver.-/
class Quiver (V : Type _) where
  hom : V → V → Sort _

infixr:10 " ⟶ " => Quiver.hom -- type using `\-->` or `\hom`

/-- Serre's definition of an undirected graph. -/
class SerreGraph (V : Type _) extends Quiver V where
  op : {A B : V} → (A ⟶ B) → (B ⟶ A)
  opInv : {A B : V} → (e : A ⟶ B) → op (op e) = e
  opFree : {A : V} → {e : A ⟶ A} → op e ≠ e

/-- The definition of a `CategoryStruct`, a barebones structure for a category containing none of the axioms (following `mathlib`). -/
class CategoryStruct (Obj : Type _) extends Quiver Obj where
  id : (X : Obj) → (X ⟶ X)
  comp : {X Y Z : Obj} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

notation "𝟙" => CategoryStruct.id -- type as `\b1`
infixr:80 " ≫ " => CategoryStruct.comp -- type as `\gg`
infixl:80 " ⊚ " => λ f g => CategoryStruct.comp g f

/-- The definition of a Category. -/
class Category (Obj : Type _) extends CategoryStruct Obj where
  idComp : {X Y : Obj} → (f : X ⟶ Y) → 𝟙 X ≫ f = f
  compId : {X Y : Obj} → (f : X ⟶ Y) → f ≫ 𝟙 Y = f
  compAssoc : {W X Y Z : Obj} → (f : W ⟶ X) → (g : X ⟶ Y) → (h : Y ⟶ Z) →
    (f ≫ g) ≫ h = f ≫ (g ≫ h)

/-- An `Invertegory` is meant to be an intermediate between a `Category` and a `Groupoid`. It is a category in which every morphism has a formal inverse, but the inverse is not required to satisfy any properties. This is not a standard construction in the literature. -/
class Invertegory (Obj : Type _) extends Category Obj where
  inv : {X Y : Obj} → (X ⟶ Y) → (Y ⟶ X)

/-- A `Groupoid` is a category in which every morphism is invertible. -/
class Groupoid (Obj : Type _) extends Invertegory Obj where
  invComp : {X Y : Obj} → (f : X ⟶ Y) → inv f ≫ f = 𝟙 Y
  compInv : {X Y : Obj} → (f : X ⟶ Y) → f ≫ inv f = 𝟙 X

end Structures


section Maps

/-- A pre-functor is a morphism of quivers. -/
structure PreFunctor (V V' : Type _) [Q : Quiver V] [Q' : Quiver V'] where
  obj : V → V'
  map : {X Y : V} → (X ⟶ Y) → (obj X ⟶ obj Y)

/-- The identity morphism between quivers. -/
@[simp] protected def PreFunctor.id (V : Type _) [Quiver V] : PreFunctor V V :=
{ obj := id, map := id }

instance (V : Type _) [Quiver V] : Inhabited (PreFunctor V V) := ⟨PreFunctor.id V⟩

/-- Composition of morphisms between quivers. -/
@[simp] def PreFunctor.comp (U V W : Type _) [Quiver U] [Quiver V] [Quiver W]
  (F : PreFunctor U V) (G : PreFunctor V W) : PreFunctor U W :=
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map }


/-- A functor is a morphism of categories. -/
structure Category.Functor (C D : Type _) [Category C] [Category D] extends PreFunctor C D where
  mapId : (X : C) → map (𝟙 X) = 𝟙 (obj X)
  mapComp : {X Y Z : C} → (f : X ⟶ Y) → (g : Y ⟶ Z) → 
      map (f ≫ g) = map f ≫ map g

infixr:26 " ⥤ " => Category.Functor -- type as `\func`

end Maps


namespace Quiver

variable {V : Type _} [Quiver V] {A B C D : V}

/-- Paths in a quiver. -/
inductive Path : V → V → Sort _
  | nil : {A : V} → Path A A
  | cons : {A B C : V} → (A ⟶ B) → Path B C → Path A C

@[matchPattern] def Path.nil' (A : V) : Path A A := Path.nil
@[matchPattern] def Path.cons' (A B C : V) : 
  (A ⟶ B) → Path B C → Path A C := Path.cons

/-- Concatenation of paths. -/
def Path.append : {A B C : V} → Path A B → Path B C → Path A C
  | _, _, _, .nil, p => p
  | _, _, _, .cons e p', p => cons e (append p' p)

@[simp] theorem Path.nil_append (p : Path A B) : .append .nil p = p := rfl

@[simp] theorem Path.append_nil (p : Path A B) : .append p .nil = p := by
  induction p
  · case nil => rfl
  · case cons =>
      simp only [append]
      apply congrArg
      assumption

theorem Path.comp_assoc (p : Path A B) (q : Path B C) (r : Path C D) : append (append p q) r = append p (append q r) := by
  induction p
  · case nil => simp
  · case cons ih => 
      simp [append]
      apply ih

/-- Paths in a quiver form a category under concatenation. -/
instance : Category V where
  hom := Path
  id := Path.nil'
  comp := Path.append

  idComp := Path.nil_append
  compId := Path.append_nil
  compAssoc := Path.comp_assoc

def Quiver.hom.toPath : (A ⟶ B) → Path A B :=
  (Path.cons · Path.nil)

end Quiver

/-
def SerreGraph.inverse [G : SerreGraph V] : {A B : V} → Quiver.Path A B → Quiver.Path B A
  | _, _, .nil => .nil
  | _, _, .cons e p => .append (inverse p) (SerreGraph.op e).toPath
-/