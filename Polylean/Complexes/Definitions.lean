import Polylean.Complexes.Quiver

section Structures

/-- Serre's definition of an undirected graph. -/
class SerreGraph (V : Type _) extends Quiver V where
  op : {A B : V} → (A ⟶ B) → (B ⟶ A)
  opInv : {A B : V} → (e : A ⟶ B) → op (op e) = e

attribute [reducible] SerreGraph.op
attribute [simp] SerreGraph.opInv

def Quiver.symmetrize {V : Type _} (Q : Quiver V) : SerreGraph V :=
{ hom := λ A B => Q.hom A B ⊕ Q.hom B A,
  op := fun | .inl e => .inr e | .inr e => .inl e,
  opInv := fun | .inl _ => rfl | .inr _ => rfl }

/-- The definition of a `CategoryStruct`, a barebones structure for a category containing none of the axioms (following `mathlib`). -/
class CategoryStruct (Obj : Type _) extends Quiver Obj where
  id : (X : Obj) → (X ⟶ X)
  comp : {X Y Z : Obj} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

attribute [reducible] CategoryStruct.id
attribute [reducible] CategoryStruct.comp

notation "𝟙" => CategoryStruct.id -- type as `\b1`
infixr:80 " ≫ " => CategoryStruct.comp -- type as `\gg`
infixl:80 " ⊚ " => λ f g => CategoryStruct.comp g f

/-- The definition of a Category. -/
class Category (Obj : Type _) extends CategoryStruct Obj where
  idComp : {X Y : Obj} → (f : X ⟶ Y) → 𝟙 X ≫ f = f
  compId : {X Y : Obj} → (f : X ⟶ Y) → f ≫ 𝟙 Y = f
  compAssoc : {W X Y Z : Obj} → (f : W ⟶ X) → (g : X ⟶ Y) → (h : Y ⟶ Z) →
    (f ≫ g) ≫ h = f ≫ (g ≫ h)

attribute [simp] Category.idComp
attribute [simp] Category.compId

/-- An `Invertegory` is meant to be an intermediate between a `Category` and a `Groupoid`. It is a category in which every morphism has a formal inverse, but the inverse is not required to satisfy any properties. This is not a standard construction in the literature. -/
class Invertegory (Obj : Type _) extends Category Obj where
  inv : {X Y : Obj} → (X ⟶ Y) → (Y ⟶ X)
  invInv : ∀ e : X ⟶ Y, inv (inv e) = e

/-- A `Groupoid` is a category in which every morphism is invertible. -/
class Groupoid (Obj : Type _) extends Invertegory Obj where
  invComp : {X Y : Obj} → (f : X ⟶ Y) → inv f ≫ f = 𝟙 Y
  compInv : {X Y : Obj} → (f : X ⟶ Y) → f ≫ inv f = 𝟙 X

attribute [simp] Groupoid.invComp
attribute [simp] Groupoid.compInv

end Structures


section Maps

/-- A functor is a morphism of categories. -/
structure Category.Functor {C D : Type _} (𝓒 : Category C) (𝓓 : Category D) extends Quiver.PreFunctor 𝓒.toQuiver 𝓓.toQuiver where
  mapId : (X : C) → map (𝟙 X) = 𝟙 (obj X)
  mapComp : {X Y Z : C} → (f : X ⟶ Y) → (g : Y ⟶ Z) → 
      map (f ≫ g) = map f ≫ map g

infixr:26 " ⥤ " => Category.Functor -- type as `\func`

attribute [simp] Category.Functor.mapId
attribute [simp] Category.Functor.mapComp

@[simp] protected def Category.Functor.id (C : Type _) [𝓒 : Category C] : 𝓒 ⥤ 𝓒 :=
-- TODO Use `..` notation : { .. , mapId := λ _ => rfl, mapComp := λ _ _ => rfl }
 { obj := id, map := id, mapId := λ _ => rfl, mapComp := λ _ _ => rfl }

@[simp] def Category.Functor.comp {C D E : Type _} {𝓒 : Category C} {𝓓 : Category D} {𝓔 : Category E} (F : 𝓒 ⥤ 𝓓) (G : 𝓓 ⥤ 𝓔) : 𝓒 ⥤ 𝓔 :=
-- TODO Use `..` notation
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map, mapId := by intro; simp, mapComp := by intros; simp }

/-- `Invertegory.Functor` is a morphism of `Invertegories` that preserves inverses. -/
structure Invertegory.Functor {C D : Type _} (ℭ : Invertegory C) (𝔇 : Invertegory D) extends Category.Functor ℭ.toCategory 𝔇.toCategory where
  mapInv : {X Y : C} → {f : X ⟶ Y} → map (Invertegory.inv f) = Invertegory.inv (map f)

attribute [simp] Invertegory.Functor.mapInv

@[simp] protected def Invertegory.Functor.id (C : Type _) [ℭ : Invertegory C] : Invertegory.Functor ℭ ℭ :=
-- TODO Use `..` notation
 { obj := id, map := id, mapId := λ _ => rfl, mapComp := λ _ _ => rfl, mapInv := rfl }

@[simp] def Invertegory.Functor.comp {C D E : Type _} {ℭ : Invertegory C} {𝔇 : Invertegory D} {𝔈 : Invertegory E} (F : Invertegory.Functor ℭ 𝔇) (G : Invertegory.Functor 𝔇 𝔈) : Invertegory.Functor ℭ 𝔈 :=
-- TODO Use `..` notation
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map, mapId := by intro; simp, mapComp := by intros; simp, mapInv := by intros; simp }

end Maps

namespace Path

/-- The inverse of a path in a Serre graph. -/
def inverse {V : Type _} [SerreGraph V] : {A B : V} → Path A B → Path B A
  | _, _, .nil => .nil
  | _, _, .cons e p => .snoc (inverse p) (SerreGraph.op e)

@[simp] theorem inverse_snoc {V : Type _} [G : SerreGraph V] {A B C : V} : 
  (p : @Path V G.toQuiver A B) → (e : B ⟶ C) → 
  inverse (.snoc p e) = .cons (SerreGraph.op e) (inverse p)
  | .nil, e => rfl
  | .cons e' p', e => by dsimp [inverse]; rw [inverse_snoc p' e]

@[simp] theorem inverse_inv {V : Type _} [G : SerreGraph V] {A B : V} : 
  (p : @Path V G.toQuiver A B) → p.inverse.inverse = p
  | .nil => rfl
  | .cons e p' => by simp [inverse]; apply inverse_inv

@[simp] theorem inverse_append {V : Type _} [G : SerreGraph V] {A B C : V} : 
  (p : @Path V G.toQuiver A B) → (q : @Path V G.toQuiver B C) → 
  inverse (append p q) = .append (inverse q) (inverse p)
  | .nil, q => by simp [inverse]
  | p, .nil => by simp [inverse]
  | .cons _ p', .cons _ q' => by
    dsimp [inverse]
    rw [inverse_append p' _, append_snoc]
    rfl

theorem length_inverse {V : Type _} [G : SerreGraph V] {A B : V} :
  (p : @Path V G.toQuiver A B) → p.inverse.length = p.length
  | .nil => rfl
  | .cons _ p' => by
    dsimp [inverse, length]
    rw [snoc_length]
    apply congrArg
    apply length_inverse

def compose {C : Type _} [𝓒 : Category C] {X Y : C} : @Path C 𝓒.toQuiver X Y → (X ⟶ Y)
  | .nil => 𝟙 _
  | .cons e p => e ≫ p.compose

@[simp] theorem compose_nil {C : Type _} [Category C] {X : C} : (Path.nil' X).compose = 𝟙 X := rfl

def compose_append {C : Type _} [𝓒 : Category C] {X Y Z : C} : {p : Path X Y} → {q : Path Y Z} → (append p q).compose = p.compose ≫ q.compose
  | .nil, _ => by simp
  | .cons _ _, _ => by
    dsimp [append, compose]
    rw [compose_append, Category.compAssoc]

theorem first_eq_inv_last {V : Type _} [G : SerreGraph V] : {A B : V} →
    (p : @Path V G.toQuiver A B) → p.first = p.inverse.last
  | _, _, .nil => rfl
  | _, _, .cons e p' => by simp [first, last, inverse, snoc, last_snoc]

theorem last_eq_inv_first {V : Type _} [G : SerreGraph V] {A B : V} :
    (p : @Path V G.toQuiver A B) → p.last = p.inverse.first := by
    intro p
    let p' := p.inverse
    have pinv : p = p'.inverse := by simp
    rw [pinv, inverse_inv p']
    apply Eq.symm
    apply first_eq_inv_last

end Path

section Instances

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

instance Intertegory.composeFunctor {C : Type _} (ℭ : Invertegory G) : Invertegory.Functor (ℭ.toSerreGraph).Invertegraph ℭ where
  obj := id
  map := Path.compose

  mapId := λ _ => rfl
  mapComp := λ _ _ => Path.compose_append

  -- does not work
  mapInv := by
    intros _ _ p
    simp
    induction p
    · show Path.compose (Path.nil) = Invertegory.inv _
      rw [Path.compose]
      sorry
    · show Path.compose (Path.snoc _ _) = _
      rw [Path.compose]
      sorry      
    

end Instances

/-! A 2-complex on a type `V` is represented here by three pieces of data:
  - A Serre graph `G` on `V` representing the underlying 1-complex
  - A groupoid `H` on `V` representing the paths in `G` up to homotopy
  - A map taking each path in `G` to a morphism in `H` representing its path-homotopy class, satisfying a few consistency conditions
 -/
class AbstractTwoComplex (V : Type _) where
  G : SerreGraph V
  H : Groupoid V
  collapse : Invertegory.Functor G.Invertegraph H.toInvertegory
  collapseId : collapse.obj = id

instance (priority := low) AbstractTwoComplex.SerreGraph (V : Type _) [CV : AbstractTwoComplex V] : SerreGraph V := CV.G

instance (priority := low) AbstractTwoComplex.Groupoid (V : Type _) [CV : AbstractTwoComplex V] : Groupoid V := CV.H

/-- A continuous map between 2-complexes. -/
structure AbstractTwoComplex.ContinuousMap {V W : Type _} (CV : AbstractTwoComplex V) (CW : AbstractTwoComplex W) where
  -- Alternative version: Construct a map between the two Serre graphs 
  graphMap : Invertegory.Functor CV.G.Invertegraph CW.G.Invertegraph
  homotopyMap : Invertegory.Functor CV.H.toInvertegory CW.H.toInvertegory

  mapCommute : Invertegory.Functor.comp graphMap CW.collapse = 
               Invertegory.Functor.comp CV.collapse homotopyMap
