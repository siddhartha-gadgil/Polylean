section Structures

/-- A `Quiver` `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. It is a common generalisation of multigraphs and categories. This definition is taken from `mathlib`: https://leanprover-community.github.io/mathlib_docs/combinatorics/quiver/basic.html#quiver.-/
class Quiver (V : Type _) where
  hom : V → V → Sort _

attribute [reducible] Quiver.hom
infixr:10 " ⟶ " => Quiver.hom -- type using `\-->` or `\hom`

/-- Serre's definition of an undirected graph. -/
class SerreGraph (V : Type _) extends Quiver V where
  op : {A B : V} → (A ⟶ B) → (B ⟶ A)
  opInv : {A B : V} → (e : A ⟶ B) → op (op e) = e
  opFree : {A : V} → (e : A ⟶ A) → op e ≠ e

attribute [reducible] SerreGraph.op
attribute [simp] SerreGraph.opInv

def Quiver.symmetrize {V : Type _} [Q : Quiver V] : SerreGraph V :=
{ hom := λ A B => Q.hom A B ⊕ Q.hom B A,
  op := fun | .inl e => .inr e | .inr e => .inl e,
  opInv := fun | .inl e => rfl | .inr e => rfl,
  opFree := fun | .inl e => by simp | .inr e => by simp }

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

/-- A `Groupoid` is a category in which every morphism is invertible. -/
class Groupoid (Obj : Type _) extends Invertegory Obj where
  invComp : {X Y : Obj} → (f : X ⟶ Y) → inv f ≫ f = 𝟙 Y
  compInv : {X Y : Obj} → (f : X ⟶ Y) → f ≫ inv f = 𝟙 X

attribute [simp] Groupoid.invComp
attribute [simp] Groupoid.compInv

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
@[simp] def PreFunctor.comp {U V W : Type _} [Quiver U] [Quiver V] [Quiver W]
  (F : PreFunctor U V) (G : PreFunctor V W) : PreFunctor U W :=
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map }


/-- A functor is a morphism of categories. -/
structure Category.Functor (C D : Type _) [Category C] [Category D] extends PreFunctor C D where
  mapId : (X : C) → map (𝟙 X) = 𝟙 (obj X)
  mapComp : {X Y Z : C} → (f : X ⟶ Y) → (g : Y ⟶ Z) → 
      map (f ≫ g) = map f ≫ map g

infixr:26 " ⥤ " => Category.Functor -- type as `\func`

attribute [simp] Category.Functor.mapId
attribute [simp] Category.Functor.mapComp

@[simp] protected def Category.Functor.id (C : Type _) [Category C] : C ⥤ C :=
-- TODO Use `..` notation : { .. , mapId := λ _ => rfl, mapComp := λ _ _ => rfl }
 { obj := id, map := id, mapId := λ _ => rfl, mapComp := λ _ _ => rfl }

@[simp] def Category.Functor.comp {C D E : Type _} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E :=
-- TODO Use `..` notation
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map, mapId := by intro; simp, mapComp := by intros; simp }

/-- `Invertegory.Functor` is a morphism of `Invertegories` that preserves inverses. -/
structure Invertegory.Functor (C D : Type _) [Invertegory C] [Invertegory D] extends Category.Functor C D where
  mapInv : {X Y : C} → {f : X ⟶ Y} → map (Invertegory.inv f) = Invertegory.inv (map f)

attribute [simp] Invertegory.Functor.mapInv

@[simp] protected def Invertegory.Functor.id (C : Type _) [Invertegory C] : Invertegory.Functor C C :=
-- TODO Use `..` notation
 { obj := id, map := id, mapId := λ _ => rfl, mapComp := λ _ _ => rfl, mapInv := rfl }

@[simp] def Invertegory.Functor.comp {C D E : Type _} [Invertegory C] [Invertegory D] [Invertegory E] (F : Invertegory.Functor C D) (G : Invertegory.Functor D E) : Invertegory.Functor C E :=
-- TODO Use `..` notation
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map, mapId := by intro; simp, mapComp := by intros; simp, mapInv := by intros; simp }

end Maps

/-- Paths in a quiver. -/
inductive Path {V : Type _} [Quiver V] : V → V → Sort _
  | nil : {A : V} → Path A A
  | cons : {A B C : V} → (A ⟶ B) → Path B C → Path A C

def Quiver.toPath {V : Type _} [Quiver V] {A B : V} (e : A ⟶ B) : Path A B :=
  .cons e .nil

namespace Path

variable {V : Type _} [Quiver V] {A B C D : V}

@[matchPattern] abbrev nil' (A : V) : Path A A := Path.nil
@[matchPattern] abbrev cons' (A B C : V) : 
  (A ⟶ B) → Path B C → Path A C := Path.cons

/-- Concatenate an edge to the end of a path. -/
@[matchPattern]
abbrev snoc : {A B C : V} → Path A B → (B ⟶ C) → Path A C
  | _, _, _, .nil, e => .cons e .nil
  | _, _, _, .cons e p', e' => .cons e (snoc p' e')

@[matchPattern]
abbrev snoc' (A B C : V) : Path A B → (B ⟶ C) → Path A C := Path.snoc

/-- Concatenation of paths. -/
def append : {A B C : V} → Path A B → Path B C → Path A C
  | _, _, _, .nil, p => p
  | _, _, _, .cons e p', p => cons e (append p' p)

/-- The length of a path. -/
def length : {A B : V} → Path A B → Nat
  | _, _, .nil => .zero
  | _, _, .cons _ p => .succ (length p)

@[simp] theorem nil_append (p : Path A B) : .append .nil p = p := rfl

@[simp] theorem append_nil (p : Path A B) : .append p .nil = p := by
  induction p
  · case nil => rfl
  · case cons =>
      simp only [append]
      apply congrArg
      assumption

theorem snoc_cons (e : A ⟶ B) (p : Path B C) (e' : C ⟶ D) : 
  snoc (cons e p) e' = cons e (snoc p e') := by cases p <;> simp

theorem append_snoc (p : Path A B) (p' : Path B C) (e : C ⟶ D) : 
    append p (snoc p' e) = snoc (append p p') e := by
  induction p
  · case nil => rfl
  · case cons ih => simp [append, ih p', snoc_cons]

theorem append_cons (p : Path A B) (e : B ⟶ C) (p' : Path C D) : 
    append p (cons e p') = append (snoc p e) p' := by
  induction p
  · case nil => rfl
  · case cons ih => dsimp [append]; rw [ih]

theorem append_assoc (p : Path A B) (q : Path B C) (r : Path C D) :
    append (append p q) r = append p (append q r) := by
  induction p
  · case nil => rfl
  · case cons ih => simp [append]; apply ih

-- TODO Rephrase this to work for general paths, not just loops
theorem nil_length {A : V} : (p : Path A A) → p.length = .zero ↔ p = .nil' A
  | .nil => ⟨λ _ => rfl, λ _ => rfl⟩
  | .cons _ p => by apply Iff.intro <;> (intro; simp [length] at *)

theorem snoc_length {A B C : V} : (p : Path A B) → (e : B ⟶ C) → length (.snoc p e) = .succ (length p)
  | .nil, e => rfl
  | .cons _ p', e => by
    rw [snoc_cons]
    dsimp only [length]
    apply congrArg
    apply snoc_length

theorem length_append {A B C : V} : (p : Path A B) → (q : Path B C) → (append p q).length = p.length + q.length
  | .nil, q => by rw [Nat.add_comm]; rfl
  | .cons _ p', q => by
    dsimp [append, length]
    rw [Nat.succ_add]
    apply congrArg
    apply length_append

/-- The end-point of the first edge in the path. -/
def first : Path A B → V
  | .nil' v => v
  | .cons' _ v _ _ _ => v

/-- The source of the last end in the path. -/
def last : {A B : V} → Path A B → V
  | _, _, .nil' v => v
  | .(v), _, .cons' v _ _ _ .nil => v
  | _, _, .cons' _ _ _ _ (.cons e p) => last (.cons e p)

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

theorem first_cons (A B C : V) (e : A ⟶ B) (p : Path B C) : first (cons e p) = B := rfl

theorem last_snoc : (A B C : V) → (p : Path A B) → (e : B ⟶ C) → last (snoc p e) = B
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons' _ _ _ _ .nil, _ => by rw [snoc_cons]; rfl
  | _, _, _, .cons' _ _ _ _ (.cons _ _), _ => by rw [snoc_cons, snoc, last, ← snoc_cons]; apply last_snoc

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

/-
section Instances

/-- Paths in a Serre graph form an invertegory under concatenation. -/
instance (priority := high) Invertegraph {V : Type _} [SerreGraph V] : Invertegory V where
  -- TODO Use `..` notation
  hom := Path
  id := Path.nil'
  comp := Path.append
  inv := Path.inverse

  idComp := Path.nil_append
  compId := Path.append_nil
  compAssoc := Path.comp_assoc

-- TODO Find why moving this above causes issues
/-- Paths in a quiver form a category under concatenation. -/
instance (priority := low) Pathegory (V : Type _) [Quiver V] : Category V where
  hom := Path
  id := Path.nil'
  comp := Path.append

  idComp := Path.nil_append
  compId := Path.append_nil
  compAssoc := Path.comp_assoc

instance {V : Type _} [Quiver V] : PreFunctor V V := 
  sorry -- sends each arrow to the singleton path

end Instances

/-! A 2-complex on a type `V` is represented here by three pieces of data:
  - A Serre graph `G` on `V` representing the underlying 1-complex
  - A groupoid `H` on `V` representing the paths in `G` up to homotopy
  - A map taking each path in `G` to a morphism in `H` representing its path-homotopy class, satisfying a few consistency conditions
 -/
class AbstractTwoComplex (V : Type _) where
  G : SerreGraph V
  H : Groupoid V
  collapse : @Invertegory.Functor V V Invertegraph H.toInvertegory
  collapseId : obj = (@id V)

instance (priority := low) AbstractTwoComplex.SerreGraph {V : Type _} [CV : AbstractTwoComplex V] : SerreGraph V := CV.G

instance (priority := low) AbstractTwoComplex.Groupoid {V : Type _} [CV : AbstractTwoComplex V] : Groupoid V := CV.H

/-
/-- A continuous map between 2-complexes. -/
structure ContinuousMap {V W : Type _} [CV : TwoComplex V] [CW : TwoComplex W] where
  -- Alternative version: Construct a map between the two Serre graphs 
  graphMap : @Invertegory.Functor V W (@Invertegraph V TwoComplex.SerreGraph) (@Invertegraph W TwoComplex.SerreGraph)
  homotopyMap : @Invertegory.Functor V W CV.H.toInvertegory CW.H.toInvertegory

  -- TODO Fix this
  -- mapCommute : Invertegory.Functor.comp graphMap CW.collapse = Invertegory.Functor.comp CV.collapse homotopyMap
-/
-/
