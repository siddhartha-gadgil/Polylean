/-- A `Quiver` `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices 
    a type `a ⟶ b` of arrows from `a` to `b`. 
    
    It is a common generalisation of multigraphs and categories. 
    This definition is taken from `mathlib`: 
    https://leanprover-community.github.io/mathlib_docs/combinatorics/quiver/basic.html#quiver. -/
class Quiver (V : Type _) where
  hom : V → V → Sort _

infixr:10 " ⟶ " => Quiver.hom -- type using `\-->` or `\hom`


/-- A pre-functor is a morphism of quivers. -/
structure Quiver.PreFunctor {V V' : Type _} (Q : Quiver V) (Q' : Quiver V') where
  obj : V → V'
  map : {X Y : V} → (X ⟶ Y) → (obj X ⟶ obj Y)

namespace Quiver.PreFunctor

/-- The identity morphism between quivers. -/
@[simp] protected def id (V : Type _) [Q : Quiver V] : PreFunctor Q Q :=
{ obj := id, map := id }

instance (V : Type _) [Q : Quiver V] : Inhabited (PreFunctor Q Q) := ⟨PreFunctor.id V⟩

/-- Composition of morphisms between quivers. -/
@[simp] def comp {U V W : Type _} {QU : Quiver U} {QV : Quiver V} {QW : Quiver W}
  (F : PreFunctor QU QV) (G : PreFunctor QV QW) : PreFunctor QU QW :=
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map }

end Quiver.PreFunctor

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

theorem first_cons (A B C : V) (e : A ⟶ B) (p : Path B C) : first (cons e p) = B := rfl

theorem last_snoc : (A B C : V) → (p : Path A B) → (e : B ⟶ C) → last (snoc p e) = B
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons' _ _ _ _ .nil, _ => by rw [snoc_cons]; rfl
  | _, _, _, .cons' _ _ _ _ (.cons _ _), _ => by rw [snoc_cons, snoc, last, ← snoc_cons]; apply last_snoc

end Path
