import Polylean.Complexes.Definitions

abbrev Loop {V : Type _} [G : SerreGraph V] (A : V) := @Path V G.toQuiver A A

namespace Loop

variable {V : Type _} [SerreGraph V] (A : V)

def toPath : Loop A → Path A A := id

abbrev nil : Loop A := Path.nil

abbrev next : Loop A → V := Path.first

abbrev concat : Loop A → Loop A → Loop A := Path.append

abbrev inv {A : V} : Loop A → Loop A := Path.inverse

@[simp] theorem inv_inv (l : Loop A) : l.inv.inv = l := by simp

-- temporary substitute for `Path.last`
abbrev prev : Loop A → V := λ l => (l.inv).next

def rotate : (l : Loop A) → Loop (l.next A)
  | .nil' A => .nil' A
  | .cons' _ _ _ e p => p.snoc e

def rotate' : (l : Loop A) → Loop (l.prev A) :=
  λ l => ((l |>.inv) |>.rotate) |>.inv


@[simp] theorem inv_rotate_inv (l : Loop A) : 
  (rotate A l.inv).inv = rotate' A l := by simp [rotate']

@[simp] theorem prev_inv (l : Loop A) : (prev A l.inv) = next A l := by simp [prev]

@[simp] theorem rotate_prev : (l : Loop A) → (l.rotate A).prev _ = A
  | .nil' _ => rfl
  | .cons' _ _ _ e p => by
    dsimp [prev, rotate, inv]
    rw [Path.inverse_snoc]
    rfl

@[simp] theorem rotate'_next (l : Loop A) : (l.rotate' A).next _ = A := by
  show prev _ (rotate _ l.inv) = A
  simp

@[simp] theorem rotate_rotate' : (l : Loop A) → rotate' _ (rotate A l) = cast (congrArg Loop $ Eq.symm $ rotate_prev A l) l
  | .nil' _ => rfl
  | .cons' _ _ _ e p => sorry

@[simp] theorem rotate'_rotate : (l : Loop A) → rotate _ (rotate' A l) = cast (congrArg Loop $ Eq.symm $ rotate'_next A l) l
  | .nil' _ => rfl
  | .cons' _ _ _ e p => sorry

theorem inv_rotate_heq (l : Loop A) : HEq (rotate A l).inv (rotate' A l.inv) := by
  rw [← inv_rotate_inv A l.inv]
  congr 2 <;> rw [inv_inv]
 
theorem inv_rotate (l : Loop A) : (rotate A l).inv = (prev_inv A l) ▸ (rotate' A l.inv) := sorry
  

end Loop


class QuiverRel {V : Type _} extends Quiver V where
  rel : {v : V} → Path v v → Sort _

class TwoComplex (V : Type _) extends SerreGraph V where
  rel : {v : V} → Loop v → Sort _
  inv : {v w : V} → (e : v ⟶ w) → rel (.cons (op e) $ .cons e .nil)
  flip :  {v : V} → {l : Loop v} → rel l → rel l.inv
  flipInv : {v : V} → {l : Loop v} → (r : rel l) → (Eq.subst l.inverse_inv $ flip (flip r)) = r

inductive Relator {V : Type _} [TwoComplex V] : (v : V) → (ℓ : Loop v) → Sort _
  | disc : {v : V} → {l : Loop v} → TwoComplex.rel l → Relator v l
  | concat : {v : V} → {l l' : Loop v} → Relator v l → Relator v l' → Relator v (.append l l')
  | delete : {v : V} → {l l' : Loop v} → TwoComplex.rel l → Relator v (.append l l') → Relator v l'
  | rotate : {v : V} → {l : Loop v} → Relator v l → Relator (l.next v) l.rotate

inductive Path.Homotopy {V : Type _} [TwoComplex V] : {v w : V} → (p q : Path v w) → Prop
  | rel : {v w : V} → (p q : Path v w) → Relator v (.append p q.inverse) → Homotopy p q


namespace Relator

variable {V : Type _} [C : TwoComplex V] {u v w : V} (l l' : Loop v)

def cast : {u v : V} → (h : u = v) → (l : Loop u) → Relator u l → Relator v (h ▸ l)
  | _, _, rfl, _ => id

def subst : {u v : V} → (h : u = v) → (l : Loop u) → (l' : Loop v) → (H : h ▸ l = l') → Relator u l → Relator v l'
  | _, _, rfl, _, _, rfl => id

def swap {u v : V} : (p : Path u v) → (q : Path v u) → Relator u (.append p q) → Relator v (.append q p)
  | .nil, _ => by rw [Path.append_nil]; exact id
  | .cons _ _, _ => by
    dsimp [Path.append]
    intro r
    let r' := Relator.rotate r
    dsimp [Loop.next, Path.first, Loop.rotate] at r'
    rw [Path.append_cons]
    apply swap
    rw [Path.append_snoc]
    exact r'

def delete' {v : V} {l l' : Loop v} (d : TwoComplex.rel l) (r : Relator v (.append l' l)) : Relator v l' :=
  let r' := swap l' l r
  Relator.delete d r'

def rotate' {v : V} {l : Loop v} (r : Relator v l) : Relator (l.prev v) l.rotate' := by
  dsimp [Loop.rotate']
  let l' := l.inv
  have : l = l'.inv := by simp
  rw [this]
  apply subst (Eq.symm $ Loop.prev_inv v l')
  · sorry
  · sorry -- unable to proceed
  · sorry

def nil {v : V} {l : Loop v} (d : TwoComplex.rel l) : Relator v (.nil v) :=
  let r : Relator v (.append .nil l) := Relator.disc d
  Relator.delete' d r

def trivial {u v : V} {l : Loop u} (d : TwoComplex.rel l) : (p : Path u v) → Relator u (.append p p.inverse)
  | .nil => nil d
  | .cons e p' => by
    rename_i x
    dsimp [Path.append, Path.inverse]
    rw [Path.append_snoc]
    rw [← Path.snoc_cons]
    let erel : Loop x := .cons (SerreGraph.op e) (.cons e .nil)
    let l : Loop x := .append erel (.append p' p'.inverse)
    show Relator l.next l.rotate
    apply Relator.rotate
    apply Relator.concat
    · apply Relator.disc
      apply TwoComplex.inv
    · apply trivial
      apply TwoComplex.inv
      exact e

def inv {v : V} {l : Loop v} : Relator v l → Relator v l.inv
  | .disc d => .disc $ TwoComplex.flip d
  | .concat r r' => by
      rw [Loop.inv, Path.inverse_append]
      apply Relator.concat
      · exact inv r'
      · exact inv r
  | .delete d r => by
      let r' := inv r
      rw [Loop.inv, Path.inverse_append] at r'
      apply Relator.delete'
      · exact TwoComplex.flip d
      · exact r'
  | .rotate r => by
      let r' := inv r
      apply subst (Loop.prev_inv _ _)
      · apply Eq.symm
        apply Loop.inv_rotate
      · apply rotate'
        exact inv r

end Relator


namespace Path.Homotopy

variable {V : Type _} [TwoComplex V] {u v w : V} (p q r : Path u v)

theorem refl : Path.Homotopy p p := sorry

theorem symm : Path.Homotopy p q → Path.Homotopy q p := sorry

theorem trans : Path.Homotopy p q → Path.Homotopy q r → Path.Homotopy p r := sorry

end Path.Homotopy
