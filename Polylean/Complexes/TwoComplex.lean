import Polylean.Complexes.Structures.SerreGraph

class QuiverRel (V : Sort _) extends Quiver V where
  rel : {v : V} → Path v v → Sort _

class TwoComplex (V : Sort _) extends SerreGraph V where  
  rel : {v : V} → Loop v → Sort _
  
  inv : {v w : V} → (e : v ⟶ w) → rel (.cons (op e) $ .cons e .nil)
  flip :  {v : V} → {l : Loop v} → rel l → rel l.inv
  flipInv : {v : V} → {l : Loop v} → (r : rel l) → (Eq.subst l.inverse_inv $ flip (flip r)) = r

inductive Relator {V : Sort _} [TwoComplex V] : (v : V) → (ℓ : Loop v) → Sort _
  | nil : {v : V} → Relator v (.nil v)
  | disc : {v : V} → {l : Loop v} → TwoComplex.rel l → Relator v l
  | concat : {v : V} → {l l' : Loop v} → Relator v l → Relator v l' → Relator v (.append l l')
  | delete : {v : V} → {l l' : Loop v} → Relator v l → Relator v (.append l l') → Relator v l'
  | rotate : {v : V} → {l : Loop v} → Relator v l → Relator (l.next v) l.rotate
  | rotate' : {v : V} → {l : Loop v} → Relator v l → Relator (l.prev v) l.rotate'

inductive Path.Homotopy {V : Sort _} [TwoComplex V] : {v w : V} → (p q : Path v w) → Prop
  | rel : {v w : V} → {p q : Path v w} → Relator v (.append p q.inverse) → Homotopy p q


namespace Relator

variable {V : Sort _} [C : TwoComplex V] {u v w : V} (l l' : Loop v)

def subst : {u v : V} → (h : u = v) → (l : Loop u) → (l' : Loop v) → (l = (congrArg Loop h) ▸ l') → Relator u l → Relator v l'
  | _, _, rfl, _, _, rfl => id

def swap {u v : V} : {p : Path u v} → {q : Path v u} → Relator u (.append p q) → Relator v (.append q p)
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

def delete' {v : V} {l l' : Loop v} (r : Relator v l) (r' : Relator v (.append l' l)) : Relator v l' :=
  Relator.delete r $ swap r'

def contract {u v : V} {p : Path u v} {l : Loop v} (rel : Relator v l) {q : Path v u} : Relator u (.append p (.append l q)) → Relator u (.append p q) := by
  intro r
  let r' := swap r
  rw [Path.append_assoc] at r'
  let r'' := delete rel r'
  exact swap r''

def splice {u v : V} {p : Path u v} {l : Loop v} (rel : Relator v l) {q : Path v u} : Relator u (.append p q) → Relator u (.append p (.append l q)) := by
  intro r
  apply swap
  rw [Path.append_assoc]
  apply concat rel
  apply swap
  exact r

def trivial {u v : V} : (p : Path u v) → Relator u (.append p p.inverse)
  | .nil => .nil
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

def inv {v : V} {l : Loop v} : Relator v l → Relator v l.inv
  | .nil => .nil
  | .disc d => .disc $ TwoComplex.flip d
  | .concat r r' => by
      rw [Loop.inv, Path.inverse_append]
      apply Relator.concat
      · exact inv r'
      · exact inv r
  | .delete r r' => by
      let r'' := inv r'
      rw [Loop.inv, Path.inverse_append] at r''
      exact Relator.delete' (inv r) r''
  | .rotate r => by
      apply subst (Loop.prev_inv _ _)
      · apply Loop.rotate'_inv
      · exact rotate' <| inv r
  | .rotate' r => by
      apply subst (Loop.next_inv _ _)
      · apply Loop.rotate_inv
      · exact rotate <| inv r

end Relator


namespace Path.Homotopy

variable {V : Sort _} [C : TwoComplex V] {u v : V} (p q r : Path u v)

theorem refl : (p : Path u v) → Path.Homotopy p p := (.rel $ Relator.trivial ·)

theorem symm : Path.Homotopy p q → Path.Homotopy q p
  | .rel h => by
    let h' := h.inv
    rw [Loop.inv, Path.inverse_append, Path.inverse_inv] at h'
    exact .rel h'

theorem trans : Path.Homotopy p q → Path.Homotopy q r → Path.Homotopy p r
  |.rel h, .rel h' => by
    let H := Relator.concat h h'
    rw [Path.append_assoc p _ _, ← Path.append_assoc _ q _] at H
    let H' := Relator.contract (.swap $ .trivial _) H
    exact .rel H'

instance equivalence (u v : V) : Equivalence (@Path.Homotopy V C u v) where
  refl := refl
  symm := symm _ _
  trans := trans _ _ _

instance setoid (u v : V) : Setoid (Path u v) where
  r := Path.Homotopy
  iseqv := equivalence u v

theorem inv_cancel_left (p : Path u v) : Path.Homotopy (.append (.inverse p) p) .nil := 
  .rel $ by
    simp [inverse]
    apply Relator.swap
    apply Relator.trivial

theorem inv_cancel_right (p : Path u v) : Path.Homotopy (.append p (.inverse p)) .nil := 
  .rel $ by
    simp [inverse]
    apply Relator.trivial

theorem mul_sound {u v w : V} {p q : Path u v} {r s : Path v w} : 
  Path.Homotopy p q → Path.Homotopy r s → 
  Path.Homotopy (.append p r) (.append q s)
  | .rel a, .rel b  => .rel $ by
    rw [inverse_append, append_assoc, ← append_assoc _ _ (inverse q)]
    exact Relator.splice b a

theorem inv_sound {u v : V} {p q : Path u v} : 
  Path.Homotopy p q → 
  Path.Homotopy p.inverse q.inverse
  | .rel r =>.rel $ by
    rw [← inverse_append]
    apply Relator.inv
    apply Relator.swap
    exact r

end Path.Homotopy
