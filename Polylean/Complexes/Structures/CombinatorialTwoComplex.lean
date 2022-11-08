import Polylean.Complexes.Structures.SerreGraph

class CombinatorialTwoComplex (V : Sort _) extends SerreGraph V where  
  relator : {v : V} → Loop v → Sort _
  inv : {v w : V} → (e : v ⟶ w) → relator (.cons (op e) $ .cons e .nil) -- the trivial relations are satisfied
  flip :  {v : V} → {l : Loop v} → relator l → relator l.inv
  flip_inv : {v : V} → {l : Loop v} → (r : relator l) → (Eq.subst l.inverse_inv $ flip (flip r)) = r

inductive NullHomotopy {V : Sort _} [CombinatorialTwoComplex V] : {v : V} → (ℓ : Loop v) → Sort _
  | nil : {v : V} →  NullHomotopy (.nil v)
  | relator : {v : V} → {l : Loop v} → CombinatorialTwoComplex.relator l → NullHomotopy l
  | concat : {v : V} → {l l' : Loop v} → NullHomotopy l → NullHomotopy l' → NullHomotopy (.append l l')
  | delete : {v : V} → {l l' : Loop v} → NullHomotopy l → NullHomotopy (.append l l') → NullHomotopy l'
  | rotate : {v : V} → {l : Loop v} → NullHomotopy l → NullHomotopy l.rotate
  | rotate' : {v : V} → {l : Loop v} → NullHomotopy l → NullHomotopy l.rotate'

inductive Path.Homotopy {V : Sort _} [CombinatorialTwoComplex V] : {v w : V} → (p q : Path v w) → Prop
  | rel : {v w : V} → {p q : Path v w} → NullHomotopy (.append p q.inverse) → Homotopy p q


namespace NullHomotopy

variable {V : Sort _} [C : CombinatorialTwoComplex V] {u v w : V} (l l' : Loop v)

def subst : {u v : V} → (h : u = v) → (l : Loop u) → (l' : Loop v) → (l = (congrArg Loop h) ▸ l') → NullHomotopy l → NullHomotopy l'
  | _, _, rfl, _, _, rfl => id

def swap {u v : V} : {p : Path u v} → {q : Path v u} → NullHomotopy (.append p q) → NullHomotopy (.append q p)
  | .nil, _ => by rw [Path.append_nil]; exact id
  | .cons _ _, _ => by
    dsimp [Path.append]
    intro r
    let r' := NullHomotopy.rotate r
    dsimp [Loop.next, Path.first, Loop.rotate] at r'
    rw [Path.append_cons]
    apply swap
    rw [Path.append_snoc]
    exact r'

def delete' {v : V} {l l' : Loop v} (r : NullHomotopy l) (r' : NullHomotopy (.append l' l)) : NullHomotopy l' :=
  NullHomotopy.delete r $ swap r'

def contract {u v : V} {p : Path u v} {l : Loop v} (rel : NullHomotopy l) {q : Path v u} : NullHomotopy (.append p (.append l q)) → NullHomotopy (.append p q) := by
  intro r
  let r' := swap r
  rw [Path.append_assoc] at r'
  let r'' := delete rel r'
  exact swap r''

def splice {u v : V} {p : Path u v} {l : Loop v} (rel : NullHomotopy l) {q : Path v u} : NullHomotopy (.append p q) → NullHomotopy (.append p (.append l q)) := by
  intro r
  apply swap
  rw [Path.append_assoc]
  apply concat rel
  apply swap
  exact r

def trivial {u v : V} : (p : Path u v) → NullHomotopy (.append p p.inverse)
  | .nil => .nil
  | .cons e p' => by
    rename_i x
    dsimp [Path.append, Path.inverse]
    rw [Path.append_snoc]
    rw [← Path.snoc_cons]
    let erel : Loop x := .cons (SerreGraph.op e) (.cons e .nil)
    let l : Loop x := .append erel (.append p' p'.inverse)
    show NullHomotopy l.rotate
    apply NullHomotopy.rotate
    apply NullHomotopy.concat
    · apply NullHomotopy.relator
      apply CombinatorialTwoComplex.inv
    · apply trivial

def inv {v : V} {l : Loop v} : NullHomotopy l → NullHomotopy l.inv
  | .nil => .nil
  | .relator d => .relator $ CombinatorialTwoComplex.flip d
  | .concat r r' => by
      rw [Loop.inv, Path.inverse_append]
      apply NullHomotopy.concat
      · exact inv r'
      · exact inv r
  | .delete r r' => by
      let r'' := inv r'
      rw [Loop.inv, Path.inverse_append] at r''
      exact NullHomotopy.delete' (inv r) r''
  | .rotate r => by
      apply subst (Loop.prev_inv _ _)
      · apply Loop.rotate'_inv
      · exact rotate' <| inv r
  | .rotate' r => by
      apply subst (Loop.next_inv _ _)
      · apply Loop.rotate_inv
      · exact rotate <| inv r

end NullHomotopy


namespace Path.Homotopy

variable {V : Sort _} [C : CombinatorialTwoComplex V] {u v : V} (p q r : Path u v)

theorem refl : (p : Path u v) → Path.Homotopy p p := (.rel $ NullHomotopy.trivial ·)

theorem symm : Path.Homotopy p q → Path.Homotopy q p
  | .rel h => by
    let h' := h.inv
    rw [Loop.inv, Path.inverse_append, Path.inverse_inv] at h'
    exact .rel h'

theorem trans : Path.Homotopy p q → Path.Homotopy q r → Path.Homotopy p r
  |.rel h, .rel h' => by
    let H := NullHomotopy.concat h h'
    rw [Path.append_assoc p _ _, ← Path.append_assoc _ q _] at H
    let H' := NullHomotopy.contract (.swap $ .trivial _) H
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
    apply NullHomotopy.swap
    apply NullHomotopy.trivial

theorem inv_cancel_right (p : Path u v) : Path.Homotopy (.append p (.inverse p)) .nil := 
  .rel $ by
    simp [inverse]
    apply NullHomotopy.trivial

theorem mul_sound {u v w : V} {p q : Path u v} {r s : Path v w} : 
  Path.Homotopy p q → Path.Homotopy r s → 
  Path.Homotopy (.append p r) (.append q s)
  | .rel a, .rel b  => .rel $ by
    rw [inverse_append, append_assoc, ← append_assoc _ _ (inverse q)]
    exact NullHomotopy.splice b a

theorem inv_sound {u v : V} {p q : Path u v} : 
  Path.Homotopy p q → 
  Path.Homotopy p.inverse q.inverse
  | .rel r =>.rel $ by
    rw [← inverse_append]
    apply NullHomotopy.inv
    apply NullHomotopy.swap
    exact r

end Path.Homotopy
