import Polylean.Complexes.Structures.Quiver

/-- Serre's definition of an undirected graph. -/
class SerreGraph (V : Sort _) extends Quiver V where
  op : {A B : V} → (A ⟶ B) → (B ⟶ A)
  opInv : {A B : V} → (e : A ⟶ B) → op (op e) = e

attribute [reducible] SerreGraph.op
attribute [simp] SerreGraph.opInv

/-- Every `Quiver` can be turned into a `SerreGraph` by adding a formal inverse for each edge. -/
def Quiver.symmetrize {V : Sort _} (Q : Quiver V) : SerreGraph V :=
{ hom := λ A B => Q.hom A B ⊕ Q.hom B A,
  op := fun | .inl e => .inr e | .inr e => .inl e,
  opInv := fun | .inl _ => rfl | .inr _ => rfl }


namespace Path

variable {V : Sort _} [G : SerreGraph V] {A B C : V} (p : Path A B)

/-- The inverse of a path in a Serre graph. -/
def inverse {A B : V} : Path A B → Path B A
  | .nil => .nil
  | .cons e p => .snoc p.inverse (SerreGraph.op e)

@[simp] theorem inverse_snoc {A B : V} : (p : Path A B) → (e : B ⟶ C) → 
  inverse (.snoc p e) = .cons (SerreGraph.op e) (inverse p)
  | .nil, e => rfl
  | .cons e' p', e => by dsimp [inverse]; rw [inverse_snoc p' e]

@[simp] theorem inverse_inv {A B : V} : (p : Path A B) → p.inverse.inverse = p
  | .nil => rfl
  | .cons e p' => by simp [inverse]; apply inverse_inv

@[simp] theorem inverse_append {A B C : V} : (p : Path A B) → (q : Path B C) → 
    inverse (append p q) = .append (inverse q) (inverse p)
  | .nil, q => by simp [inverse]
  | p, .nil => by simp [inverse]
  | .cons _ p', .cons _ q' => by
    dsimp [inverse]
    rw [inverse_append p' _, append_snoc]
    rfl

theorem length_inverse {A B : V} : (p : Path A B) → p.inverse.length = p.length
  | .nil => rfl
  | .cons _ p' => by
    dsimp [inverse, length]
    rw [snoc_length]
    apply congrArg
    apply length_inverse

theorem first_eq_inv_last : {A B : V} →
    (p : Path A B) → p.first = p.inverse.last
  | _, _, .nil => rfl
  | _, _, .cons e p' => by simp [first, last, inverse, snoc, last_snoc]

theorem last_eq_inv_first :
    (p : Path A B) → p.last = p.inverse.first := by
    intro p
    let p' := p.inverse
    have pinv : p = p'.inverse := by simp
    rw [pinv, inverse_inv p']
    apply Eq.symm
    apply first_eq_inv_last

end Path


namespace Loop

variable {V : Sort _} [SerreGraph V] (A : V)

abbrev inv {A : V} : Loop A → Loop A := Path.inverse

@[simp] theorem inv_inv (l : Loop A) : l.inv.inv = l := by simp

-- alternative to using `Path.last`
abbrev prev : Loop A → V := λ l => (l.inv).next

def rotate : (l : Loop A) → Loop (l.next A)
  | .nil' A => .nil' A
  | .cons' _ _ _ e p => p.snoc e

def rotate' : (l : Loop A) → Loop (l.prev A) :=
  λ l => ((l |>.inv) |>.rotate) |>.inv


@[simp] theorem inv_rotate_inv (l : Loop A) : 
  (rotate A l.inv).inv = rotate' A l := by simp [rotate']

@[simp] theorem prev_inv (l : Loop A) : (prev A l.inv) = next A l := by simp [prev]

@[simp] theorem next_inv (l : Loop A) : (next A l.inv) = prev A l := by simp

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

theorem rotate'_inv_heq (l : Loop A) : HEq (rotate' A l.inv) (rotate A l).inv := by
  rw [← inv_rotate_inv A l.inv]
  congr 2 <;> rw [inv_inv]

theorem rotate_inv_heq (l : Loop A) : HEq (rotate A l.inv) (rotate' A l).inv := by
  rw [rotate', inv_inv]
  exact .refl _

theorem HEq.toEqCast {A B : Sort _} {a : A} {b : B} : (h : A = B) → HEq a b → a = h ▸ b
  | rfl, .refl _ => rfl

theorem rotate'_inv (l : Loop A) : (rotate' A l.inv) = (congrArg Loop $ prev_inv A l) ▸ (rotate A l).inv := 
  HEq.toEqCast (congrArg Loop $ prev_inv A l) (rotate'_inv_heq A l)

theorem rotate_inv (l : Loop A) : (rotate A l.inv) = (congrArg Loop $ next_inv A l) ▸ (rotate' A l).inv :=
  HEq.toEqCast (congrArg Loop $ next_inv A l) (rotate_inv_heq A l)

end Loop