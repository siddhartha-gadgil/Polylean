import Mathlib.Data.Fin.Basic
import Polylean.MetabelianGroup
import Polylean.ProductGroups
import Polylean.EnumDecide
import Polylean.FreeAbeliaGroup

/-
We construct the group `P` as a Metabelian group. Helper functions for defining elements in the group etc. should be defined.
-/

namespace P

abbrev K := ℤ × ℤ × ℤ

abbrev Q := Fin 2 × Fin 2

def x : K := (1, 0, 0)
def y : K := (0, 1, 0)
def z : K := (0, 0, 1)

abbrev e  : Q := (0, 0)
abbrev a  : Q := (1, 0)
abbrev b  : Q := (0, 1)
abbrev ab : Q := (1, 1)

/- Demo code -/
abbrev X := Unit ⊕ Unit ⊕ Unit

def egActionBasis' : Fin 2 → Unit → ℤ 
| ⟨0, _⟩ => fun _ => 1
| ⟨1, _⟩ => fun _ => -1

def actionBasis' : Q → X → K
| (0, 0) => Z3.onX ((1, 0, 0), (0, 1, 0), (0, 0, 1))
| (0, 1) => Z3.onX ((-1, 0, 0), (0, 1, 0), (0, 0, -1))
| (1, 0) => Z3.onX ((1, 0, 0), (0, -1, 0), (0, 0, -1))
| (1, 1) => Z3.onX ((-1, 0, 0), (0, -1, 0), (0, 0, 1))

abbrev action' := fromBasisFamily K Q actionBasis' -- shows basis is inferred

open EnumDecide

instance dfQ : DecideForall Q := inferInstance -- a check

-- perhaps `by decide` will work if there are no holes
theorem isAction: ∀ (x y: Q), 
  (action' x) ∘ (action' y) = action' (x + y) := by 
    intro x y
    let chk : AddCommGroup.Homomorphism (action' x) := inferInstance
    let chk' : AddCommGroup.Homomorphism <| 
         (action' x) ∘  (action' y) := inferInstance
    apply @unique_extension _ _ X
    apply funext 
    simp
    admit 

abbrev egAction' := fromBasisFamily ℤ (Fin 2)  (egActionBasis')



theorem egIsAction: ∀ (x y: Fin 2), 
  (egAction' x) ∘ (egAction' y) = egAction' (x + y) := by decide -- works!

/- Demo end -/

def action : Q → K → K
  | (0, 0) , (p, q, r) => (p, q, r)
  | (0, 1) , (p, q, r) => (-p, q, -r)
  | (1, 0) , (p, q, r) => (p, -q, -r)
  | (1, 1) , (p, q, r) => (-p, -q, r)

instance : AddCommGroup.ActionByAutomorphisms Q K :=
  {
    sMul := action
    id_action := rfl
    compatibility := sorry
    add_dist := sorry
  }

def cocycle : Q → Q → K
  | (0, 0), (0, 0) => 0
  | (0, 0), (0, 1) => 0
  | (0, 0), (1, 0) => 0
  | (0, 0), (1, 1) => 0
  | (0, 1), (0, 0) => 0
  | (0, 1), (0, 1) => y
  | (0, 1), (1, 0) => -x + y -z
  | (0, 1), (1, 1) => -x -z
  | (1, 0), (0, 0) => 0
  | (1, 0), (0, 1) => 0
  | (1, 0), (1, 0) => x
  | (1, 0), (1, 1) => x
  | (1, 1), (0, 0) => 0
  | (1, 1), (0, 1) => -y
  | (1, 1), (1, 0) => -y + z
  | (1, 1), (1, 1) => z

instance : Cocycle cocycle :=
  {
    cocycleId := rfl
    cocycleCondition := by decide
  }

end P
