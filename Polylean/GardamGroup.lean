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

section Demo

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

instance infer_comp_action' (x y : Q) : AddCommGroup.Homomorphism ((action' x) ∘ (action' y)) := inferInstance

theorem isAction: ∀ (x y: Q), (action' x) ∘ (action' y) = action' (x + y) := by decide

abbrev egAction' := fromBasisFamily ℤ (Fin 2)  (egActionBasis')

theorem egIsAction: ∀ (x y: Fin 2), 
  (egAction' x) ∘ (egAction' y) = egAction' (x + y) := by decide -- works!

end Demo

/-
def action : Q → K → K
  | (0, 0) , (p, q, r) => (p, q, r)
  | (0, 1) , (p, q, r) => (-p, q, -r)
  | (1, 0) , (p, q, r) => (p, -q, -r)
  | (1, 1) , (p, q, r) => (-p, -q, r)
-/

def action : Q → K → K
  | (0, 0) => id × id × id
  | (0, 1) => neg × id × neg
  | (1, 0) => id × neg × neg
  | (1, 1) => neg × neg × id

def Q.rec (P : Q → Sort _) :
  P (⟨0, by decide⟩, ⟨0, by decide⟩) →
  P (⟨0, by decide⟩, ⟨1, by decide⟩) →
  P (⟨1, by decide⟩, ⟨0, by decide⟩) →
  P (⟨1, by decide⟩, ⟨1, by decide⟩) →
  ------------------------------------
  ∀ (q : Q), P q :=
    λ p00 p01 p10 p11 q =>
      match q with
        | (0, 0) => p00
        | (0, 1) => p01
        | (1, 0) => p10
        | (1, 1) => p11

instance (q : Q) : AddCommGroup.Homomorphism (action q) := by
  revert q; apply Q.rec <;> simp [action] <;> exact inferInstance

instance (q q' : Q) : AddCommGroup.Homomorphism (action q ∘ action q') := inferInstance

instance : AutAction Q K :=
  {
    sMul := action
    aut_action := by apply Q.rec <;> simp [SMul.sMul, action] <;> exact inferInstance
    id_action := by
      have : (0 : Q) = (⟨0, by decide⟩, ⟨0, by decide⟩) := rfl
      simp [SMul.sMul, this, action]
    compatibility := by
      intro q
      apply Q.rec <;> revert q <;> apply Q.rec <;> simp [SMul.sMul]
  }

instance : AddCommGroup.ActionByAutomorphisms Q K := @actionaut _ _ _ _ inferInstance

def cocycle : Q → Q → K
  | (0, 0), (0, 0) => 0
  | (0, 0), (0, 1) => 0
  | (0, 0), (1, 0) => 0
  | (0, 0), (1, 1) => 0
  | (0, 1), (0, 0) => 0
  | (0, 1), (0, 1) => y
  | (0, 1), (1, 0) => -x + y + -z
  | (0, 1), (1, 1) => -x + -z
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


def P := K × Q

instance PGrp : Group P := MetabelianGroup.metabeliangroup cocycle

end P
