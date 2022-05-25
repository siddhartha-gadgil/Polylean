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

instance KGrp : AddCommGroup K := inferInstance

abbrev Q := Fin 2 × Fin 2

instance QGrp : AddCommGroup Q := inferInstance

abbrev x : K := (1, 0, 0)
abbrev y : K := (0, 1, 0)
abbrev z : K := (0, 0, 1)

abbrev e  : Q := (⟨0, by decide⟩, ⟨0, by decide⟩)
abbrev a  : Q := (⟨1, by decide⟩, ⟨0, by decide⟩)
abbrev b  : Q := (⟨0, by decide⟩, ⟨1, by decide⟩)
abbrev ab : Q := (⟨1, by decide⟩, ⟨1, by decide⟩)

-- perhaps an unnecessary theorem
theorem K_add (p q r p' q' r' : ℤ) : (p, q, r) + (p', q', r') = (p + p', q + q', r + r') := by
  show Add.add (p, q, r) (p', q', r') = _
  simp [DirectSum.directSum_add]
  show Add.add (q, r) (q', r') = _
  simp [DirectSum.directSum_add]

section Demo

abbrev X := Unit ⊕ Unit ⊕ Unit

def egActionBasis' : Fin 2 → Unit → ℤ 
| ⟨0, _⟩ => fun _ => 1
| ⟨1, _⟩ => fun _ => -1

def actionBasis' : Q → X → K
| (⟨0, _⟩, ⟨0, _⟩)  => Z3.onX ((1, 0, 0), (0, 1, 0), (0, 0, 1))
| (⟨0, _⟩, ⟨1, _⟩)  => Z3.onX ((-1, 0, 0), (0, 1, 0), (0, 0, -1))
| (⟨1, _⟩, ⟨0, _⟩)  => Z3.onX ((1, 0, 0), (0, -1, 0), (0, 0, -1))
| (⟨1, _⟩, ⟨1, _⟩)  => Z3.onX ((-1, 0, 0), (0, -1, 0), (0, 0, 1))

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
  | (⟨0, _⟩, ⟨0, _⟩)  , (p, q, r) => (p, q, r)
  | (⟨0, _⟩, ⟨1, _⟩)  , (p, q, r) => (-p, q, -r)
  | (⟨1, _⟩, ⟨0, _⟩)  , (p, q, r) => (p, -q, -r)
  | (⟨1, _⟩, ⟨1, _⟩)  , (p, q, r) => (-p, -q, r)
-/

def action : Q → K → K
  | (⟨0, _⟩, ⟨0, _⟩) => id × id × id
  | (⟨0, _⟩, ⟨1, _⟩) => neg × id × neg
  | (⟨1, _⟩, ⟨0, _⟩) => id × neg × neg
  | (⟨1, _⟩, ⟨1, _⟩) => neg × neg × id

def Q.rec (P : Q → Sort _) :
  P (⟨0, by decide⟩, ⟨0, by decide⟩) →
  P (⟨0, by decide⟩, ⟨1, by decide⟩) →
  P (⟨1, by decide⟩, ⟨0, by decide⟩) →
  P (⟨1, by decide⟩, ⟨1, by decide⟩) →
  ------------------------------------
  ∀ (q : Q), P q :=
    λ p00 p01 p10 p11 q =>
      match q with
        | (⟨0, _⟩, ⟨0, _⟩) => p00
        | (⟨0, _⟩, ⟨1, _⟩) => p01
        | (⟨1, _⟩, ⟨0, _⟩) => p10
        | (⟨1, _⟩, ⟨1, _⟩) => p11

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

instance P_action : AddCommGroup.ActionByAutomorphisms Q K := @actionaut _ _ _ _ inferInstance

def cocycle : Q → Q → K
  | (⟨0, _⟩, ⟨0, _⟩) , (⟨0, _⟩, ⟨0, _⟩)  => 0
  | (⟨0, _⟩, ⟨0, _⟩) , (⟨0, _⟩, ⟨1, _⟩)  => 0
  | (⟨0, _⟩, ⟨0, _⟩) , (⟨1, _⟩, ⟨0, _⟩)  => 0
  | (⟨0, _⟩, ⟨0, _⟩) , (⟨1, _⟩, ⟨1, _⟩)  => 0
  | (⟨0, _⟩, ⟨1, _⟩) , (⟨0, _⟩, ⟨0, _⟩)  => 0
  | (⟨0, _⟩, ⟨1, _⟩) , (⟨0, _⟩, ⟨1, _⟩)  => y
  | (⟨0, _⟩, ⟨1, _⟩) , (⟨1, _⟩, ⟨0, _⟩)  => -x + y + -z
  | (⟨0, _⟩, ⟨1, _⟩) , (⟨1, _⟩, ⟨1, _⟩)  => -x + -z
  | (⟨1, _⟩, ⟨0, _⟩) , (⟨0, _⟩, ⟨0, _⟩)  => 0
  | (⟨1, _⟩, ⟨0, _⟩) , (⟨0, _⟩, ⟨1, _⟩)  => 0
  | (⟨1, _⟩, ⟨0, _⟩) , (⟨1, _⟩, ⟨0, _⟩)  => x
  | (⟨1, _⟩, ⟨0, _⟩) , (⟨1, _⟩, ⟨1, _⟩)  => x
  | (⟨1, _⟩, ⟨1, _⟩) , (⟨0, _⟩, ⟨0, _⟩)  => 0
  | (⟨1, _⟩, ⟨1, _⟩) , (⟨0, _⟩, ⟨1, _⟩)  => -y
  | (⟨1, _⟩, ⟨1, _⟩) , (⟨1, _⟩, ⟨0, _⟩)  => -y + z
  | (⟨1, _⟩, ⟨1, _⟩) , (⟨1, _⟩, ⟨1, _⟩)  => z

instance P_cocycle : Cocycle cocycle :=
  {
    cocycleId := rfl
    cocycleCondition := by decide
  }


def P := K × Q

instance PGrp : Group P := MetabelianGroup.metabeliangroup cocycle

instance : DecidableEq P := inferInstanceAs (DecidableEq (K × Q))

theorem P_mul : ∀ k k' : K, ∀ q q' : Q, (k, q) * (k', q') = (k + action q k' + cocycle q q', q + q') :=
  λ k k' q q' => by
    show PGrp.mul (k, q) (k', q') = _
    simp [Mul.mul, MetabelianGroup.mul]
    have : q • k' = action q k' := rfl
    rw [this]

end P
