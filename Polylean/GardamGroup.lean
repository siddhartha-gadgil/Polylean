import Mathlib.Data.Fin.Basic
import Polylean.MetabelianGroup
import Polylean.ProductGroups
import Polylean.EnumDecide
import Polylean.FreeAbelianGroup

/-
We construct the group `P` (the *Promislow* or *Hantzsche–Wendt* group) as a Metabelian group.

This is done via the cocycle construction, using the explicit action and cocycle described in Section 3.1 of Gardam's paper (https://arxiv.org/abs/2102.11818).
-/

namespace P

-- the "kernel" group
abbrev K := ℤ × ℤ × ℤ

instance KGrp : AddCommGroup K := inferInstance

-- the "quotient" group
abbrev Q := Fin 2 × Fin 2

instance QGrp : AddCommGroup Q := inferInstance

-- group elements

abbrev x : K := (1, 0, 0)
abbrev y : K := (0, 1, 0)
abbrev z : K := (0, 0, 1)

abbrev e  : Q := (⟨0, by decide⟩, ⟨0, by decide⟩)
abbrev a  : Q := (⟨1, by decide⟩, ⟨0, by decide⟩)
abbrev b  : Q := (⟨0, by decide⟩, ⟨1, by decide⟩)
abbrev ab : Q := (⟨1, by decide⟩, ⟨1, by decide⟩)

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

-- the action of `Q` on `K` by automorphisms
-- `id` and `neg` are the identity and negation homomorphisms
def action : Q → K → K
  | (⟨0, _⟩, ⟨0, _⟩) => id × id × id
  | (⟨0, _⟩, ⟨1, _⟩) => neg × id × neg
  | (⟨1, _⟩, ⟨0, _⟩) => id × neg × neg
  | (⟨1, _⟩, ⟨1, _⟩) => neg × neg × id

-- a helper function to easily prove theorems about Q by cases
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
  revert q; apply Q.rec <;> rw [action] <;> exact inferInstance

-- confirm that the above action is an action by automorphisms
-- this is done automatically with the machinery of decidable equality of homomorphisms on free groups
instance : AutAction Q K action :=
  {
    aut_action := inferInstance
    id_action := rfl
    compatibility := by decide
  }


-- the cocycle in the construction
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

-- confirm that the above function indeed satisfies the cocycle condition
-- this is done fully automatically by previously defined decision procedures
instance P_cocycle : Cocycle action cocycle :=
  {
    cocycleId := rfl
    cocycleCondition := by decide
  }

-- the group `P` constructed via the cocycle construction

abbrev P := K × Q

instance PGrp : Group P := MetabelianGroup.metabeliangroup action cocycle

instance : DecidableEq P := inferInstanceAs (DecidableEq (K × Q))

-- a handy theorem for describing the group multiplication
@[simp] theorem P_mul : ∀ k k' : K, ∀ q q' : Q, (k, q) * (k', q') = (k + action q k' + cocycle q q', q + q') :=
  λ k k' q q' => by
    show PGrp.mul (k, q) (k', q') = _
    simp [Mul.mul, MetabelianGroup.mul]
    rfl

end P
