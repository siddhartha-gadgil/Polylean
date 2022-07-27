import Mathlib.Data.Fin.Basic
import Polylean.MetabelianGroup
import Polylean.ProductGroups
import Polylean.EnumDecide
import Polylean.FreeAbelianGroup

/-!
## The Group `P`

We construct the group `P` (the *Promislow* or *Hantzsche–Wendt* group) as a Metabelian group.

This is done via the cocycle construction, using the explicit action and cocycle described in Section 3.1 of [Gardam's paper](https://arxiv.org/abs/2102.11818).
-/

namespace P

/-! The *kernel* group -/
abbrev K := ℤ × ℤ × ℤ

instance KGrp : AddCommGroup K := inferInstance

/-! The *quotient* group -/
abbrev Q := Fin 2 × Fin 2

instance QGrp : AddCommGroup Q := inferInstance

/-! ### The group elements -/

abbrev x : K := (1, 0, 0)
abbrev y : K := (0, 1, 0)
abbrev z : K := (0, 0, 1)

@[matchPattern] abbrev e  : Q := (0, 0)
@[matchPattern] abbrev a  : Q := (1, 0)
@[matchPattern] abbrev b  : Q := (0, 1)
@[matchPattern] abbrev ab : Q := (1, 1)

/-!
### The action of `Q` on `K` by automorphisms
Here `id` and `neg` are the identity and negation homomorphisms
-/

@[reducible] def action : Q → (K → K)
  | e => id × id × id
  | a => id × neg × neg
  | b => neg × id × neg
  | ab => neg × neg × id

/-- A helper function to easily prove theorems about `Q` by cases -/
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

/-- The outputs of the `action` are are automorphisms -/
instance (q : Q) : AddCommGroup.Homomorphism (action q) := by
  cases q using Q.rec <;> exact inferInstance

/-- A verification that the action is indeed an action by automorphisms,
done automatically with the machinery of decidable equality of homomorphisms on free groups -/
instance : AutAction Q K action :=
  {
    aut_action := inferInstance
    id_action := rfl
    compatibility := by decide
  }


/-! ### The cocycle in the construction -/
@[reducible] def cocycle : Q → Q → K
  | a , a  => x
  | a , ab => x
  | b , b  => y
  | ab, b  => -y
  | ab, ab => z
  | b , ab => -x + -z
  | ab, a  => -y + z
  | b , a  => -x + y + -z
  | _ , _  => 0

/-- A verification that the cocycle indeed satisfies the cocycle condition,
done fully automatically by previously defined decision procedures -/
instance P_cocycle : Cocycle cocycle :=
  {
    α := action
    autaction := inferInstance
    cocycleId := rfl
    cocycleCondition := by decide
  }


/-- The group `P`, constructed via the cocycle construction on the underlying set `ℤ³ × (ℤ₂ × ℤ₂)` -/
abbrev P := K × Q

/- A group structure on the type `P` coming from the explicit action and cocycle -/
instance PGrp : Group P := MetabelianGroup.metabeliangroup cocycle

instance : DecidableEq P := inferInstanceAs (DecidableEq (K × Q))

/- A confirmation that multiplication in `P` is as expected -/
@[reducible, simp] theorem Pmul (k k' : K) (q q' : Q) : (k, q) * (k', q') = (k + action q k' + cocycle q q', q + q') := rfl

theorem one : (1 : P) = ((0, 0, 0), P.e) := rfl

end P
