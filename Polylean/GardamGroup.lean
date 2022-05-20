import Mathlib.Data.Fin.Basic
import Polylean.MetabelianGroup
import Polylean.EnumDecide

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
    cocycleCondition := sorry
  }

end P
