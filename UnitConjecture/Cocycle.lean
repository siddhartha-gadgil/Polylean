import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import UnitConjecture.Tactics.ReduceGoal
import Aesop

/-!
## Group actions by automorphisms and Cocycles
The definitions of cocycles and group actions by automorphisms, which are required for the Metabelian construction.

## Overview
- `AutAction` - the definition of an action of one group on another by automorphisms. 
  This is done as a typeclass representing the property of being an action by automorphisms.
- `Cocycle` - the definition of a *cocycle* associated with a certain action by automorphisms.
  This is also done as a typeclass with the function as an explicit argument and the action as a field of the structure.
-/

/-!
### Actions by automorphisms
-/

/-- An action of an additive group on another additive group by automorphisms. 
    There is a closely related typeclass `DistribMulAction` in `Mathlib` that uses multiplicative notation. -/
class AutAction (A B : Type _) [AddGroup A] [AddGroup B] (α : A → (B →+ B)) where
  /-- The automorphism corresponding to the zero element is the identity. -/
  id_action : α 0 = .id _
  /-- The compatibility of group addition with the action by automorphisms. -/
  compatibility : ∀ a a' : A, α (a + a') = (α a).comp (α a')


namespace AutAction

variable (A B : Type _) [AddGroup A] [AddGroup B] (α : A → (B →+ B)) [AutAction A B α]

declare_aesop_rule_sets [AutAction]

attribute [aesop norm (rule_sets [AutAction])] id_action
attribute [aesop norm (rule_sets [AutAction])] compatibility

/-- An action by automorphisms of additive groups is an additive group action. -/
instance toAddAction : AddAction A B where
  vadd := fun a b => α a b
  zero_vadd := (by aesop (rule_sets [AutAction]) : ∀ b : B, α 0 b = b)
  add_vadd := by
    intros a a' b
    show α (a + a') b = α a (α a' b)
    aesop (rule_sets [AutAction])

/-!
Some easy consequences of the definition of an action by automorphisms.
-/

@[aesop norm (rule_sets [AutAction])]
lemma vadd_eq : ∀ {a : A} {b : B}, a +ᵥ b = α a b := rfl

@[aesop norm (rule_sets [AutAction])]
lemma vadd_zero : ∀ {a : A}, a +ᵥ (0 : B) = (0 : B) := by aesop (rule_sets [AutAction])

@[aesop unsafe (rule_sets [AutAction])]
lemma vadd_dist : ∀ {a : A} {b b' : B}, a +ᵥ (b + b') = (a +ᵥ b) + (a +ᵥ b') := by aesop (rule_sets [AutAction])

@[aesop unsafe (rule_sets [AutAction])]
lemma compatibility' : ∀ {a a' : A} {b : B}, α a (α a' b) = α (a + a') b := by aesop (rule_sets [AutAction]) 

@[aesop norm (rule_sets [AutAction])]
lemma act_neg_act {a : A} {b : B} : α a (α (-a) b) = b := by
  rw [compatibility']
  aesop (erase compatibility) (rule_sets [AutAction])

@[aesop unsafe (rule_sets [AutAction])]
lemma vadd_of_neg : ∀ {a : A} {b : B}, a +ᵥ (-b) = - (a +ᵥ b) := by aesop (rule_sets [AutAction])

end AutAction


/-!
### Cocycles
-/

/--
A cocycle associated with a certain action of `Q` on `K` via automorphisms is a function from `Q × Q` to `K` satisfying
a certain requirement known as the "cocycle condition". This allows one to define an associative multiplication operation on the set `K × Q` as shown below.
The requirement `c 0 0 = (0 : K)` is not strictly necessary and mainly for convenience.
-/
class Cocycle {Q K : Type _} [AddGroup Q] [AddGroup K] (c : Q → Q → K) where
  /-- An action of the quotient on the kernel by automorphisms. -/
  α : Q → (K →+ K)
  /-- A typeclass instance for the action by automorphisms. -/
  [autAct : AutAction Q K α]
  /-- The value of the cocycle is zero when its inputs are zero, as a convention. -/
  cocycle_zero : c 0 0 = (0 : K)
  /-- The *cocycle condition*. -/
  cocycle_condition : ∀ q q' q'' : Q, c q q' + c (q + q') q'' = q +ᵥ c q' q'' + c q (q' + q'')


namespace Cocycle

/-!
A few deductions from the cocycle condition.
-/

declare_aesop_rule_sets [Cocycle]

variable {Q K : Type _} [AddGroup Q] [AddGroup K]
variable (c : Q → Q → K) [ccl : Cocycle c]

attribute [aesop norm (rule_sets [Cocycle])] Cocycle.cocycle_zero
attribute [aesop norm (rule_sets [Cocycle])] Cocycle.cocycle_condition

instance : AutAction Q K ccl.α := ccl.autAct

@[aesop norm (rule_sets [Cocycle])]
lemma left_id {q : Q} : c 0 q = (0 : K) := by
  have := ccl.cocycle_condition 0 0 q
  aesop (rule_sets [Cocycle])

@[aesop norm (rule_sets [Cocycle])]
lemma right_id {q : Q} : c q 0 = (0 : K) := by
  have := ccl.cocycle_condition q 0 0
  aesop (rule_sets [AutAction, Cocycle])

@[aesop unsafe (rule_sets [Cocycle])]
lemma inv_rel (q : Q) : c q (-q) = q +ᵥ (c (-q) q) := by
  have := ccl.cocycle_condition q (-q) q
  aesop (rule_sets [AutAction, Cocycle])

@[aesop unsafe (rule_sets [Cocycle])]
lemma inv_rel' (q : Q) : c (-q) q = (-q) +ᵥ (c q (-q)) := by
  have := inv_rel c (-q)
  aesop

end Cocycle