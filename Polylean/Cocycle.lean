import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Polylean.Tactics.ReduceGoal
import Aesop

/-!
The definition of a cocycle through a typeclass.
-/

/--
A cocycle associated with a certain action of `Q` on `K` via automorphisms is a function from `Q × Q` to `K` satisfying
a certain requirement known as the "cocycle condition". This allows one to define an associative multiplication operation on the set `K × Q` as shown below.
The requirement `c 1 1 = (0 : K)` is not strictly necessary and mainly for convenience.
-/
class Cocycle {Q K : Type _} [Group Q] [AddCommGroup K] (c : Q → Q → K) where
  /-- An action of the quotient on the kernel by automorphisms. -/
  [autAct : DistribMulAction Q K]
  /-- The value of the cocycle is the identity when its inputs are the identity, as a convention. -/
  cocycle_id : c 1 1 = (0 : K)
  /-- The *cocycle condition*. -/
  cocycle_condition : ∀ q q' q'' : Q, c q q' + c (q * q') q'' = q • (c q' q'') + c q (q' * q'')


namespace Cocycle

/-!
A few deductions from the cocycle condition.
-/

declare_aesop_rule_sets [Cocycle]

variable {Q K : Type _} [Group Q] [AddCommGroup K]
variable (c : Q → Q → K) [ccl : Cocycle c]

attribute [aesop norm (rule_sets [Cocycle])] Cocycle.cocycle_id
attribute [aesop norm (rule_sets [Cocycle])] Cocycle.cocycle_condition

instance : DistribMulAction Q K := ccl.autAct

@[aesop norm (rule_sets [Cocycle])]
lemma left_id {q : Q} : c 1 q = (0 : K) := by
  have := ccl.cocycle_condition 1 1 q
  aesop (rule_sets [Cocycle])

@[aesop norm (rule_sets [Cocycle])]
lemma right_id {q : Q} : c q 1 = (0 : K) := by
  have := ccl.cocycle_condition q 1 1
  aesop (rule_sets [Cocycle])

@[aesop unsafe (rule_sets [Cocycle])]
lemma inv_rel (q : Q) : c q q⁻¹ = q • (c q⁻¹ q) := by
  have := ccl.cocycle_condition q q⁻¹ q
  aesop (rule_sets [Cocycle])

@[aesop unsafe (rule_sets [Cocycle])]
lemma inv_rel' (q : Q) : c q⁻¹ q = q⁻¹ • (c q q⁻¹) := by
  have := inv_rel c q⁻¹
  aesop

end Cocycle