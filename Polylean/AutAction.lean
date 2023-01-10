import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Polylean.Tactics.ReduceGoal
import Aesop

/-!
The definition of an action of one group on another by automorphisms. 
This is done as a typeclass representing the property of being an action by automorphisms.
-/

/-- An action of an additive group on another additive group by automorphisms. -/
class AutAction (A B : Type _) [AddCommGroup A] [AddCommGroup B] (α : A → (B →+ B)) where
  /-- The automorphism corresponding to the zero element is the identity. -/
  id_action : α 0 = .id _
  /-- The compatibility of group addition with the action by automorphisms. -/
  compatibility : ∀ a a' : A, α (a + a') = α a ∘ α a'


namespace AutAction

variable (A B : Type _) [AddCommGroup A] [AddCommGroup B] (α : A → (B →+ B)) [AutAction A B α]

declare_aesop_rule_sets [AutAction]

attribute [aesop norm (rule_sets [AutAction])] id_action
attribute [aesop norm (rule_sets [AutAction])] compatibility

/-- An action by automorphisms of additive groups is an additive group action. -/
instance : AddAction A B where
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
theorem vadd_eq : ∀ {a : A} {b : B}, a +ᵥ b = α a b := rfl

@[aesop norm (rule_sets [AutAction])]
theorem vadd_zero : ∀ {a : A}, a +ᵥ (0 : B) = (0 : B) := by aesop (rule_sets [AutAction])

@[aesop norm (rule_sets [AutAction])]
theorem vadd_dist : ∀ {a : A} {b b' : B}, a +ᵥ (b + b') = (a +ᵥ b) + (a +ᵥ b') := by aesop (rule_sets [AutAction])

@[aesop norm (rule_sets [AutAction])]
theorem vadd_neg : ∀ {a : A} {b : B}, a +ᵥ (-b) = - (a +ᵥ b) := by aesop (rule_sets [AutAction])

end AutAction
