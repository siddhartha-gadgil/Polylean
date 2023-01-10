import Mathlib.Algebra.Group.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Aesop

/-
An action of one group on another by automorphisms. 
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

attribute [simp] id_action
attribute [simp] compatibility

instance : AddAction A B where
  vadd := fun a b => α a b
  zero_vadd := (by aesop : ∀ b : B, α 0 b = b)
  add_vadd := by
    intros a a' b
    show α (a + a') b = α a (α a' b)
    simp

@[simp] theorem vadd_eq : ∀ {a : A} {b : B}, a +ᵥ b = α a b := rfl

@[simp] theorem vadd_zero : ∀ {a : A}, a +ᵥ (0 : B) = (0 : B) := by aesop

@[simp] theorem vadd_dist : ∀ {a : A} {b b' : B}, a +ᵥ (b + b') = (a +ᵥ b) + (a +ᵥ b') := by aesop

@[simp] theorem vadd_neg : ∀ {a : A} {b : B}, a +ᵥ (-b) = - (a +ᵥ b) := by aesop

end AutAction
