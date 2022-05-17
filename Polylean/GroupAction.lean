import Mathlib.Algebra.Group.Defs

/-
Define group actions. This is done as a typeclass representing the property of being a group action.
-/

class SMul (α β : Type _) where
  sMul : α → β → β

infix:100 " • " => SMul.sMul

class GroupAction (G X : Type _) [Group G] extends SMul G X where
  id_action : ∀ x : X, (1 : G) • x = x
  combatibility : ∀ g g' : G, ∀ x : X, (g * g') • x = g • (g' • x)
