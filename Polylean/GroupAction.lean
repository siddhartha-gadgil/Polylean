import Polylean.Morphisms

/-
Define group actions. This is done as a typeclass representing the property of being a group action.
-/

class SMul (α β : Type _) where
  sMul : α → β → β

infix:100 " • " => SMul.sMul

class Group.Action (G X : Type _) [Group G] extends SMul G X where
  id_action : ∀ x : X, (1 : G) • x = x
  compatibility : ∀ g g' : G, ∀ x : X, (g * g') • x = g • (g' • x)

class AddCommGroup.Action (A X : Type _) [AddCommGroup A] extends SMul A X where
  id_action : ∀ x : X, (0 : A) • x = x
  compatibiity : ∀ a a' : A, ∀ x : X, (a + a') • x = a • (a' • x)

class AddCommGroup.ActionByAutomorphisms (A B : Type _) [AddCommGroup A] [AddCommGroup B] extends AddCommGroup.Action A B where
  add_dist : ∀ a : A, ∀ b b' : B, a • (b + b') = a • b + a • b'

-- an alternative definition for actions of a group by automorphisms
class AutAction (A B : Type _) [AddCommGroup A] [AddCommGroup B] extends SMul A B where
  [aut_action : ∀ a : A, AddCommGroup.Homomorphism (sMul a)]
  id_action : sMul a = id
  compatibility : ∀ a a' : A, sMul (a + a') = sMul a ∘ sMul a'
