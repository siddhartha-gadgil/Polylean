import Polylean.Morphisms
import Polylean.SMul

/-
Define group actions. This is done as a typeclass representing the property of being a group action.
-/


class Group.Action (G X : Type _) [Group G] extends SMul G X where
  id_action : ∀ x : X, (1 : G) • x = x
  compatibility : ∀ g g' : G, ∀ x : X, (g * g') • x = g • (g' • x)

class AddCommGroup.Action (A X : Type _) [AddCommGroup A] extends SMul A X where
  id_action : ∀ {x : X}, (0 : A) • x = x
  compatibility : ∀ {a a' : A}, ∀ {x : X}, (a + a') • x = a • (a' • x)

class AddCommGroup.ActionByAutomorphisms (A B : Type _) [AddCommGroup A] [AddCommGroup B] extends AddCommGroup.Action A B where
  add_dist : ∀ {a : A}, ∀ b b' : B, a • (b + b') = a • b + a • b'

-- an alternative definition for actions of a group by automorphisms
class AutAction (A B : Type _) [AddCommGroup A] [AddCommGroup B] extends SMul A B where
  [aut_action : ∀ a : A, AddCommGroup.Homomorphism (sMul a)]
  id_action : sMul 0 = id
  compatibility : ∀ a a' : A, sMul (a + a') = sMul a ∘ sMul a'

instance (A B : Type _) [AddCommGroup A] [AddCommGroup B] [AA : AutAction A B] : AddCommGroup.Action A B :=
  {
    id_action := λ {x : B} => congrFun AA.id_action x
    compatibility := λ {a a' : A} {x : B} => congrFun (AA.compatibility a a') x
  }

instance actionaut (A B : Type _) [AddCommGroup A] [AddCommGroup B] [AA : AutAction A B] : AddCommGroup.ActionByAutomorphisms A B :=
  {
    add_dist := λ {a} => (AA.aut_action a).add_dist
  }

theorem AddCommGroup.ActionByAutomorphisms.act_zero {A B : Type _} [AddCommGroup A] [AddCommGroup B] [AddCommGroup.ActionByAutomorphisms A B] :
  ∀ {a : A}, a • (0 : B) = (0 : B) := by
    intro a
    have : a • (0 : B) + a • (0 : B) = a • (0 : B) + 0 := by rw [← add_dist, add_zero, add_zero]
    exact add_left_cancel this

theorem AddCommGroup.ActionByAutomorphisms.neg_push {A B : Type _} [AddCommGroup A] [AddCommGroup B] [AddCommGroup.ActionByAutomorphisms A B] :
  ∀ {a : A}, ∀ {b : B}, a • (-b) = - (a • b) := by
    intro a b
    have : a • b + a • (- b) = (a • b) + - (a • b) := by
      rw [← AddCommGroup.ActionByAutomorphisms.add_dist, add_right_neg, act_zero, add_right_neg]
    exact add_left_cancel this
