import Polylean.Morphisms
import Polylean.SMul

/-!
## Group Actions

We define group actions. This is done as a typeclass representing the property of being a group action.
-/


class Group.Action (G X : Type _) [Group G] extends SMul G X where
  id_action : ∀ x : X, (1 : G) • x = x
  compatibility : ∀ g g' : G, ∀ x : X, (g * g') • x = g • (g' • x)

attribute [simp] Group.Action.id_action
attribute [simp] Group.Action.compatibility

class AddCommGroup.Action (A X : Type _) [AddCommGroup A] extends SMul A X where
  id_action : ∀ {x : X}, (0 : A) • x = x
  compatibility : ∀ {a a' : A}, ∀ {x : X}, (a + a') • x = a • (a' • x)

attribute [simp] AddCommGroup.Action.id_action
attribute [simp] AddCommGroup.Action.compatibility

class AutAction (A B : Type _) [AddCommGroup A] [AddCommGroup B] (α : A → B → B) where
  [aut_action : ∀ a : A, AddCommGroup.Homomorphism (α a)]
  id_action : α 0 = id
  compatibility : ∀ a a' : A, α (a + a') = α a ∘ α a'


namespace AutAction

variable (A B : Type _) [AddCommGroup A] [AddCommGroup B] (α : A → B → B) [AA : AutAction A B α]

attribute [simp] id_action
attribute [simp] compatibility

instance : AddCommGroup.Action A B where
    id_action := λ {x : B} => congrFun AA.id_action x
    compatibility := λ {a a' : A} {x : B} => congrFun (AA.compatibility a a') x

instance (a : A) : AddCommGroup.Homomorphism (α a) := aut_action a

@[simp] theorem act_zero : ∀ {a : A}, a • (0 : B) = (0 : B) := by intro; simp [SMul.sMul]

@[simp] theorem add_dist : ∀ {a : A}, ∀ {b b' : B}, a • (b + b') = a • b + a • b' := by intro; simp [SMul.sMul]

@[simp] theorem neg_push : ∀ {a : A}, ∀ {b : B}, a • (-b) = - (a • b) := by intros; simp [SMul.sMul]

end AutAction
