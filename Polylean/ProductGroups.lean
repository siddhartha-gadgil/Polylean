import Polylean.MetabelianGroup

/-
Define the product of two groups and related concepts.

Product groups are defined as a special case of the Metabelian construction with trivial action and trivial cocycle.
-/


section Product

variable {Q K : Type _} [AddCommGroup Q] [AddCommGroup K]

def trivial_action : Q → K → K
  | _ => id

-- the trivial action of `Q` on `K`
instance : AutAction Q K trivial_action :=
  {
    id_action := rfl
    compatibility := λ _ _ => rfl
    aut_action := λ _ => inferInstanceAs (AddCommGroup.Homomorphism id)
  }

-- the trivial cocycle
def trivial_cocycle : Q → Q → K
  | _, _ => 0

instance : @Cocycle Q K _ _ trivial_cocycle :=
  {
    α := trivial_action
    autaction := inferInstance
    cocycleId := rfl
    cocycleCondition := λ _ _ _ => rfl
  }

theorem product_comm : ∀ g h : K × Q, MetabelianGroup.mul trivial_cocycle g h = MetabelianGroup.mul trivial_cocycle h g := by
  intro (k, q)
  intro (k', q')
  simp [MetabelianGroup.mul, trivial_cocycle]
  apply And.intro
  · have : ∀ q : Q, ∀ κ : K, q • κ = κ := λ _ _ => rfl
    rw [this, this, add_comm]
  · exact AddCommGroup.add_comm q q'

end Product

namespace DirectSum

variable {A B : Type _} [AddCommGroup A] [AddCommGroup B]

-- Direct sums as an additive version of products
instance directSum : AddCommGroup (A × B) :=
  Group.to_additive product_comm

theorem mul {a a' : A} {b b' : B} : MetabelianGroup.mul trivial_cocycle (a, b) (a', b') = (a + a', b + b') := by
    simp [MetabelianGroup.mul, trivial_cocycle]
    rfl

@[simp] theorem add (a a' : A) (b b' : B) : (a, b) + (a', b') = (a + a', b + b') := mul

end DirectSum


section Homomorphisms

variable {A B C D : Type _} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]

-- products of homomorphisms
-- this is used in defining the group action required for constructing the Metabelian group `P`
def prod (f : A → C) (g : B → D) : A × B → C × D
  | (a, b) => (f a, g b)

infixr:100 " × " => prod

-- showing that the product of homomorphisms is a homomorphism
instance (ϕ : A → C) [ϕHom : AddCommGroup.Homomorphism ϕ] (ψ : B → D) [ψHom : AddCommGroup.Homomorphism ψ] :
  AddCommGroup.Homomorphism (ϕ × ψ) where
    add_dist := by
                intro (a, b)
                intro (a', b')
                simp [trivial_cocycle, MetabelianGroup.mul, prod]
                rfl

abbrev ι₁ [Zero A] [Zero B] : A → A × B := λ a => (a, 0)

abbrev ι₂ [Zero A] [Zero B] : B → A × B := λ b => (0, b)

/-
instance {A B : Type _} [AddCommGroup A] [AddCommGroup B] : AddCommGroup.Homomorphism (@ι₁ A B _ _) where
  add_dist := by intros; simp

instance {A B : Type _} [AddCommGroup A] [AddCommGroup B] : AddCommGroup.Homomorphism (@ι₂ A B _ _) where
  add_dist := by intros; simp
-/

instance proj₁ {G : Type _} [AddCommGroup G] (ϕ : A × B → G) [Homϕ : AddCommGroup.Homomorphism ϕ] : AddCommGroup.Homomorphism (ϕ ∘ ι₁) where
  add_dist := by
    intro a a'
    simp [ι₁]
    rw [← Homϕ.add_dist]
    simp

instance proj₂ {G : Type _} [AddCommGroup G] (ϕ : A × B → G) [Homϕ : AddCommGroup.Homomorphism ϕ] : AddCommGroup.Homomorphism (ϕ ∘ ι₂) where
  add_dist := by
    intro b b'
    simp [ι₂]
    rw [← Homϕ.add_dist]
    simp

end Homomorphisms
