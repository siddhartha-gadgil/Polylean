import Polylean.MetabelianGroup

/-
Define the product of two groups and related concepts.

Product groups are defined as a special case of the Metabelian construction with trivial action and trivial cocycle.
-/


section Product

variable {Q K : Type _} [AddCommGroup Q] [AddCommGroup K]

def trivial_mul : Q → K → K
  | _ => id

-- the trivial action of `Q` on `K`
instance trivial_action : AddCommGroup.ActionByAutomorphisms Q K :=
  {
    sMul := trivial_mul
    id_action := rfl
    compatibility := rfl
    add_dist := λ b b' => rfl
  }

-- the trivial cocycle
def trivial_cocycle : Q → Q → K
  | _, _ => 0

instance : @Cocycle Q K _ _ trivial_action trivial_cocycle :=
  {
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

theorem directSum_mul {a a' : A} {b b' : B} : MetabelianGroup.mul trivial_cocycle (a, b) (a', b') = (a + a', b + b') := by
    simp [MetabelianGroup.mul, trivial_cocycle]
    rfl

theorem directSum_add (a a' : A) (b b' : B) : directSum.add (a, b) (a', b') = (a + a', b + b') := directSum_mul

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
                have : b • a' = a' := rfl
                rw [this, ϕHom.add_dist, ψHom.add_dist, ← DirectSum.directSum_add]
                rfl

abbrev ι₁ [Zero A] [Zero B] : A → A × B := λ a => (a, 0)

abbrev ι₂ [Zero A] [Zero B] : B → A × B := λ b => (0, b)

instance proj₁ {G : Type _} [AddCommGroup G] (ϕ : A × B → G) [Homϕ : AddCommGroup.Homomorphism ϕ] : AddCommGroup.Homomorphism (ϕ ∘ ι₁) where
  add_dist := by
    intro a a'
    simp [ι₁]
    rw [← Homϕ.add_dist]
    have : (a, (0 : B)) + (a', (0 : B)) = (a + a', (0 + 0 : B)) := DirectSum.directSum_add a a' 0 0
    rw [this, add_zero]

instance proj₂ {G : Type _} [AddCommGroup G] (ϕ : A × B → G) [Homϕ : AddCommGroup.Homomorphism ϕ] : AddCommGroup.Homomorphism (ϕ ∘ ι₂) where
  add_dist := by
    intro b b'
    simp [ι₂]
    rw [← Homϕ.add_dist]
    have : ((0 : A), b) + ((0 : A), b') = ((0 + 0 : A), b + b') := DirectSum.directSum_add 0 0 b b'
    rw [this, add_zero]

end Homomorphisms
