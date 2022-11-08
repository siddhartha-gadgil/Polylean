import Polylean.MetabelianGroup
import Polylean.Tactics.ReduceGoal

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
  repeat (rw [MetabelianGroup.mul])
  show  (k + k' + 0, q + q') = (k' + k + 0, q' + q)
  rw [add_zero, add_zero, AddCommGroup.add_comm k k', AddCommGroup.add_comm q q']

theorem prod_eq {α β : Type _} (a c : α) (b d : β) : (a, b) = (c, d) ↔ (a = c) ∧ (b = d) := by
  apply Iff.intro
  · intro (h : Prod.mk a b = Prod.mk c d)
    injection h
    apply And.intro <;> assumption
  · intro ⟨hac, hbd⟩
    subst hac hbd
    rfl

theorem product_coords : ∀ g h : K × Q,
     MetabelianGroup.mul trivial_cocycle g h = (g.1 + h.1, g.2 + h.2) := by
        intro (k, q) (k', q')
        reduceGoal
        let tc : @trivial_cocycle Q K _ q q' = 0 := by rfl
        show (k + q • k' + trivial_cocycle q q', q + q') = (k + k', q + q')
        rw [tc, add_zero]
        simp only [SMul.sMul] 
        have tc' : trivial_action q k'= k' := by rfl
        rw [tc']
        
end Product

namespace DirectSum

variable {A B : Type _} [AddCommGroup A] [AddCommGroup B]

-- Direct sums as an additive version of products
-- @[irreducible]
instance directSum : AddCommGroup (A × B) :=
  Group.to_additive product_comm

theorem mul {a a' : A} {b b' : B} : MetabelianGroup.mul trivial_cocycle (a, b) (a', b') = (a + a', b + b') := by
    show (a + a' + 0, b + b') = _
    rw [add_zero]

@[reducible, simp] theorem add (a a' : A) (b b' : B) : (a, b) + (a', b') = (a + a', b + b') := by simp only [HAdd.hAdd, Add.add]; exact mul

theorem zero_pair : (0 : A × B) = ((0 : A), (0 : B)) := rfl
/-
  have pair_left_id : ∀ x : A × B, (0, 0) + x = x := by
    intro (a, b); rw [add, zero_add, zero_add]
  have id_add : (0, 0) + (0 : A × B) = (0, 0) := by rw [add_zero]
  rw [pair_left_id] at id_add
  assumption
-/

end DirectSum


section Homomorphisms

variable {A B C D : Type _} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]

-- products of homomorphisms
-- this is used in defining the group action required for constructing the Metabelian group `P`
@[reducible] def prod (f : A → C) (g : B → D) : A × B → C × D
  | (a, b) => (f a, g b)

infixr:100 " × " => prod

-- showing that the product of homomorphisms is a homomorphism
instance (ϕ : A → C) [ϕHom : AddCommGroup.Homomorphism ϕ] (ψ : B → D) [ψHom : AddCommGroup.Homomorphism ψ] :
  AddCommGroup.Homomorphism (ϕ × ψ) where
    add_dist := by
                intro (a, b) (a', b')
                rw [prod, DirectSum.add]
                show (ϕ (a + a'), ψ (b + b')) = (ϕ a, ψ b) + (ϕ a', ψ b')
                rw [DirectSum.add]
                rw [ϕHom.add_dist, ψHom.add_dist]

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
    show ϕ (a + a', 0) = ϕ (a, 0) + ϕ (a', 0)
    rw [← Homϕ.add_dist, DirectSum.add, add_zero]

instance proj₂ {G : Type _} [AddCommGroup G] (ϕ : A × B → G) [Homϕ : AddCommGroup.Homomorphism ϕ] : AddCommGroup.Homomorphism (ϕ ∘ ι₂) where
  add_dist := by
    intro b b'
    show ϕ (0, b + b') = ϕ (0, b) + ϕ (0, b')
    rw [← Homϕ.add_dist, DirectSum.add, add_zero]

end Homomorphisms
