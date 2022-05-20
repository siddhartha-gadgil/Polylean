import Polylean.MetabelianGroup

/-
Define the product of two groups and related concepts.
-/


section Product

variable {Q K : Type _} [AddCommGroup Q] [AddCommGroup K]

def trivial_mul : Q → K → K
  | _ => id

instance trivial_action : AddCommGroup.ActionByAutomorphisms Q K :=
  {
    sMul := trivial_mul
    id_action := rfl
    compatibility := rfl
    add_dist := λ b b' => rfl
  }

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

instance to_additive {G : Type _} [Grp : Group G] (mul_comm : ∀ g h : G, g * h = h * g) : AddCommGroup G :=
  {
    add := Grp.mul
    add_assoc := Grp.mul_assoc
    zero := Grp.one
    add_zero := Grp.mul_one
    zero_add := Grp.one_mul

    neg := Grp.inv
    add_left_neg := Grp.mul_left_inv
    add_comm := mul_comm

    nsmul_succ' := by intros; rfl
    nsmul_zero' := by intros; rfl

    sub_eq_add_neg := by intros; rfl

    gsmul_zero' := by intros; rfl
    gsmul_succ' := by intros; rfl
    gsmul_neg' := by intros; rfl
  }

instance directSum {A B : Type _} [AddCommGroup A] [AddCommGroup B] : AddCommGroup (A × B) :=
  to_additive product_comm

end DirectSum

section Homomorphisms

variable {A B : Type _} [AddCommGroup A] [AddCommGroup B]

instance (ϕ : A → A) [AddCommGroup.Homomorphism ϕ] (ψ : B → B) [AddCommGroup.Homomorphism ψ] :
  AddCommGroup.Homomorphism (λ (a, b) => (ϕ a, ψ b)) := sorry

end Homomorphisms
