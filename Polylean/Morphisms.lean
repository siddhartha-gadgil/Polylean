import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic

/-
It appears that mathlib4 does not yet have homomorphisms. We need:

* Homomorophisms for Abelian (additive) groups.
* Homomorophisms for rings.

As with all structures, there should be a typeclass for _being a morphism_ and theorems that let us access the defining properties of a morphism.
-/

-- @[to_additive]
class Group.Homomorphism {G H : Type _} [Group G] [Group H] (ϕ : G → H) where
  mul_dist : ∀ g g' : G, ϕ (g * g') = (ϕ g) * (ϕ g')


section Group

theorem Group.mul_left_cancel {G : Type _} [Group G] {a b c : G} : a * b = a * c → b = c := by
  intro h
  have : b = a⁻¹ * (a * b) := by simp
  simp [h] at this
  assumption

instance {G : Type _} [Group G] : IsMulLeftCancel G := ⟨@Group.mul_left_cancel G _⟩

theorem Group.mul_right_cancel {G : Type _} [Group G] {a b c : G} : b * a = c * a → b = c := by
  intro h
  have : b = (b * a) * a⁻¹ := by simp
  simp [h] at this
  assumption

instance {G : Type _} [Group G] : IsMulRightCancel G := ⟨@Group.mul_right_cancel G _⟩

@[simp] theorem one_inv {G : Type _} [Group G] : (1 : G)⁻¹ = 1 := by
  have : (1 : G)⁻¹ * 1 = 1 := mul_left_inv 1
  rw [mul_one] at this
  assumption

end Group


namespace Group.Homomorphism

variable {G H : Type _} [GrpG : Group G] [GrpH : Group H]
variable {ϕ : G → H} [Homϕ : Group.Homomorphism ϕ]


@[simp] theorem mul_distrib {g g' : G} : ϕ (g * g') = ϕ g * ϕ g' := Homomorphism.mul_dist g g'

/- Kernel of a group homomorphism-/
def kernel (ϕ : G → H) [Group.Homomorphism ϕ] := {g : G // ϕ g = 1}

@[simp] theorem one_image : ϕ 1 = 1 := by
  have : (ϕ 1) * (ϕ 1) = (ϕ 1) * 1 := by rw [← Homomorphism.mul_distrib, mul_one, mul_one]
  exact mul_left_cancel this

theorem hom_inv {g : G} : (ϕ g)⁻¹ = ϕ g⁻¹ := by
  have : ϕ g * ϕ g⁻¹ = ϕ g * (ϕ g)⁻¹ := by rw [← Homomorphism.mul_distrib]; simp
  exact GrpH.mul_left_cancel (Eq.symm this)

theorem inv_kernel {g : G} : ϕ g = 1 → ϕ g⁻¹ = 1 := by
  intro h
  have : ϕ g * ϕ g⁻¹ = 1 := by have := (mul_right_inv (ϕ g)); rw [hom_inv] at this; assumption
  rw [h, one_mul] at this
  assumption


instance : Group (kernel ϕ) :=
  {
    mul := λ ⟨g₁, prf₁⟩ ⟨g₂, prf₂⟩ => ⟨g₁ * g₂, by rw [Homϕ.mul_dist g₁ g₂, prf₁, prf₂, mul_one]⟩
    mul_assoc := λ ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => by sorry

    one := ⟨1, one_image⟩
    mul_one := by intro ⟨a, prf⟩; sorry
    one_mul := by intro ⟨a, prf⟩; sorry

    inv := λ ⟨g, prf⟩ => ⟨g⁻¹, inv_kernel prf⟩
    mul_left_inv := by intro ⟨a, prf⟩; simp [Inv.inv]; sorry

    npow_zero' := by intros; rfl
    npow_succ' := by intros; rfl

    div_eq_mul_inv := by intros; rfl
    gpow_zero' := by intros; rfl
    gpow_succ' := by intros; rfl
    gpow_neg' := by intros; rfl
  }

end Group.Homomorphism

section

variable {G : Type _} [Grp : Group G]

instance (P : G → Prop)
  (mul_closure : ∀ {a b : G}, P a → P b → P (a * b))
  (inv_closure : ∀ {a : G}, P a → P a⁻¹)
  (id_closure : P 1) :
  Group {g : G // P g} :=
   {
    mul := λ ⟨g₁, prf₁⟩ ⟨g₂, prf₂⟩ => ⟨g₁ * g₂, mul_closure prf₁ prf₂⟩
    mul_assoc := λ ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => sorry

    one := ⟨1, id_closure⟩
    mul_one := by intro α; cases α; sorry
    one_mul := by intro ⟨a, prf⟩; sorry

    inv := λ ⟨g, prf⟩ => ⟨g⁻¹, inv_closure prf⟩
    mul_left_inv := by intro ⟨a, prf⟩; simp [Inv.inv]; sorry

    npow_zero' := by intros; rfl
    npow_succ' := by intros; rfl

    div_eq_mul_inv := by intros; rfl
    gpow_zero' := by intros; rfl
    gpow_succ' := by intros; rfl
    gpow_neg' := by intros; rfl
  }

end

section Morphisms

class AddCommGroup.Homomorphism {A B : Type _} [AddCommGroup A] [AddCommGroup B] (ϕ : A → B) where
  add_dist : ∀ a a' : A, ϕ (a + a') = ϕ a + ϕ a'

class Monoid.Homomorphism {M N : Type _} [Monoid M] [Monoid N] (ϕ : M → N) where
  mul_dist : ∀ m m' : M, ϕ (m * m') = ϕ m * ϕ m'
  one_map : ϕ 1 = 1

class CommRing.Homomorphism {R S : Type _} [CommRing R] [CommRing S] (ϕ : R → S)
  extends AddCommGroup.Homomorphism ϕ, Monoid.Homomorphism ϕ

end Morphisms
