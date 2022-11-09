import Polylean.Complexes.Structures.CombinatorialTwoComplex
import Polylean.Complexes.Structures.Groupoid
import Mathlib.Algebra.Group.Defs

/-- The fundamental groupoid of a two-complex. -/
instance FundamentalGroupoid {V : Sort _} (CV : CombinatorialTwoComplex V) : Groupoid V where
  hom := λ u v => Quotient $ Path.Homotopy.setoid u v
  id := λ v => .mk' .nil
  comp := .lift₂ (λ p q => .mk' $ .append p q) $ λ _ _ _ _ h h' => 
            Quotient.sound $ Path.Homotopy.mul_sound h h'
  inv := .lift (λ p => .mk' p.inverse) λ _ _ h => 
            Quotient.sound $ Path.Homotopy.inv_sound h

  id_comp := by
    intro _ _
    apply Quotient.ind
    intro
    apply Quotient.sound
    rw [Path.nil_append]
    apply Path.Homotopy.refl

  comp_id := by
    intro _ _
    apply Quotient.ind
    intro
    apply Quotient.sound
    rw [Path.append_nil]
    apply Path.Homotopy.refl

  comp_assoc := by
    intro _ _ _ _ f g h
    revert f
    apply Quotient.ind
    intro p
    revert g
    apply Quotient.ind
    intro q
    revert h
    apply Quotient.ind
    intro r
    apply Quotient.sound
    rw [Path.append_assoc]
    apply Path.Homotopy.refl        

  inv_comp_id := by
    intro _ _
    apply Quotient.ind
    intro
    apply Quotient.sound
    apply Path.Homotopy.inv_cancel_left

  comp_inv_id := by
    intro _ _
    apply Quotient.ind
    intro
    apply Quotient.sound
    apply Path.Homotopy.inv_cancel_right

/-- The group of endomorphisms at an object of a groupoid. -/
def Groupoid.groupAt {G : Sort _} (Gpd : Groupoid G) (g : G) : Group (g ⟶ g) where
  mul := Gpd.comp
  one := Gpd.id g
  inv := Gpd.inv

  mul_assoc := Gpd.comp_assoc
  mul_one := Gpd.comp_id
  one_mul := Gpd.id_comp
  mul_left_inv := Gpd.inv_comp_id

  npow_zero' := by intros; rfl
  npow_succ' := by intros; rfl

  div_eq_mul_inv := by intros; rfl

/-- The fundamental group of a two-complex. -/
@[instance] def FundamentalGroup {V : Sort _} (CV : CombinatorialTwoComplex.{_ + 1, _ + 1} V) (v : V) := 
  @Groupoid.groupAt V (FundamentalGroupoid CV) v

/-- A group as a single-object groupoid. -/
instance Group.toGroupoid {G : Type } (_ : Group G) : Groupoid Unit where
  hom := fun | _, _ => G
  id := fun | _ => (1 : G)
  comp := λ g h => g * h
  inv := λ g => g⁻¹

  id_comp := one_mul
  comp_id := mul_one
  comp_assoc := mul_assoc
  inv_comp_id := mul_left_inv
  comp_inv_id := mul_right_inv