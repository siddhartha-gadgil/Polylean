import Polylean.Complexes.TwoComplex
import Mathlib.Algebra.Group.Defs

/-- The fundamental groupoid of a two-complex. -/
instance FundamentalGroupoid {V : Type _} (CV : TwoComplex V) : Groupoid V where
  hom := λ u v => Quotient $ Path.Homotopy.setoid u v
  id := λ v => .mk' .nil
  comp := .lift₂ (λ p q => .mk' $ .append p q) $ λ _ _ _ _ h h' => 
            Quotient.sound $ Path.Homotopy.mul_sound h h'
  inv := .lift (λ p => .mk' p.inverse) λ _ _ h => 
            Quotient.sound $ Path.Homotopy.inv_sound h
  invInv := by
    intro _ _
    apply Quotient.ind
    intro e
    apply Quotient.sound
    simp
    apply Path.Homotopy.refl

  idComp := by
    intro _ _
    apply Quotient.ind
    intro
    apply Quotient.sound
    rw [Path.nil_append]
    apply Path.Homotopy.refl

  compId := by
    intro _ _
    apply Quotient.ind
    intro
    apply Quotient.sound
    rw [Path.append_nil]
    apply Path.Homotopy.refl

  compAssoc := by
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

  invComp := by
    intro _ _
    apply Quotient.ind
    intro
    apply Quotient.sound
    apply Path.Homotopy.inv_cancel_left

  compInv := by
    intro _ _
    apply Quotient.ind
    intro
    apply Quotient.sound
    apply Path.Homotopy.inv_cancel_right

/-- The group of endomorphisms at an object of a groupoid. -/
def Groupoid.groupAt {G : Type _} (Gpd : Groupoid G) (g : G) : Group (g ⟶ g) where
  mul := Gpd.comp
  one := Gpd.id g
  inv := Gpd.inv

  mul_assoc := Gpd.compAssoc
  mul_one := Gpd.compId
  one_mul := Gpd.idComp
  mul_left_inv := Gpd.invComp

  npow_zero' := by intros; rfl
  npow_succ' := by intros; rfl

  div_eq_mul_inv := by intros; rfl

  gpow_zero' := by intros; rfl
  gpow_neg' := by intros; rfl
  gpow_succ' := by intros; rfl

/-- The fundamental group of a two-complex. -/
@[instance] def FundamentalGroup {V : Type _} (CV : TwoComplex.{_, _ + 1} V) (v : V) := 
  @Groupoid.groupAt V (FundamentalGroupoid CV) v

/-- A group as a single-object groupoid. -/
instance Group.toGroupoid {G : Type } (_ : Group G) : Groupoid Unit where
  hom := fun | _, _ => G
  id := fun | _ => (1 : G)
  comp := λ g h => g * h
  inv := λ g => g⁻¹
  invInv := by simp

  idComp := one_mul
  compId := mul_one
  compAssoc := mul_assoc
  invComp := mul_left_inv
  compInv := mul_right_inv

#check @Path.compose

-- does not work
instance Groupoid.toTwoComplex {G : Type _} (Grpd : Groupoid G) : AbstractTwoComplex G where
  G := Grpd.toInvertegory.toSerreGraph
  H := Grpd
  collapse := @Path.compose G Grpd.toInvertegory.toCategory
  collapseId := sorry