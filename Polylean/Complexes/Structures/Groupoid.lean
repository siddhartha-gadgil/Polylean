import Polylean.Complexes.Structures.Quiver

/-- A `GroupoidStruct` is a barebones structure for a groupoid containing none of the axioms. -/
class GroupoidStruct (S : Sort _) extends Quiver S where
  id : {X : S} → (X ⟶ X)
  comp : {X Y Z : S} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)
  inv : {X Y : S} → (X ⟶ Y) → (Y ⟶ X)

notation "𝟙" => GroupoidStruct.id -- type as `\b1`
infixr:80 " ≫ " => GroupoidStruct.comp -- type as `\gg`
infixl:80 " ⊚ " => λ f g => GroupoidStruct.comp g f -- type as `\oo`
postfix:max " ⁻¹ " => GroupoidStruct.inv -- type as `\inv`

/-- A `Groupoid` is defined as a `GroupoidStruct` together with consistency conditions imposed. -/
class Groupoid (S : Sort _) extends GroupoidStruct S where
  id_comp : {X Y : S} → (g : X ⟶ Y) → 𝟙 ≫ g = g
  comp_id : {X Y : S} → (g : X ⟶ Y) → g ≫ 𝟙 = g
  comp_assoc : {W X Y Z : S} → {f : W ⟶ X} → {g : X ⟶ Y} → {h : Y ⟶ Z} → (f ≫ g) ≫ h = f ≫ (g ≫ h)
  inv_comp_id : {X Y : S} → (g : X ⟶ Y) → g⁻¹ ≫ g = 𝟙
  comp_inv_id : {X Y : S} → (g : X ⟶ Y) → g ≫ g⁻¹ = 𝟙

namespace Groupoid

attribute [simp] id_comp
attribute [simp] comp_id
attribute [simp] comp_assoc
attribute [simp] inv_comp_id
attribute [simp] comp_inv_id

variable {S : Sort _} [G : Groupoid S] {X Y Z : S} (g g' : X ⟶ Y) (h h' : Y ⟶ Z)

abbrev id' (X : S) : X ⟶ X := 𝟙

@[simp] theorem left_inv_cancel : g⁻¹ ≫ (g ≫ h) = h := by
  rw [← comp_assoc]; simp

@[simp] theorem id_inv : (G.id' X)⁻¹ = (G.id' X) := by
  have := left_inv_cancel (G.id' X) (G.id' X)
  rw [comp_id, comp_id] at this; assumption

@[simp] theorem inv_inv : (g⁻¹)⁻¹ = g := by
  have := left_inv_cancel (g⁻¹) g
  rw [inv_comp_id, comp_id] at this; assumption

@[simp] theorem left_cancel_inv (h : X ⟶ Z) : g ≫ (g⁻¹ ≫ h) = h := by
  have := left_inv_cancel g⁻¹ h
  rw [inv_inv] at this; assumption

@[simp] theorem inv_comp : (g ≫ h)⁻¹ = h⁻¹ ≫ g⁻¹ := by
  have := left_cancel_inv (g ≫ h)⁻¹ (h⁻¹ ≫ g⁻¹)
  simp at this; assumption

@[simp] theorem left_cancel : g ≫ h = g ≫ h' ↔ h = h' :=
  ⟨by
    intro hyp
    have := congrArg (g⁻¹ ≫ ·) hyp
    simp at this
    assumption
  , 
    congrArg _⟩

@[simp] theorem right_cancel : g ≫ h = g' ≫ h ↔ g = g' :=
  ⟨by
    intro hyp
    have := congrArg (· ≫ h⁻¹) hyp
    simp at this
    assumption
  , 
    congrArg (· ≫ h)⟩

@[simp] theorem left_cancel_id : (g = g ≫ e) ↔ 𝟙 = e := by
  have := left_cancel g 𝟙 e
  simp at this; assumption

@[simp] theorem left_cancel_id' : (g ≫ e = g) ↔ e = 𝟙 := by
  have := left_cancel g e 𝟙
  simp at this; assumption
  
@[simp] theorem right_cancel_id : (g = e ≫ g) ↔ 𝟙 = e := by
  have := right_cancel 𝟙 e g
  simp at this; assumption 

@[simp] theorem right_cancel_id' : (e ≫ g = g) ↔ e = 𝟙 := by
  have := right_cancel e 𝟙 g
  simp at this; assumption

end Groupoid


/-- A `Functor` is a morphism of `Groupoid`s. -/
structure Groupoid.Functor {S S' : Sort _} (G : Groupoid S) (G' : Groupoid S') 
    extends Quiver.PreFunctor G.toQuiver G'.toQuiver where
  map_comp : {X Y Z : S} → (g : X ⟶ Y) → (h : Y ⟶ Z) → map (g ≫ h) = map g ≫ map h

namespace Groupoid.Functor

attribute [simp] map_comp

infixr:26 " ⥤ " => Groupoid.Functor -- type as `\func`

/-- The identity morphism of groupoids. -/
@[simp] protected def id (S : Sort _) [G : Groupoid S] : G ⥤ G := 
  {obj := id, map := id, map_comp := λ _ _ => rfl}

instance (S : Sort _) [G : Groupoid S] : Inhabited (G ⥤ G) := ⟨Groupoid.Functor.id S⟩

/-- Composition of morphisms of groupoids. -/
@[simp] def comp {S T U : Sort _} {𝔊 : Groupoid S} {ℌ : Groupoid T} {ℑ : Groupoid U} 
  (F : 𝔊 ⥤ ℌ) (G : ℌ ⥤ ℑ) : 𝔊 ⥤ ℑ :=
  {obj := G.obj ∘ F.obj, map := G.map ∘ F.map, map_comp := by simp}

infixr:80 " ⋙ " => comp

variable {R S T : Sort _} [F : Groupoid R] [G : Groupoid S] [H : Groupoid T] 
variable (Ψ : F ⥤ G) (Φ : G ⥤ H)

@[simp] theorem map_id {X : S} : Φ.map (G.id' X) = H.id' (Φ.obj X) := by
  have := Φ.map_comp (G.id' X) (G.id' X)
  simp at this
  apply Eq.symm
  assumption

@[simp] theorem map_inv {X Y : S} (g : X ⟶ Y) : Φ.map g⁻¹ = (Φ.map g)⁻¹ := by
  apply (Groupoid.left_cancel (Φ.map g) _ _).mp
  rw [← map_comp]
  simp

@[simp] theorem comp_obj : (Φ.obj ∘ Ψ.obj) = (Ψ ⋙ Φ).obj := rfl

@[simp] theorem comp_obj' : ∀ x, (Φ.obj (Ψ.obj x)) = (Ψ ⋙ Φ).obj x := λ _ => rfl

-- @[simp] theorem comp_map : (Φ.map ∘ Ψ.map) = (Ψ ⋙ Φ).map := sorry

end Groupoid.Functor