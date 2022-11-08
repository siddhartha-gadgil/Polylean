import Polylean.Groupoids.Groupoid

-- TODO: Eventually switch to groupoid actions
abbrev Group := Groupoid Unit

theorem Subtype.eq_prop {P P' : X → Prop} (h : ∀ x, P x ↔ P' x) : Subtype P = Subtype P' :=
  have h' : ∀ x, P x = P' x := λ x => propext $ h x
  have h'' : P = P' := funext h'
  congrArg _ h''

class Groupoid.Action [G : Group] (S : Sort _) [Γ : Groupoid S] where
  action : (G.hom () ()) → (Γ ⥤ Γ)
  free : {g h : G.hom () ()} → action g = action h → g = h
  compatibility : {g h : G.hom () ()} → action (g ≫ h) = (action g) ⋙ (action h)

namespace Groupoid.Action

variable (S : Sort _) [G : Group] [Γ : Groupoid S] [α : Groupoid.Action S]

@[simp] theorem action_id : action 𝟙 = (Functor.id S) := sorry


inductive Orbit.rel : S → S → Prop
  | action (A : S) (g : G.hom () ()) : Orbit.rel A ((α.action g).obj A)

def QuotientSpace := Quot $ Orbit.rel S


abbrev HomCollection (X Y : QuotientSpace S) := 
  Σ (A : {Z // X = Quot.mk _ Z}), 
  Σ (B : {Z // Y = Quot.mk _ Z}),
    A.val ⟶ B.val
      
/-- The translation of a morphism by an action. -/
inductive HomCollection.rel : (X Y : QuotientSpace S) → HomCollection _ X Y → HomCollection _ X Y → Prop
  | action {A B : S} (f : A ⟶ B) (g : G.hom () ()) : 
      HomCollection.rel (Quot.mk _ A) (Quot.mk _ B) 
        ⟨⟨A, rfl⟩, ⟨B, rfl⟩, f⟩

        ⟨⟨(α.action g).obj A, Quot.sound (Orbit.rel.action _ _)⟩, 
         ⟨(α.action g).obj B, Quot.sound (Orbit.rel.action _ _)⟩, 
         (α.action g).map f⟩

def HomCollection.id (A : S) : HomCollection _ (Quot.mk _ A) (Quot.mk _ A) :=
  ⟨⟨A, rfl⟩, ⟨A, rfl⟩, 𝟙⟩

def HomCollection.comp {X Y Z : QuotientSpace S} : HomCollection _ X Y → HomCollection _ Y Z → HomCollection _ X Z
  | ⟨A, B, f⟩, ⟨B', C, g⟩ => ⟨A, C, f ≫ g⟩

def HomCollection.inv {X Y : QuotientSpace S} : HomCollection _ X Y → HomCollection _ Y X
  | ⟨A, B, f⟩ => ⟨B, A, f⁻¹⟩

def HomSpace (X Y : QuotientSpace S) := Quot $ HomCollection.rel _ X Y

def HomSpace.id : (X : QuotientSpace S) → HomSpace _ X X := 
  Quot.rec (λ a => Quot.mk _ (HomCollection.id S a))
  (by
    intro a b
    simp [HomCollection.id]
    intro p
    cases p
    sorry
    )

def HomSpace.comp {X Y Z : QuotientSpace S} : HomSpace _ X Y → HomSpace _ Y Z → HomSpace _ X Z := sorry

def HomSpace.inv {X Y : QuotientSpace S} : HomSpace _ X Y → HomSpace _ Y X :=
  Quot.lift (λ φ => Quot.mk _ φ.inv) 
  (by
    intro ⟨⟨A, quotAX⟩, ⟨B, quotBY⟩, (f : A ⟶ B)⟩
    intro ⟨⟨C, quotCX⟩, ⟨D, quotDY⟩, (g : C ⟶ D)⟩
    intro h
    apply Quot.sound
    rw [HomCollection.inv, HomCollection.inv]
    dsimp
    cases h with
      | action _ a => 
        have := HomCollection.rel.action f⁻¹ a
        simp at this
        exact this)

instance Groupoid.OrbitSpace : Groupoid (QuotientSpace S) where
  hom := HomSpace S
  id := sorry
  comp := sorry
  inv := sorry

  id_comp := sorry
  comp_id := sorry
  comp_assoc := sorry
  inv_comp_id := sorry
  comp_inv_id := sorry

end Groupoid.Action