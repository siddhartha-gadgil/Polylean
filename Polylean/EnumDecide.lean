import Mathlib.Data.Fintype.Basic

/-!
Automatically decide statements of the form `∀ x : X, P x` on a finite type `X` by enumeration.
-/

set_option autoImplicit false

namespace EnumDecide

/-- A typeclass for "exhaustively verifiable types", i.e., 
  types for which it is possible to decide whether a given (decidable) predicate holds for all its elements. -/
class DecideForall (α : Type) where
  decideForall (p : α → Prop) [DecidablePred p] : 
    Decidable (∀ x : α, p x)

instance {α : Sort _} {p : α → Prop} [DecidablePred p] [dfa : DecideForall α] : Decidable (∀ x : α, p x) := dfa.decideForall p


variable {α : Sort _} (p : α → Prop) [DecidablePred p]

/-- It is possible to check whether a decidable predicate holds for all elements of a list. -/
@[instance] def decideList : (l : List α) → Decidable (∀ a ∈ l, p a)
  | [] => .isTrue <| by intros; contradiction
  | a :: as =>
    if h : p a then
      match decideList as with
      | .isTrue _ => .isTrue <| by simp [h]; assumption
      | .isFalse ih => .isFalse <| by simp [h, ih]
    else .isFalse <| by simp [h]

/-- It is possible to check whether a decidable predicate holds for all elements of a multiset. -/
@[instance] def decideMultiset (s : Multiset α) : Decidable (∀ a ∈ s, p a) := 
  s.rec (decideList _) <| by intros; simp

def decideFintype [Fintype α] : Decidable (∀ a : α, p a) := by
  have : (∀ a : α, p a) ↔ (∀ a ∈ Finset.univ.val, p a) := by
    have : ∀ a : α, (p a ↔ (a ∈ Finset.univ → p a)) := by intros; simp
    conv =>
      lhs
      ext
      rw [this]
  rw [this]; exact inferInstance

instance [Fintype α] : DecideForall α := ⟨fun p ↦ decideFintype p⟩

instance {k : ℕ} : DecideForall (Fin k) := inferInstance

section Examples

example : ∀ x : Fin 3, x + 0 = x := by decide

example : ∀ x y : Fin 3, x + y = y + x := by decide

theorem Zmod3.assoc :
  ∀ x y z : Fin 3, (x + y) + z = x + (y + z) := by decide
end Examples

section CompositeEnumeration

@[instance]
def decideProd {α β : Type}[dfa : DecideForall α][dfb : DecideForall β] (p:α × β → Prop)[DecidablePred p] : Decidable (∀ xy :α × β, p xy) := 
    if c: (∀ x: α, ∀ y : β, p (x, y)) 
    then
      by
      apply Decidable.isTrue
      intro (x, y)
      exact c x y
    else    
      by
      apply Decidable.isFalse
      intro contra
      apply c 
      intro x y
      exact contra (x, y)

instance {α β : Type}[dfa : DecideForall α][dfb : DecideForall β] :
  DecideForall (α × β) := 
  ⟨by apply decideProd⟩

@[instance]
def decideUnit (p: Unit → Prop)[DecidablePred p] : Decidable (∀ x : Unit, p x) := 
   if c : p (()) then by 
      apply Decidable.isTrue
      intro x
      have l : x = () := by rfl
      rw [l]
      exact c
    else by 
      apply Decidable.isFalse
      intro contra
      apply c
      exact contra ()

instance : DecideForall Unit := 
  ⟨by apply decideUnit⟩

@[instance]
def decideSum {α β : Type}[dfa : DecideForall α][dfb : DecideForall β](p:α ⊕ β → Prop)[DecidablePred p] : Decidable (∀ x :α ⊕ β, p x) := 
    if c: ∀x: α, p (Sum.inl x) then 
       if c': ∀y: β , p (Sum.inr y) then 
       by
        apply Decidable.isTrue
        intro x
        cases x with 
        | inl a => exact c a
        | inr a => exact c' a
      else by
        apply Decidable.isFalse
        intro contra
        apply c'
        intro x
        exact contra (Sum.inr x) 
    else by
      apply Decidable.isFalse
      intro contra
      apply c
      intro x
      exact contra (Sum.inl x) 
      
instance {α β : Type}[dfa : DecideForall α][dfb : DecideForall β] :
  DecideForall (α ⊕ β) := 
  ⟨by apply decideSum⟩

instance funEnum {α β : Type}[dfa : DecideForall α][dfb : DecidableEq β] : DecidableEq (α → β) := fun f g => 
      if c:∀ x:α, f x = g x then
        by
        apply Decidable.isTrue
        apply funext
        intro x  
        exact c x
      else 
        by
        apply Decidable.isFalse
        intro contra
        apply c
        intro x
        exact congrFun  contra x
        

example : ∀ xy : (Fin 3) × (Fin 2), 
      xy.1.val + xy.2.val  = xy.2.val + xy.1.val := by decide
end CompositeEnumeration