namespace EnumDecide

def decideBelow (p:Nat → Prop)[DecidablePred p](bound: Nat):
  Decidable (∀ n : Nat, n < bound → p n) := 
    match bound with
    | 0 => by
      apply Decidable.isTrue
      intro n bd 
      contradiction
    | k + 1 => 
      let prev := decideBelow p k
      match prev with
      | Decidable.isTrue hyp => 
        if c:p k then 
          by
          apply Decidable.isTrue
          intro n bd
          cases Nat.eq_or_lt_of_le bd with
          | inl eql => 
            have eql' : n = k := by
                injection eql
                assumption
            simp [eql']
            assumption
          | inr lt => 
            have lt' : n < k := by
                apply Nat.le_of_succ_le_succ
                assumption
            exact hyp n lt'
        else 
          by
          apply Decidable.isFalse
          intro contra
          have lem : p k := by
            apply contra k
            apply Nat.le_refl
          contradiction
      | Decidable.isFalse hyp => by
        apply Decidable.isFalse
        intro contra
        have lem : ∀ (n : Nat), n < k → p n := by
          intro n bd
          have bd' : n < k + 1 := by
            apply Nat.le_step
            exact bd
          exact contra n bd'
        contradiction

def decideBelowFin {m: Nat}(p:Fin m → Prop)[DecidablePred p](bound: Nat):
  Decidable (∀ n : Fin m, n < bound → p n) := 
    match bound with
    | 0 => by
      apply Decidable.isTrue
      intro n bd 
      contradiction
    | k + 1 => 
      let prev := decideBelowFin p k
      match prev with
      | Decidable.isTrue hyp => 
        if ineq : k < m then
          if c:p ⟨k, ineq⟩ then 
            by
            apply Decidable.isTrue
            intro n bd
            cases Nat.eq_or_lt_of_le bd with
            | inl eql => 
              have eql' : n = ⟨k, ineq⟩ := by
                  apply Fin.eq_of_val_eq
                  injection eql
                  assumption
              simp [eql']
              assumption
            | inr lt => 
              have lt' : n < k := by
                  apply Nat.le_of_succ_le_succ
                  assumption
              exact hyp n lt'
          else 
            by
            apply Decidable.isFalse
            intro contra
            have lem : p ⟨k, ineq⟩ := by
              apply contra ⟨k, ineq⟩
              apply Nat.le_refl
            contradiction
        else
          by 
          apply Decidable.isTrue
          intro ⟨n, nbd⟩ bd
          have ineq' : m ≤ k := by
            apply Nat.le_of_succ_le_succ
            apply Nat.gt_of_not_le ineq 
          have ineq'' := Nat.le_trans nbd ineq'
          exact hyp ⟨n, nbd⟩ ineq''
      | Decidable.isFalse hyp => by
        apply Decidable.isFalse
        intro contra
        have lem : ∀ (n : Fin m), n < k → p n := by
          intro n bd
          have bd' : n < k + 1 := by
            apply Nat.le_step
            exact bd
          exact contra n bd'
        contradiction

def decideFin {m: Nat}(p:Fin m → Prop)[DecidablePred p]:
  Decidable (∀ n : Fin m, p n) := 
  match decideBelowFin p m with 
  | Decidable.isTrue hyp => 
    by
    apply Decidable.isTrue
    intro ⟨n, ineq⟩
    exact hyp ⟨n, ineq⟩ ineq
  | Decidable.isFalse hyp => by
    apply Decidable.isFalse
    intro contra
    apply hyp
    intro ⟨n, ineq⟩ bd
    exact contra ⟨n, ineq⟩   

class DecideForall (α : Type) where
  decideForall (p : α → Prop) [DecidablePred p]: 
    Decidable (∀ x : α, p x)  

instance {k: Nat} : DecideForall (Fin k) := 
  ⟨by apply decideFin⟩

instance {α : Type}[dfa: DecideForall α]{p : α → Prop}[DecidablePred p]: 
  Decidable (∀ x : α, p x) := 
  dfa.decideForall p

#check ex_of_PSigma

example : ∀ x : Fin 3, x + 0 = x := by decide

example : ∀ x y : Fin 3, x + y = y + x := by decide

theorem Zmod3.assoc {n: Nat} :
  ∀ x y z : Fin 2, (x + y) + z = x + (y + z) := by decide

def decideProd {α β : Type}[dfa : DecideForall α][dfb : DecideForall β]
  (p:α × β → Prop)[DecidablePred p] :
  Decidable (∀ xy :α × β, p xy) := 
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

def decideUnit (p: Unit → Prop)[DecidablePred p] :
  Decidable (∀ x : Unit, p x) := 
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

def decideSum {α β : Type}[dfa : DecideForall α][dfb : DecideForall β]
  (p:α ⊕ β → Prop)[DecidablePred p] :
  Decidable (∀ x :α ⊕ β, p x) := 
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

example : ∀ xy : (Fin 3) × (Fin 2), 
      xy.1.val + xy.2.val  = xy.2.val + xy.1.val := by decide

/- The group Q (rough code) -/

abbrev Q := (Fin 2) × (Fin 2)

instance : Add Q := 
  ⟨fun (x₁, y₁) (x₂ , y₂) => (x₁ + x₂, y₁ + y₂)⟩

namespace Q 

theorem comm : ∀ a b : Q, a + b = b + a := by decide

theorem assoc : ∀ a b c : Q, a + b + c = a + (b + c) := by decide

def zero : Q := (0, 0)

theorem zero_add : ∀ a : Q, zero + a = a := by decide

theorem add_zero : ∀ a : Q, a + zero = a := by decide

def neg : Q → Q
  | (x, y) => (x, y)

theorem neg_add : ∀ a : Q, (neg a) + a = zero := by decide

theorem add_neg : ∀ a : Q, a + (neg a) = zero := by decide

end Q

