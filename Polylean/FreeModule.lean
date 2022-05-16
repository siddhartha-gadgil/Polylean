import Mathlib.Algebra.Ring.Basic

/-
Free module over a ring `R` which may be assumed to be commutative, will eventually be $Z/2`$. 

Outline:

* Define formal sums; coordinates of formal sums.
* Define the relation corresponding to equal coordinates and prove that it is an equivalence relation.
* Define the free module as a quotient of the above relation, via setoids.
* Introduce an inductive type giving the elementary relations, i.e., single moves.
* Define an auxiliary quotient by this relation (which is not an equivalence relation); and an auxiliary equivalence relation corresponding to this quotient.
* Show that coefficients are equal if and only if formal sums satisfy the auxiliary relation.
* Deduce that the auxiliary relation is the original relation (may not need to make this explicit).
* Deduce a universal property and construct the sum and product operations : these depend on each other, so one may need a weaker version of the universal property first. Alternatively, the operations may be constructed as special cases of the universal property.
-/

/-!
Defining the free module. The basis set is `X` and the ring is `R`.
-/
variable (R: Type)[Ring R][DecidableEq R]
variable (X: Type)[DecidableEq X]

abbrev FormalSum := List (R × X)

def monomCoeff (x₀ : X) (nx : R × X) : R := 
  match  (nx.2 == x₀) with 
  | true => nx.1
  | false => 0

#check monomCoeff

theorem monom_coeff_hom (x₀ x : X)(a b : R) :
    monomCoeff R X x₀ (a + b, x) = 
      monomCoeff R X x₀ (a, x) + monomCoeff R X x₀ (b, x) := by
    repeat (rw [monomCoeff])
    cases x==x₀ <;> simp 

theorem monom_coeff_at_zero (x₀ x : X) : monomCoeff R X x₀ (0, x) = 0 :=
    by 
      rw [monomCoeff]
      cases x==x₀ <;> rfl

def FormalSum.coords{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]: FormalSum R X → X → R
| [], _ =>  0
| h :: t, x₀ => monomCoeff R X x₀ h + coords t x₀

def FormalSum.support{R: Type}[Ring R][DecidableEq R]{X: Type}[DecidableEq X]
        (s: FormalSum R X) : List X :=
              s.map <| fun (_, x) => x

open FormalSum

#check Ring

theorem nonzero_coord_in_support{R: Type}[Ring R][DecidableEq R]
    {X: Type}[DecidableEq X](s: FormalSum R X) :
        ∀ x: X, 0 ≠  s.coords x  → x ∈ s.support  := 
          match s with 
          | [] => fun x hyp => 
            by
              have d : coords [] x = (0 : R) := by rfl
              rw [d] at hyp
              contradiction
          | h :: t => 
            by
            intro x hyp
            let (a₀, x₀) := h
            have d : support ((a₀, x₀) :: t) =  
              x₀ :: (support t) := by rfl
            rw [d]
            match p:x₀ == x with
            | true => 
                have eqn : x₀ = x := of_decide_eq_true p
                rw [eqn]
                apply List.mem_of_elem_eq_true
                simp [List.elem]
            | false => 
                rw [coords, monomCoeff, p, zero_add] at hyp
                let step := nonzero_coord_in_support t x hyp
                apply List.mem_of_elem_eq_true
                simp [List.elem]
                have p' : (x == x₀) = false := 
                      by
                        have eqn := of_decide_eq_false p 
                        have eqn' : ¬ (x = x₀) := by
                            intro contra
                            let contra' := Eq.symm contra
                            contradiction
                        exact decide_eq_false eqn'                                      
                rw [p']
                apply List.elem_eq_true_of_mem
                exact step

def equalOnSupport{R: Type}[DecidableEq R]{X: Type}[DecidableEq X](l: List X)(f g : X → R) : Prop :=
  match l with
  | [] => true
  | h :: t =>
    (f h = g h) ∧ (equalOnSupport t f g)

theorem equal_on_support_of_equal{R: Type}[DecidableEq R]{X: Type}[DecidableEq X]
  (l: List X)(f g : X → R):
    f = g → equalOnSupport l f g := by
    intro hyp
    induction l with
    | nil =>
      rw [equalOnSupport]  
    | cons h t step => 
      rw [equalOnSupport]
      apply And.intro
      rw [hyp]
      exact step

theorem mem_of_equal_on_support{R: Type}[DecidableEq R]
  {X: Type}[DecidableEq X](l: List X)
    (f g : X → R)(x : X)(mhyp: x ∈ l) : 
      equalOnSupport l f g →  f x = g x :=
    match l with
    | [] => by contradiction
    | h :: t => by 
      intro hyp
      simp [equalOnSupport] at hyp
      cases mhyp 
      exact hyp.left
      have inTail : x ∈ t := by assumption
      have step := mem_of_equal_on_support t f g x inTail hyp.right
      exact step

def decideEqualOnSupport{R: Type}[DecidableEq R]
  {X: Type}[DecidableEq X](l: List X)(f g : X → R) :
      Decidable (equalOnSupport l f g) := 
  match l with
  | [] => 
    Decidable.isTrue (by simp [equalOnSupport])
  | h :: t => by 
    simp [equalOnSupport]
    cases (decideEqualOnSupport t f g) with
    | isTrue hs => 
        exact (
          if c:f h = g h then (Decidable.isTrue ⟨c, hs⟩) 
          else by
            apply Decidable.isFalse
            intro contra
            have contra' := contra.left 
            contradiction
        )        
    | isFalse hs => 
       apply Decidable.isFalse
       intro contra
       have contra' := contra.right
       contradiction

instance {X: Type}[DecidableEq X]{R: Type}[DecidableEq R]
  {l: List X}{f g : X → R} :
    Decidable (equalOnSupport l f g) := decideEqualOnSupport l f g

-- Setoid using coordinate equality
def eqlCoords(s₁ s₂ : FormalSum R X) : Prop :=
        s₁.coords = s₂.coords

namespace eqlCoords

theorem refl{R: Type}[Ring R][DecidableEq R]{X: Type}[DecidableEq X]
  (s: FormalSum R X) :
      eqlCoords R X s s := by
        rfl

theorem symm{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]{s₁ s₂ : FormalSum R X} : 
    eqlCoords R X s₁ s₂ → eqlCoords R X s₂ s₁ := by
    intro hyp
    apply funext
    intro x 
    apply Eq.symm
    exact congrFun hyp x

theorem trans{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]{s₁ s₂ s₃ : FormalSum R X}:
    eqlCoords R X s₁ s₂ → eqlCoords R X s₂ s₃ → eqlCoords R X s₁ s₃ := by
    intro hyp₁ hyp₂
    apply funext
    intro x
    have l₁ := congrFun hyp₁ x
    have l₂ := congrFun hyp₂ x
    exact Eq.trans l₁ l₂

theorem is_equivalence{R: Type}[Ring R][DecidableEq R]
    {X: Type}[DecidableEq X] : 
      Equivalence (eqlCoords R X) := 
      {refl := refl, symm := symm, trans := trans}

end eqlCoords

instance formalSumSetoid:
    Setoid (FormalSum R X) := ⟨eqlCoords R X, eqlCoords.is_equivalence⟩

def FreeModule := Quotient (formalSumSetoid R X)

notation "⟦" a "⟧" => Quotient.mk' a

def decideEqualQuotient{R: Type}[Ring R][DecidableEq R]
    {X: Type}[DecidableEq X](s₁ s₂ : FormalSum R X) : 
  Decidable ( ⟦ s₁ ⟧ = ⟦ s₂ ⟧ )  := 
        if ch₁ : equalOnSupport s₁.support s₁.coords s₂.coords then
          if ch₂ : equalOnSupport s₂.support s₁.coords s₂.coords then
            Decidable.isTrue ( 
              by
              apply Quotient.sound
              apply funext
              intro x
              exact 
                if  h₁:(0 = s₁.coords x) then 
                  if h₂:(0 = s₂.coords x) then
                    by rw [← h₁, h₂]
                  else by
                  have lem : x ∈ s₂.support := by 
                      apply nonzero_coord_in_support
                      assumption                      
                  let lem' :=   
                    mem_of_equal_on_support s₂.support s₁.coords s₂.coords x lem ch₂
                  exact lem'
                else by
                  have lem : x ∈ s₁.support := by 
                      apply nonzero_coord_in_support
                      assumption
                  let lem' :=   
                    mem_of_equal_on_support s₁.support s₁.coords s₂.coords x lem ch₁
                  exact lem'
              )
          else
            Decidable.isFalse (
              by
                intro contra
                let lem :=
                  equal_on_support_of_equal 
                    s₂.support s₁.coords s₂.coords (Quotient.exact contra) 
                contradiction
            )
        else
          Decidable.isFalse (
            by
              intro contra
              let lem :=
                  equal_on_support_of_equal 
                    s₁.support s₁.coords s₂.coords (Quotient.exact contra)
              contradiction
          )

instance {R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]{s₁ s₂ : FormalSum R X} :  
    Decidable ( ⟦ s₁ ⟧ = ⟦ s₂ ⟧ ) := decideEqualQuotient s₁ s₂

def FreeModule.beq?{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]
    (x₁ x₂ : FreeModule R X) : Bool := by
    apply Quotient.lift₂ (fun (s₁ s₂ : FormalSum R X) => 
          decide ( ⟦ s₁ ⟧ = ⟦ s₂ ⟧))
    intro a₁ b₁ a₂ b₂ eqv₁ eqv₂
    let eq₁ : ⟦ a₁ ⟧ = ⟦ a₂ ⟧ := Quot.sound eqv₁
    let eq₂ : ⟦ b₁⟧ = ⟦ b₂ ⟧ := Quot.sound eqv₂
    simp [eq₁, eq₂]
    exact x₁
    exact x₂
    
def FreeModule.eq_of_beq_true
  {R: Type}[Ring R][DecidableEq R]{X: Type}[DecidableEq X]:
    ∀ x₁ x₂ : FreeModule R X,  x₁.beq? x₂ = true → x₁ = x₂ := by
    let f := @Quotient.ind₂ (FormalSum R X) (FormalSum R X)
              (formalSumSetoid R X) (formalSumSetoid R X)
              (fun (x₁ x₂ : FreeModule R X) =>   x₁.beq? x₂ = true → x₁ = x₂)
    apply f
    intro s₁ s₂ eqv
    let eql := of_decide_eq_true eqv
    assumption

def FreeModule.neq_of_beq_false
  {R: Type}[Ring R][DecidableEq R]{X: Type}[DecidableEq X]:
    ∀ x₁ x₂ : FreeModule R X,  x₁.beq? x₂ = false → Not (x₁ = x₂) := by
    let f := @Quotient.ind₂ (FormalSum R X) (FormalSum R X)
              (formalSumSetoid R X) (formalSumSetoid R X)
              (fun (x₁ x₂ : FreeModule R X) =>   x₁.beq? x₂ = false →
                Not (x₁ = x₂))
    apply f
    intro s₁ s₂ neqv
    let neql := of_decide_eq_false neqv
    assumption

def FreeModule.decEq{R: Type}[Ring R][DecidableEq R]
  {X: Type}[DecidableEq X]
    (x₁ x₂ : FreeModule R X) : Decidable (x₁ = x₂) := by
    match p:x₁.beq? x₂ with
    | true => 
      apply Decidable.isTrue
      apply FreeModule.eq_of_beq_true
      assumption
    | false => 
      apply Decidable.isFalse
      apply FreeModule.neq_of_beq_false
      assumption

instance {X: Type}[DecidableEq X]: DecidableEq (FreeModule R X) :=
  fun x₁ x₂ => x₁.decEq x₂

