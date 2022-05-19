import Polylean.FreeModule

/-
Group ring given a group. The ring structures is constructed using the universal property of R-modules, with uniqueness used to show that it is a ring. This is only an additional structure, i.e., no need to wrap. 
-/

variable {R : Type} [Ring R] [DecidableEq R]

variable {G: Type} [Group G] [DecidableEq G]


def FormalSum.mulTerm (b: R)(h: G) : FormalSum R G → FormalSum R G 
| [] => []
| (a, g) :: tail => (a * b, g * h) :: (mulTerm b h tail)

def FormalSum.mul(fst: FormalSum R G) : FormalSum R G → FormalSum R G
| [] =>    []
| (b, h) :: ys =>  
  (FormalSum.mulTerm  b h fst) ++ (mul fst ys)

open FormalSum

theorem mulTerm_zero (g x₀: G)(s: FormalSum R G):
  coords (mulTerm 0 g s) x₀ = 0 := by
  induction s with
  | nil =>  
    simp [mulTerm, coords]
  | cons h t ih => 
    simp [mulTerm, coords, monom_coords_at_zero]
    assumption

theorem mulTerm_add(b₁ b₂ : R)(h : G)(s: FormalSum R G):
  coords (mulTerm (b₁ + b₂) h s) x₀ = coords (mulTerm b₁ h s) x₀ + coords (mulTerm b₂ h s) x₀ := by
  induction s with
  | nil => 
  simp [mulTerm, coords]
  | cons head tail ih => 
    let (a, g) := head
    simp [mulTerm, coords]
    rw [left_distrib]
    rw [monom_coords_hom]
    rw [ih]
    conv =>
      lhs
      rw [add_assoc]
      congr
      skip
      rw [← add_assoc]
      congr
      rw [add_comm]    
    conv =>
      rhs
      rw [add_assoc]
    conv =>
      rhs 
      congr
      skip 
      rw [← add_assoc]

theorem mul_zero_cons (s t : FormalSum R G)(g: G): 
    mul s ((0, h) :: t) ≈  mul s t := by
    induction s
    case nil =>
      simp [mul, mulTerm]
      apply eqlCoords.refl
    case cons head tail ih =>
      simp [mul, mulTerm]
      apply funext ; intro x₀
      simp [coords]
      rw [monom_coords_at_zero]
      rw [zero_add]
      rw [← append_coords]
      simp [coords, mul]
      let l := mulTerm_zero h x₀ tail
      rw [l]
      simp [zero_add]

  
def mulAux : FormalSum R G → FreeModule R G → FreeModule R G := by
  intro s
  let f  := fun t => ⟦ FormalSum.mul s t ⟧ 
  apply  Quotient.lift f
  apply func_eql_of_move_equiv
  intro t t' rel
  simp 
  induction rel with
  | zeroCoeff tail g a hyp =>
    rw [hyp]
    apply Quotient.sound
    simp [mul]
    apply funext
    intro x₀
    rw [← append_coords]
    let l := mulTerm_zero g x₀ s
    rw [l]
    simp [zero_add]
  | addCoeffs a b x tail =>
    apply Quotient.sound
    apply funext; intro x₀
    simp [mul]
    repeat (rw [← append_coords])
    simp
    simp [mulTerm_add, add_assoc]    
  | cons a x s₁ s₂ r step =>
    apply Quotient.sound
    apply funext ; intro x₀
    simp [mul]
    rw [← append_coords]
    rw [← append_coords]
    simp 
    let l := Quotient.exact step
    let l := congrFun l x₀
    rw [l]
  | swap a₁ a₂ x₁ x₂ tail =>
    apply Quotient.sound
    apply funext ; intro x₀
    simp [mul, ← append_coords]
    rw [← add_assoc]
    rw [← add_assoc]
    simp
    let lc := 
      add_comm 
        (coords (mulTerm a₁ x₁ s) x₀)
        (coords (mulTerm a₂ x₂ s) x₀)
    rw [lc] 

open ElementaryMove
theorem mulTerm_invariant (b : R)(h x₀ : G)(s₁ s₂ : FormalSum R G)
    (rel : ElementaryMove R G s₁ s₂) : 
      coords (mulTerm b h s₁) x₀ = 
      coords (mulTerm b h s₂) x₀ := by
      induction rel with
      | zeroCoeff tail g a hyp => 
        rw [hyp]
        simp [mulTerm, coords,monom_coords_at_zero]
      | addCoeffs a₁ a₂ x tail => 
        simp [mulTerm, coords, right_distrib, monom_coords_hom, add_assoc]
        
      | cons a x t₁ t₂ r step => 
        simp [mulTerm, coords, step]
      | swap a₁ a₂ x₁ x₂ tail => 
        simp [mulTerm, coords]
        conv =>
          lhs
          rw [← add_assoc]
          arg 1
          rw [add_comm]
        rw [← add_assoc]      


theorem first_arg_invariant (s₁ s₂ t : FormalSum R G) 
  (rel : ElementaryMove R G s₁ s₂) :
    FormalSum.mul s₁ t ≈  FormalSum.mul s₂ t := by 
    cases t
    case nil => 
      simp [mul]
      rfl
    case cons head' tail' =>
      let (b, h) := head'
      induction rel with
      | zeroCoeff tail g a hyp => 
        rw [hyp]
        simp [mul, mulTerm]
        apply funext; intro x₀
        rw [← append_coords]
        simp
        simp [coords, monom_coords_at_zero]
        rw [← append_coords]
        simp  
        let rel' : ElementaryMove R G ((0, g) :: tail)  tail := by 
          apply ElementaryMove.zeroCoeff
          rfl
        let prev  := first_arg_invariant  _ _ tail' rel' 
        let pl := congrFun prev x₀
        rw [pl]  
      | addCoeffs a₁ a₂ x tail => 
        simp [mul]
        apply funext; intro x₀
        rw [← append_coords]
        rw [← append_coords]
        simp [coords]
        rw [right_distrib]
        simp [monom_coords_hom]
        let rel' : ElementaryMove R G 
          ((a₁, x) :: (a₂, x) :: tail)
            ((a₁ + a₂, x) :: tail) := by 
            apply ElementaryMove.addCoeffs
        let prev  := first_arg_invariant  _ _ tail' rel' 
        let pl := congrFun prev x₀
        rw [pl]
        simp [add_assoc] 
      | cons a x s₁ s₂ r step => 
        simp [mul]
        apply funext; intro x₀
        rw [← append_coords]
        rw [← append_coords]
        simp [coords]
        let rel' : ElementaryMove R G 
          ((a, x) :: s₁)
            ((a, x) :: s₂) := by 
            apply ElementaryMove.cons
            assumption 
        let prev  := first_arg_invariant  _ _ tail' rel' 
        let pl := congrFun prev x₀
        rw [pl]
        let ps := mulTerm_invariant b h x₀ s₁ s₂ r
        rw [ps]       
      | swap a₁ a₂ x₁ x₂ tail => 
        simp [mul]
        apply funext; intro x₀
        rw [← append_coords]
        rw [← append_coords]
        simp
        rw [mulTerm]
        rw [mulTerm]
        rw [coords]
        rw [coords]
        rw [mulTerm]
        rw [mulTerm]
        rw [coords]
        rw [coords]
        simp
        let rel' : ElementaryMove R G 
          ((a₁, x₁) :: (a₂, x₂) :: tail)
            ((a₂, x₂) :: (a₁, x₁) :: tail) := by 
            apply ElementaryMove.swap
        let prev  := first_arg_invariant  _ _ tail' rel' 
        let pl := congrFun prev x₀
        rw [pl]
        simp 
        rw [← add_assoc]
        rw [← add_assoc]
        simp
        conv =>
          lhs 
          congr
          congr
          rw [add_comm]    
        



def FreeModule.mul : FreeModule R G → FreeModule R G → FreeModule R G := by
  let f  := fun (s : FormalSum R G) => 
    fun  (t : FreeModule R G) => mulAux  s t 
  apply  Quotient.lift f
  apply func_eql_of_move_equiv  
  intro s₁ s₂ rel
  simp 
  apply funext
  apply Quotient.ind 
  intro t
  let lhs : mulAux s₁ (Quotient.mk (formalSumSetoid R G) t) = 
    ⟦FormalSum.mul s₁ t⟧ := by rfl
  let rhs : mulAux s₂ (Quotient.mk (formalSumSetoid R G) t) = 
    ⟦FormalSum.mul s₂ t⟧ := by rfl
  rw [lhs, rhs]
  simp
  apply Quotient.sound
  apply first_arg_invariant
  exact rel
  