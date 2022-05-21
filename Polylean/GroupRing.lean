import Polylean.FreeModule

/-
Group ring given a group. The ring structures is constructed using the universal property of R-modules, with uniqueness used to show that it is a ring. This is only an additional structure, i.e., no need to wrap. 
-/

variable {R : Type} [Ring R] [DecidableEq R]

variable {G: Type} [Group G] [DecidableEq G]


def FormalSum.mulMonom (b: R)(h: G) : FormalSum R G → FormalSum R G 
| [] => []
| (a, g) :: tail => (a * b, g * h) :: (mulMonom b h tail)

def FormalSum.mul(fst: FormalSum R G) : FormalSum R G → FormalSum R G
| [] =>    []
| (b, h) :: ys =>  
  (FormalSum.mulMonom  b h fst) ++ (mul fst ys)

open FormalSum

namespace GroupRing

theorem mul_monom_zero (g x₀: G)(s: FormalSum R G):
  coords (mulMonom 0 g s) x₀ = 0 := by
  induction s with
  | nil =>  
    simp [mulMonom, coords]
  | cons h t ih => 
    simp [mulMonom, coords, monom_coords_at_zero]
    assumption

theorem mul_monom_dist(b : R)(h x₀ : G)(s₁ s₂: FormalSum R G):
  coords (mulMonom b h (s₁  ++ s₂)) x₀ = coords (mulMonom b h s₁) x₀ + coords (mulMonom b h s₂) x₀ := by
    induction s₁ with
    | nil => 
      simp [mulMonom, coords]
    | cons head tail ih =>
      simp [mulMonom, coords]
      rw [ih]
      simp [add_assoc]

theorem mul_dist(x₀ : G)(s₁ s₂ s₃: FormalSum R G):
  coords (mul s₁ (s₂  ++ s₃)) x₀ = coords (mul s₁ s₂) x₀ + coords (mul s₁ s₃) x₀ := by
    induction s₂ with
    | nil => 
      simp [mulMonom, coords]
    | cons head tail ih =>
      simp [mulMonom, coords, mul]
      rw [← append_coords]
      rw [← append_coords]
      rw [ih]
      simp [add_assoc]

theorem mul_monom_monom_assoc(a b : R)(h x₀ : G)(s : FormalSum R G):
  coords (mulMonom b h (mulMonom a x s)) x₀ = 
    coords (mulMonom (a * b) (x * h) s) x₀  := by 
    induction s with
    | nil => 
      simp [mulMonom, coords]
    | cons head tail ih =>
      let (a₁, x₁) := head
      simp [mulMonom, coords, mul_assoc]
      rw [ih]

theorem mul_monom_assoc(b : R)(h x₀ : G)(s₁ s₂: FormalSum R G):
  coords (mulMonom b h (mul s₁ s₂)) x₀ = 
    coords (mul s₁ (mulMonom b h s₂)) x₀  := by
    induction s₂ with
    | nil => 
      simp [mulMonom, coords]
    | cons head tail ih =>
      let (a, x) := head
      simp [mulMonom, coords, mul]
      rw [← append_coords]
      simp
      rw [mul_monom_dist]
      rw [ih]
      simp [add_assoc, mulMonom]
      rw [mul_monom_monom_assoc]

theorem mul_monom_add(b₁ b₂ : R)(h x₀ : G)(s: FormalSum R G):
  coords (mulMonom (b₁ + b₂) h s) x₀ = coords (mulMonom b₁ h s) x₀ + coords (mulMonom b₂ h s) x₀ := by
  induction s with
  | nil => 
  simp [mulMonom, coords]
  | cons head tail ih => 
    let (a, g) := head
    simp [mulMonom, coords]
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
      simp [mul, mulMonom]
      apply eqlCoords.refl
    case cons head tail ih =>
      simp [mul, mulMonom]
      apply funext ; intro x₀
      simp [coords]
      rw [monom_coords_at_zero]
      rw [zero_add]
      rw [← append_coords]
      simp [coords, mul]
      let l := mul_monom_zero h x₀ tail
      rw [l]
      simp [zero_add]

/-- Quotient in second argument for group ring multiplication 
-/
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
    let l := mul_monom_zero g x₀ s
    rw [l]
    simp [zero_add]
  | addCoeffs a b x tail =>
    apply Quotient.sound
    apply funext; intro x₀
    simp [mul]
    repeat (rw [← append_coords])
    simp
    simp [mul_monom_add, add_assoc]    
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
        (coords (mulMonom a₁ x₁ s) x₀)
        (coords (mulMonom a₂ x₂ s) x₀)
    rw [lc] 

open ElementaryMove
theorem mul_monom_invariant (b : R)(h x₀ : G)(s₁ s₂ : FormalSum R G)
    (rel : ElementaryMove R G s₁ s₂) : 
      coords (mulMonom b h s₁) x₀ = 
      coords (mulMonom b h s₂) x₀ := by
      induction rel with
      | zeroCoeff tail g a hyp => 
        rw [hyp]
        simp [mulMonom, coords,monom_coords_at_zero]
      | addCoeffs a₁ a₂ x tail => 
        simp [mulMonom, coords, right_distrib, monom_coords_hom, add_assoc]
        
      | cons a x t₁ t₂ r step => 
        simp [mulMonom, coords, step]
      | swap a₁ a₂ x₁ x₂ tail => 
        simp [mulMonom, coords]
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
        simp [mul, mulMonom]
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
        let ps := mul_monom_invariant b h x₀ s₁ s₂ r
        rw [ps]       
      | swap a₁ a₂ x₁ x₂ tail => 
        simp [mul]
        apply funext; intro x₀
        rw [← append_coords]
        rw [← append_coords]
        simp
        rw [mulMonom]
        rw [mulMonom]
        rw [coords]
        rw [coords]
        rw [mulMonom]
        rw [mulMonom]
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
        
def mul : FreeModule R G → FreeModule R G → FreeModule R G := by
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

instance groupRingMul : Mul (FreeModule R G) := 
  ⟨mul⟩

instance : One (FreeModule R G) := 
  ⟨⟦[(1, 1)]⟧⟩


instance : Ring (FreeModule R G) :=
  {
    zero := ⟦ []⟧
    add := FreeModule.add
    add_assoc := FreeModule.addn_assoc
    add_zero := FreeModule.addn_zero
    zero_add := FreeModule.zero_addn
    neg := fun x => (-1 : R) • x

    nsmul_zero' := by intros; rfl
    nsmul_succ' := by intros; rfl
    sub_eq_add_neg := by 
      intro x y 
      rfl
    gsmul_zero' := by intros; rfl
    gsmul_succ' := by intros; rfl
    gsmul_neg' := by intros; rfl

    add_left_neg := by 
        intro x
        let l := FreeModule.coeff_distrib (-1 : R) (1 : R) x
        simp at l
        have lc : (-1 : R) + 1 = 0 := by 
            apply add_left_neg
        rw [lc] at l
        rw [FreeModule.unit_coeff] at l
        rw [FreeModule.zero_coeff] at l
        exact l

    add_comm := FreeModule.addn_comm

    mul := mul
    left_distrib := by
      apply @Quotient.ind (motive := fun a  =>
        ∀ b c, a * (b + c) = a * b + a * c)
      intro x
      apply @Quotient.ind₂ (motive := fun b c =>
        ⟦ x ⟧ * (b + c) = ⟦ x ⟧ * b + ⟦ x ⟧ * c)
      intro y z
      apply Quotient.sound
      induction y with
      | nil => 
          simp
          simp [FormalSum.mul]
          apply eqlCoords.refl
      | cons h t ih => 
          simp [FormalSum.mul]
          apply funext; intro x₀
          repeat (rw [← append_coords])
          simp
          let lih := congrFun ih x₀
          rw [← append_coords] at lih
          rw [lih]
          simp [add_assoc]
    right_distrib := by
      apply @Quotient.ind (motive := fun a  =>
        ∀ b c, (a + b) * c = a * c + b * c)
      intro x
      apply @Quotient.ind₂ (motive := fun b c =>
        (⟦ x ⟧ + b) * c = ⟦ x ⟧ * c + b * c)
      intro y z
      apply Quotient.sound
      induction z with
      | nil => 
          simp
          simp [FormalSum.mul]
          apply eqlCoords.refl
      | cons h t ih => 
          let (a, h) := h
          simp [FormalSum.mul, mulMonom]
          apply funext; intro x₀
          repeat (rw [← append_coords])
          simp
          let lih := congrFun ih x₀
          rw [← append_coords] at lih
          rw [lih]
          simp [add_assoc]
          rw [mul_monom_dist]
          simp [add_assoc, add_left_cancel]
          conv =>
            lhs
            arg 2
            rw [← add_assoc]
            arg 1
            rw [add_comm]
          conv =>
            rhs
            arg 2
            rw [← add_assoc]

    zero_mul := by
      apply Quotient.ind
      intro x
      apply Quotient.sound
      induction x with
      | nil =>        
        rfl
      | cons h t ih =>        
        rw [FormalSum.mul]
        simp
        apply funext ; intro x₀
        let lih := congrFun ih x₀
        rw [coords] at lih
        rw [← append_coords]
        rw [lih]
        simp
        rw [mulMonom]

    mul_zero := by 
      apply Quotient.ind
      intro x
      rfl

    one := ⟦[(1, 1)]⟧
    natCast := fun n => ⟦ [(n, 1)] ⟧
    natCast_zero := 
      by
      apply Quotient.sound
      apply funext; intro x₀
      simp [coords, monomCoeff]
      cases 1 == x₀ <;> rfl
    natCast_succ := by 
      intro n
      apply Quotient.sound
      apply funext; intro x₀
      rw [← append_coords]
      simp
      cases m:1 == x₀ with
      | true =>
          repeat (rw [coords])
          repeat (rw [monomCoeff])
          simp
          rw [m]
      | false => 
          repeat (rw [coords])
          repeat (rw [monomCoeff])
          simp
          rw [m]
          simp          
    mul_assoc := by
      apply @Quotient.ind (motive := fun a  =>
        ∀ b c, a * b * c = a * (b * c))
      intro x
      apply @Quotient.ind₂ (motive := fun b c =>
        ⟦ x ⟧ * b * c = ⟦ x ⟧ * (b  * c))
      intro y z
      apply Quotient.sound
      apply funext; intro x₀
      simp [coords]
      induction z with
      | nil => 
          simp
          simp [FormalSum.mul]
      | cons h t ih => 
          let (a, h) := h
          simp [FormalSum.mul, mulMonom]
          repeat (rw [← append_coords])
          rw [mul_dist]
          rw [ih]
          rw [mul_monom_assoc]
    mul_one := by
      apply Quotient.ind
      intro x
      apply Quotient.sound
      apply funext; intro x₀
      repeat (rw[FormalSum.mul])
      simp
      induction x with
      | nil => rfl
      | cons h t ih => 
        let (a, x) := h
        rw [mulMonom, coords, monomCoeff]
        simp
        rw [coords, monomCoeff]
        cases m:x == x₀ <;> simp [ih]
        
    one_mul := by
      apply Quotient.ind
      intro x
      apply Quotient.sound
      apply funext; intro x₀
      induction x with
      | nil => rfl
      | cons h t ih => 
        let (a, x) := h
        repeat (rw [coords])
        simp
        rw [FormalSum.mul]
        rw [← append_coords]
        simp [ih, mulMonom, coords]
    npow_zero' := by
      apply Quotient.ind
      intro x
      apply Quotient.sound
      apply eqlCoords.refl
    npow_succ' := by
      intro n x
      rw [npow_rec]

    intCast := fun n => 
      match n with 
      | Int.ofNat k =>  ⟦ [(Int.ofNat k, 1)] ⟧
      | Int.negSucc k => - ⟦ [(Int.ofNat k + 1, 1)] ⟧
    intCast_ofNat := by 
      intro n
      apply Quotient.sound
      apply funext; intro x₀
      simp
    intCast_negSucc := by 
      intro n
      simp
      simp [NonUnitalNonAssocSemiring.natCast]            
  }



  
end GroupRing