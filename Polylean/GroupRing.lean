import Polylean.FreeModule

/-
Group ring given a group. The ring structures is constructed using the universal property of R-modules, with uniqueness used to show that it is a ring. This is only an additional structure, i.e., no need to wrap. 
-/

variable (R : Type) [Ring R] [DecidableEq R]

variable (G: Type) [Group G] [DecidableEq G]


def FormalSum.mulTerm (b: R)(h: G) : FormalSum R G → FormalSum R G 
| [] => []
| (a, g) :: tail => (a * b, g * h) :: (mulTerm b h tail)

def FormalSum.mul(fst: FormalSum R G) : FormalSum R G → FormalSum R G
| [] =>    []
| (b, h) :: ys =>  
  (FormalSum.mulTerm R G b h fst) ++ (mul fst ys)

open FormalSum

theorem mulTerm_zero (g x₀: G)(s: FormalSum R G):
  coords (mulTerm R G 0 g s) x₀ = 0 := by
  induction s with
  | nil =>  
    simp [mulTerm, coords]
  | cons h t ih => 
    simp [mulTerm, coords, monom_coords_at_zero]
    assumption

theorem mul_zero_cons (s t : FormalSum R G)(g: G): 
    mul R G s ((0, h) :: t) ≈  mul R G s t := by
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
      let l := mulTerm_zero R G h x₀ tail
      rw [l]
      simp [zero_add]
  
def mulAux : FormalSum R G → FreeModule R G → FreeModule R G := by
  intro s
  let f  := fun t => ⟦ FormalSum.mul R G s t ⟧ 
  apply  Quotient.lift f
  apply func_eql_of_move_equiv
  intro t t rel
  simp 
  induction rel with
  | zeroCoeff tail g a hyp =>
    rw [hyp]
    apply Quotient.sound
    simp [mul]
    apply funext
    intro x₀
    rw [← append_coords]
    let l := mulTerm_zero R G g x₀ s
    rw [l]
    simp [zero_add]
  | addCoeffs a b x tail =>
    apply Quotient.sound
    apply funext; intro x₀
    simp [mul]
    repeat (rw [← append_coords])
    admit
    
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
        (coords (mulTerm R G a₁ x₁ s) x₀)
        (coords (mulTerm R G a₂ x₂ s) x₀)
    rw [lc] 
