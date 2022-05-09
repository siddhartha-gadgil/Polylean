variable (X: Type)[DecidableEq X]

abbrev FormalSum : Type := List (Nat × X)

inductive BasicRel : FormalSum X  → FormalSum X   →  Prop where
| zeroCoeff (tail: FormalSum X)(x: X)(a : Nat)(h: a = 0):  
        BasicRel  ((a, x):: tail) tail 
| addCoeffs (a b: Nat)(x: X)(tail: FormalSum X):  
        BasicRel  ((a, x) :: (b, x) :: tail) ((a + b, x) :: tail)
| cons (a: Nat)(x: X)(s₁ s₂ : FormalSum X):
        BasicRel  s₁ s₂ → BasicRel ((a, x) :: s₁) ((a, x) ::  s₂)
| swap (a₁ a₂: Nat)(x₁ x₂: X)(tail : FormalSum X):
        BasicRel  ((a₁, x₁) :: (a₂, x₂) :: tail) 
                    ((a₂, x₂) :: (a₁, x₁) :: tail)


def linear_extension{X: Type}[DecidableEq X](f₀ : X → Nat) : FormalSum X → Nat
| [] => 0
| h :: t => 
      let (a, x) := h
      a * f₀ x + (linear_extension f₀ t)
termination_by _ _ s => s.length

set_option maxHeartbeats 2000000

open BasicRel in
theorem invariance_of_linear_extension{X: Type}[DecidableEq X](f₀ : X → Nat) :
    (∀ s₁ s₂ : FormalSum X, ∀ rel : BasicRel X s₁ s₂, linear_extension f₀ s₁ = linear_extension f₀ s₂) := 
    fun s₁ s₂ rel =>
    match s₁, s₂, rel with
        | (a, x) :: tail, .(tail), zeroCoeff .(tail) .(x) .(a) hyp => by
          rw [hyp]
          simp [linear_extension] 
        | (a, x) :: (b, .(x)) :: tail, .((a + b, x) :: tail), 
          addCoeffs .(a) .(b) .(x) .(tail) => by
            simp [linear_extension, ← Nat.add_assoc]
            have step : a * f₀ x + b * f₀ x = (a + b) * f₀ x := 
              by simp [Nat.right_distrib]
            rw [← step]
        | (a, x) :: t₁, (.(a), .(x)) :: t₂, cons .(a) .(x) .(t₁) .(t₂) r =>
          by
            simp [linear_extension, ← Nat.add_assoc]
            let ih := invariance_of_linear_extension f₀ t₁ t₂ r
            rw [ih]
        | (a₁, x₁) :: (a₂, x₂) :: tail, 
            (.(a₂), .(x₂)) :: (.(a₁), .(x₁)) :: .(tail) ,
              swap .(a₁) .(a₂) .(x₁) .(x₂) .(tail) => by 
              simp [linear_extension, ← Nat.add_assoc]
              have step : a₁ * f₀ x₁ + a₂ * f₀ x₂ = a₂ * f₀ x₂ + a₁ * f₀ x₁ :=
                  by simp [Nat.add_comm]
              rw [step]
termination_by _ _ s₁ s₂ => s₁.length

#check invariance_of_linear_extension