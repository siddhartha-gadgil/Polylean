/-
This is for experimentation with free objects. Given the type X, we construct
a free "Nat-module" with basis X.
-/

variable (X: Type)[DecidableEq X]

def FormalSum : Type := List (Nat × X)

inductive basicRel : FormalSum X  → FormalSum X   →  Prop where
| zeroCoeff (tail: FormalSum X)(x: X)(a : Nat)(h: a = 0):  
        basicRel  ((a, x):: tail) tail 
| addCoeffs (a b: Nat)(x: X)(tail: FormalSum X):  
        basicRel  ((a, x) :: (b, x) :: tail) ((a + b, x) :: tail)
| cons (a: Nat)(x: X)(s₁ s₂ : FormalSum X):
        basicRel  s₁ s₂ → basicRel ((a, x) :: s₁) ((a, x) ::  s₂)
| swap (a₁ a₂: Nat)(x₁ x₂: X)(tail : FormalSum X):
        basicRel  ((a₁, x₁) :: (a₂, x₂) :: tail) 
                    ((a₂, x₂) :: (a₁, x₁) :: tail)

def NatSpan := Quot (@basicRel X)

def monoCoeff {X: Type}[DecidableEq X](x₀ : X) (nx : Nat × X) : Nat := 
  match  (nx.2 == x₀) with 
  | true => nx.1
  | false => 0

theorem monoCoeffHom (x₀ x : X)(a b : Nat) :
    monoCoeff x₀ (a + b, x) = monoCoeff x₀ (a, x) + monoCoeff x₀ (b, x) := by
    repeat (rw [monoCoeff])
    cases x==x₀ <;> rfl

theorem monoCoeffZero (x₀ x : X) : monoCoeff x₀ (0, x) = 0 :=
    by 
      rw [monoCoeff]
      cases x==x₀ <;> rfl

def coeffSum(x₀ : X) : FormalSum X → Nat
| [] => 0
| h :: l => (monoCoeff x₀ h) + (coeffSum x₀ l)

open basicRel in
theorem coeff_well_defined (x₀ : X)(s₁ s₂: FormalSum X)(h: basicRel X s₁ s₂):
        coeffSum X x₀  s₁ = coeffSum X x₀ s₂ := by
          induction h with
          | zeroCoeff tail x a hyp => simp [coeffSum, hyp, monoCoeffZero]
          | addCoeffs a b x tail => 
            simp [coeffSum, monoCoeffZero, ← Nat.add_assoc, monoCoeffHom]
          | cons a x s₁ s₂ r step => 
            simp [coeffSum, step]
          | swap a₁ a₂ x₁ x₂ tail => 
            simp [coeffSum, ← Nat.add_assoc, Nat.add_comm]

def NatSpan.coeff (x₀ : X) : NatSpan X → Nat := 
      Quot.lift (coeffSum X x₀) (coeff_well_defined X x₀)

