/-
This is for experimentation with free objects. Given the type X, we construct
a free "Nat-module" with basis X.
-/

abbrev X := Nat × Nat × Nat

abbrev FormalSum : Type := List (Nat × X)

inductive basicRel : FormalSum   → FormalSum   →  Prop where
| zeroCoeff (tail: FormalSum )(x: X)(a : Nat)(h: a = 0):  basicRel  ((a, x):: tail) tail 
| addCoeffs (a b: Nat)(x: X)(tail: FormalSum):  
        basicRel  ((a, x) :: (b, x) :: tail) ((a + b, x) :: tail)
| cons (a: Nat)(x: X)(s₁ s₂ : FormalSum ):
        basicRel  s₁ s₂ → basicRel ((a, x) :: s₁) ((a, x) ::  s₂)

def NatSpan := Quot (basicRel )

def monoCoeff (x₀ : X) (nx : Nat × X) : Nat := 
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

def coeffSum(x₀ : X) : FormalSum → Nat
| [] => 0
| h :: l => (monoCoeff x₀ h) + (coeffSum x₀ l)

open basicRel in
theorem coeff_well_defined (x₀ : X)(s₁ s₂: FormalSum)(h: basicRel s₁ s₂):
        coeffSum x₀  s₁ = coeffSum x₀ s₂ := by
          induction h with
          | zeroCoeff tail x a hyp => simp [coeffSum, hyp, monoCoeffZero]
          | addCoeffs a b x tail => 
            simp [coeffSum, monoCoeffZero]
            simp [coeffSum, ← Nat.add_assoc, monoCoeffHom]
          | cons a x s₁ s₂ r => 
            let step := coeff_well_defined x₀ s₁ s₂ r 
            simp [coeffSum, step]

def NatSpan.coeff (x₀ : X) : NatSpan → Nat := 
      Quot.lift (coeffSum x₀) (coeff_well_defined x₀)

