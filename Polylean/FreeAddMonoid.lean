/-
This is for experimentation with free objects. Given the type X, we construct
a free "Nat-module" with basis X.
-/

abbrev X := Nat × Nat × Nat

example : ((1, 2, 3) : X) = ((1, 2, 3) : X) := by decide

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

theorem coeff_well_defined (x₀ : X)(s₁ s₂: FormalSum)(h: basicRel s₁ s₂):
        coeffSum x₀  s₁ = coeffSum x₀ s₂ := 
      match s₁, s₂, h with
      | (a, x) :: tail, .(tail), basicRel.zeroCoeff  .(tail) .(x) .(a) hyp => by
        simp [coeffSum, hyp, monoCoeffZero]
      | (a, x) :: (b, .(x)) :: tail, _, basicRel.addCoeffs .(a) .(b) .(x) .(tail) => by
          simp [coeffSum, ← Nat.add_assoc, monoCoeffHom] 
      | (a, x) :: s₁, (_, _) :: s₂  , basicRel.cons .(a) .(x) .(s₁) .(s₂) r => by
        let step := coeff_well_defined x₀ s₁ s₂ r 
        simp [coeffSum, step]


