/-
This is for experimentation with free objects. Given the type X, we construct
a free "Nat-module" with basis X.
-/

variable (X: Type)[DecidableEq X]

abbrev FormalSum : Type := List (Nat × X)

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

def NatSpan := Quot (basicRel X)

def FormalSum.sum {X: Type} [DecidableEq X] (s: FormalSum X): NatSpan X :=
      Quot.mk (basicRel X) s

def FormalSum.equiv {X: Type} [DecidableEq X] (s₁ s₂: FormalSum X): Prop :=
      s₁.sum = s₂.sum

infix:65 " ≅ " => FormalSum.equiv

theorem consEquiv{X: Type}[DecidableEq X] (s₁ s₂ : FormalSum X) (a: Nat) (x: X):
      s₁ ≅ s₂ → (a, x) :: s₁ ≅ (a, x) :: s₂  := by
        intro h
        let f : FormalSum X → NatSpan X := 
            fun s => FormalSum.sum <| (a, x) :: s
        let wit : (s₁ s₂ : FormalSum X) → (basicRel X s₁ s₂) → f s₁ = f s₂ :=
            by
            intro s₁ s₂ hyp
            apply Quot.sound
            apply basicRel.cons
            assumption
        let g := Quot.lift f wit
        let factorizes : 
            (s : FormalSum X) → g (s.sum) = 
              FormalSum.sum ((a, x) :: s) := Quot.liftBeta f wit
        rw[FormalSum.equiv]
        rw [← factorizes]
        rw [← factorizes]
        rw [h]

             

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

def FormalSum.coeff{X: Type}[DecidableEq X](x₀ : X) : FormalSum X → Nat
| [] => 0
| h :: l => (monoCoeff x₀ h) + (coeff x₀ l)

open basicRel in
theorem coeff_well_defined (x₀ : X)(s₁ s₂: FormalSum X)(h: basicRel X s₁ s₂):
        FormalSum.coeff  x₀  s₁ = FormalSum.coeff  x₀ s₂ := by
          induction h with
          | zeroCoeff tail x a hyp => simp [FormalSum.coeff, hyp, monoCoeffZero]
          | addCoeffs a b x tail => 
            simp [FormalSum.coeff, monoCoeffZero, ← Nat.add_assoc, monoCoeffHom]
          | cons a x s₁ s₂ r step => 
            simp [FormalSum.coeff, step]
          | swap a₁ a₂ x₁ x₂ tail => 
            simp [FormalSum.coeff, ← Nat.add_assoc, Nat.add_comm]

def NatSpan.coeff (x₀ : X) : NatSpan X → Nat := 
      Quot.lift (FormalSum.coeff  x₀) (coeff_well_defined X x₀)

theorem coeffComplement (x₀ : X)(s : FormalSum X) :
        0 < s.coeff x₀  → 
          (∃ ys: FormalSum X, 
            (((s.coeff x₀, x₀) :: ys) ≅ s) ∧ 
            (List.length ys < s.length))  := by 
            induction s with 
            | nil =>
              intro contra
              have l : FormalSum.coeff x₀ [] = 0 := by rfl
              rw [l] at contra
              let l' := Nat.not_succ_le_zero _ contra  
              exact False.elim l'
            | cons head tail hyp => 
              let (a, x) := head
              intro pos
              cases c:x == x₀ with
              | true => 
                  admit
              | false =>
                let k := FormalSum.coeff x₀ tail
                have lem : FormalSum.coeff x₀ tail = 
                      FormalSum.coeff x₀ ((a, x) :: tail) := 
                        by 
                          rw [FormalSum.coeff, monoCoeff]
                          rw [c]
                          simp [Nat.zero_add]
                rw [← lem] at pos          
                let ⟨ys', eqnStep, lIneqStep⟩ := hyp pos   
                rw [← lem]
                let ys := (a, x) :: ys'      
                have lIneq : ys.length < ((a, x) :: tail).length := 
                  by 
                    have d : ys.length = ys'.length + 1 := by rfl
                    have d' : ((a, x) :: tail).length = tail.length + 1 := 
                        by rfl
                    rw [d, d']
                    apply Nat.succ_lt_succ
                    exact lIneqStep
                have eqn₁ : 
                  (k, x₀) :: ys ≅ (a, x) :: (k, x₀) :: ys' := by
                    apply Quot.sound 
                    apply basicRel.swap
                have eqn₂ : 
                  (a, x) :: (k, x₀) :: ys' ≅ (a, x) :: tail := 
                    by 
                      apply consEquiv
                      assumption 
                have eqn : (k, x₀) :: ys ≅ (a, x) :: tail := by 
                    exact Eq.trans eqn₁ eqn₂
                exact ⟨ys, eqn, lIneq⟩
termination_by _ s => s.length
