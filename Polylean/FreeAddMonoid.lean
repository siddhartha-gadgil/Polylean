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

             

def monomCoeff {X: Type}[DecidableEq X](x₀ : X) (nx : Nat × X) : Nat := 
  match  (nx.2 == x₀) with 
  | true => nx.1
  | false => 0

theorem monomCoeffHom (x₀ x : X)(a b : Nat) :
    monomCoeff x₀ (a + b, x) = monomCoeff x₀ (a, x) + monomCoeff x₀ (b, x) := by
    repeat (rw [monomCoeff])
    cases x==x₀ <;> rfl

theorem monomCoeffZero (x₀ x : X) : monomCoeff x₀ (0, x) = 0 :=
    by 
      rw [monomCoeff]
      cases x==x₀ <;> rfl

def FormalSum.coeff{X: Type}[DecidableEq X](x₀ : X) : FormalSum X → Nat
| [] => 0
| h :: l => (monomCoeff x₀ h) + (coeff x₀ l)

open basicRel in
theorem coeff_well_defined (x₀ : X)(s₁ s₂: FormalSum X)(h: basicRel X s₁ s₂):
        FormalSum.coeff  x₀  s₁ = FormalSum.coeff  x₀ s₂ := by
          induction h with
          | zeroCoeff tail x a hyp => simp [FormalSum.coeff, hyp, monomCoeffZero]
          | addCoeffs a b x tail => 
            simp [FormalSum.coeff, monomCoeffZero, ← Nat.add_assoc, monomCoeffHom]
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
              contradiction
            | cons head tail hyp => 
              let (a, x) := head
              intro pos
              cases c:x == x₀ with
              | true => 
                let k := FormalSum.coeff x₀ tail
                have lem : a + k = 
                      FormalSum.coeff x₀ ((a, x) :: tail) := 
                        by rw [FormalSum.coeff, monomCoeff, c]
                have c'' : x = x₀ := 
                        of_decide_eq_true c
                rw [c'']
                rw [c''] at lem
                cases c':k with
                | zero => 
                  have lIneq : tail.length < List.length ((a, x) :: tail) := 
                    by 
                      simp [List.length_cons]
                      apply Nat.le_refl
                  rw [c', Nat.add_zero] at lem
                  rw [← lem]   
                  exact ⟨tail, rfl, lIneq⟩
                | succ k' => 
                  have pos : 0  < k := by 
                    rw [c']
                    apply Nat.zero_lt_succ
                  let ⟨ys, eqnStep, lIneqStep⟩ := hyp pos
                  have eqn₁ : 
                    (a, x₀) :: (k, x₀) :: ys ≅ (a + k, x₀) :: ys := by
                    apply Quot.sound 
                    apply basicRel.addCoeffs
                  have eqn₂ : 
                  (a, x₀) :: (k, x₀) :: ys ≅ (a, x₀) :: tail := 
                    by 
                      apply consEquiv
                      assumption
                  have eqn : (a + k, x₀) :: ys ≅ 
                          (a, x₀) :: tail :=
                      Eq.trans (Eq.symm eqn₁) eqn₂    
                  rw [← lem]
                  have lIneq : ys.length < List.length ((a, x₀) :: tail) :=
                    by
                    apply Nat.le_trans lIneqStep 
                    simp [List.length_cons, Nat.le_succ]
                  exact ⟨ys, eqn, lIneq⟩
              | false =>
                let k := FormalSum.coeff x₀ tail
                have lem : k = 
                      FormalSum.coeff x₀ ((a, x) :: tail) := 
                        by 
                          simp [FormalSum.coeff, monomCoeff, c, Nat.zero_add]
                rw [← lem] at pos          
                let ⟨ys', eqnStep, lIneqStep⟩ := hyp pos   
                rw [← lem]
                let ys := (a, x) :: ys'      
                have lIneq : ys.length < ((a, x) :: tail).length := 
                  by 
                    simp [List.length_cons]
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

theorem zeroCoeffs{X: Type}[DecidableEq X](s: FormalSum X)
               (hyp :∀ x: X, s.coeff x = 0) : s ≅ [] := 
               match s with 
               | [] => rfl
               | h :: t => by
                let (a₀, x₀) := h
                let hyp₀ := hyp x₀
                rw [FormalSum.coeff] at hyp₀
                have c₀ : monomCoeff x₀ (a₀, x₀) = a₀ := by
                    simp [monomCoeff]                     
                rw [c₀] at hyp₀
                have hyp₁ : a₀ + FormalSum.coeff x₀ t  
                    - (FormalSum.coeff x₀ t ) = 0 - FormalSum.coeff x₀ t  :=
                      congrArg (fun m => m - FormalSum.coeff x₀ t ) hyp₀
                simp [Nat.add_sub_cancel] at hyp₁
                rw [hyp₁]
                let tailCoeffs : (x: X) → FormalSum.coeff x t = 0 :=
                      by
                        intro x
                        let hx := hyp x
                        rw [FormalSum.coeff, Nat.add_comm] at hx
                        let hx' :=
                          congrArg (fun m => m - (monomCoeff x (a₀, x₀)) ) hx
                        simp [Nat.add_sub_cancel] at hx'
                        exact hx'
                let step := zeroCoeffs t tailCoeffs
                let l₀ : (0, x₀) :: t ≅ t := 
                   Quot.sound <| basicRel.zeroCoeff  t x₀ 0 rfl
                exact Eq.trans l₀ step

