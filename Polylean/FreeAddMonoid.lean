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

namespace FormalSum

def sum {X: Type} [DecidableEq X] (s: FormalSum X): NatSpan X :=
      Quot.mk (basicRel X) s

def equiv {X: Type} [DecidableEq X] (s₁ s₂: FormalSum X): Prop :=
      s₁.sum = s₂.sum

end FormalSum

infix:65 " ≅ " => FormalSum.equiv

open FormalSum

theorem consEquiv{X: Type}[DecidableEq X] (s₁ s₂ : FormalSum X) (a: Nat) (x: X):
      s₁ ≅ s₂ → (a, x) :: s₁ ≅ (a, x) :: s₂  := by
        intro h
        let f : FormalSum X → NatSpan X := 
            fun s => sum <| (a, x) :: s
        let wit : (s₁ s₂ : FormalSum X) → (basicRel X s₁ s₂) → f s₁ = f s₂ :=
            by
            intro s₁ s₂ hyp
            apply Quot.sound
            apply basicRel.cons
            assumption
        let g := Quot.lift f wit
        let factorizes : 
            (s : FormalSum X) → g (s.sum) = 
              sum ((a, x) :: s) := Quot.liftBeta f wit
        rw[equiv]
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
theorem coeff_move_invariant (x₀ : X)(s₁ s₂: FormalSum X)(h: basicRel X s₁ s₂):
        coeff  x₀  s₁ = coeff  x₀ s₂ := by
          induction h with
          | zeroCoeff tail x a hyp => simp [coeff, hyp, monomCoeffZero]
          | addCoeffs a b x tail => 
            simp [coeff, monomCoeffZero, ← Nat.add_assoc, monomCoeffHom]
          | cons a x s₁ s₂ r step => 
            simp [coeff, step]
          | swap a₁ a₂ x₁ x₂ tail => 
            simp [coeff, ← Nat.add_assoc, Nat.add_comm]

def NatSpan.coeff (x₀ : X) : NatSpan X → Nat := 
      Quot.lift (FormalSum.coeff  x₀) (coeff_move_invariant X x₀)

theorem coeff_factors (x: X)(s: FormalSum X):
      NatSpan.coeff X x (sum s) = coeff x s := by
      simp [NatSpan.coeff]
      apply Quot.liftBeta
      apply coeff_move_invariant

theorem coeff_well_defined (x: X)(s₁ s₂: FormalSum X):
      s₁ ≅ s₂ → (coeff x s₁) = (coeff x s₂) := by
        intro hyp
        simp [← coeff_factors, NatSpan.coeff]
        rw [hyp]
        

theorem tail_coeffs (x₀ x : X)(a: Nat) (s: FormalSum X):
      s.coeff x₀ = 
        (coeff x₀ ((a, x) :: s)) - monomCoeff x₀ (a, x) := 
        by
          simp [coeff]
          rw [Nat.add_comm]
          simp [Nat.add_sub_cancel]
          

def coeffComplement (x₀ : X)(s : FormalSum X) :
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
                let k := coeff x₀ tail
                have lem : a + k = 
                      coeff x₀ ((a, x) :: tail) := 
                        by rw [coeff, monomCoeff, c]
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
                let k := coeff x₀ tail
                have lem : k = 
                      coeff x₀ ((a, x) :: tail) := 
                        by 
                          simp [coeff, monomCoeff, c, Nat.zero_add]
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
                rw [coeff] at hyp₀
                have c₀ : monomCoeff x₀ (a₀, x₀) = a₀ := by
                    simp [monomCoeff]                     
                rw [c₀] at hyp₀
                have hyp₁ : a₀ + coeff x₀ t  
                    - (coeff x₀ t ) = 0 - coeff x₀ t  :=
                      congrArg (fun m => m - coeff x₀ t ) hyp₀
                simp [Nat.add_sub_cancel] at hyp₁
                rw [hyp₁]
                let tailCoeffs : (x: X) → coeff x t = 0 :=
                      by
                        intro x
                        let hx := hyp x
                        rw [coeff, Nat.add_comm] at hx
                        let hx' :=
                          congrArg (fun m => m - (monomCoeff x (a₀, x₀)) ) hx
                        simp [Nat.add_sub_cancel] at hx'
                        exact hx'
                let step := zeroCoeffs t tailCoeffs
                let l₀ : (0, x₀) :: t ≅ t := 
                   Quot.sound <| basicRel.zeroCoeff  t x₀ 0 rfl
                exact Eq.trans l₀ step

theorem equalCoeffs{X: Type}[DecidableEq X](s₁ s₂: FormalSum X)
               (hyp :∀ x: X, s₁.coeff x = s₂.coeff x) : s₁ ≅ s₂ := 
               match mt:s₁ with 
               | [] => 
                have coeffs : ∀ x: X, s₂.coeff x = 0 := by
                  intro x
                  let h := hyp x
                  rw [← h]
                  rfl
                let zl := zeroCoeffs s₂ coeffs
                Eq.symm zl
               | h :: t => 
                  let (a₀, x₀):= h
                  if p: 0  < a₀ then 
                    let a₁ := coeff x₀ t
                    if p₁: 0 < a₁ then
                      by
                        let ⟨ys, eqn, ineqn⟩ := coeffComplement X x₀ t p₁
                        let s₃ := (a₀ + a₁, x₀) :: ys
                        have eq₁ : (a₀, x₀) :: (a₁ , x₀) :: ys ≅ s₃ := by 
                          apply Quot.sound
                          let lem := basicRel.addCoeffs a₀ a₁ x₀ ys
                          exact lem
                        have eq₂ : (a₀, x₀) :: (a₁ , x₀) :: ys ≅ 
                            (a₀, x₀) :: t := by 
                              apply consEquiv
                              assumption
                        have eq₃ : s₃ ≅ s₂ := by 
                          have bd : ys.length + 1 < t.length + 1 := 
                            by
                              apply Nat.succ_lt_succ
                              exact ineqn
                          apply equalCoeffs
                          intro x
                          rw [← hyp x]
                          simp [coeff]
                          let d := coeff_well_defined X x _ _ eqn
                          rw [coeff] at d
                          rw [← d]
                          simp [monomCoeffHom]
                          simp [coeff, 
                            Nat.add_assoc]
                        apply Eq.trans (Eq.trans (Eq.symm eq₂) eq₁) eq₃ 
                    else
                      let p' : a₁ = 0 := by
                      cases Nat.eq_zero_or_pos a₁ with
                      | inl h => exact h
                      | inr h => contradiction
                      by
                        have cf₂ : s₂.coeff x₀ = a₀ := by
                          rw [← hyp]
                          simp [coeff]
                          have lem : coeff x₀ t = 0 := p'
                          simp [lem, Nat.add_zero]
                          simp [monomCoeff]
                        let ⟨ys, eqn, ineqn⟩ := 
                          coeffComplement X x₀ s₂ (by 
                            rw [cf₂]
                            assumption)
                        let cfs := fun x => 
                          coeff_well_defined X x _ _ eqn
                        rw [cf₂] at cfs
                        let cfs' := fun (x: X) =>
                          Eq.trans (hyp x) (Eq.symm (cfs x))
                        simp [coeff] at cfs'
                        let cs'' : ∀ x: X,
                            coeff x t = ys.coeff x := by
                              intro x
                              let c := cfs' x
                              exact Nat.add_left_cancel c 
                        let step := 
                          equalCoeffs t ys cs''
                        let step' := consEquiv t ys a₀ x₀ step 
                        rw [cf₂] at eqn
                        exact Eq.trans step' eqn  
                  else 
                    let p' : a₀ = 0 := by
                      cases Nat.eq_zero_or_pos a₀ with
                      | inl h => exact h
                      | inr h => contradiction                     
                    have eq₁ : (a₀, x₀) :: t ≅ t := by 
                        apply Quot.sound
                        rw [p']
                        apply basicRel.zeroCoeff
                        rfl
                    have eq₂ : t ≅ s₂ := by 
                      apply equalCoeffs t s₂
                      intro x
                      let ceq := coeff_well_defined X x ((a₀, x₀) :: t) t eq₁
                      simp [← ceq, hyp]
                    Eq.trans eq₁ eq₂
termination_by _ X s _ _  => s.length

def FormalSum.support{X: Type}[DecidableEq X](s: FormalSum X) : List X :=
        s.map <| fun (_, x) => x

theorem coeff_support{X: Type}[DecidableEq X](s: FormalSum X) :
        ∀ x: X, 0 < s.coeff x  → x ∈ s.support  := 
          match s with 
          | [] => fun x hyp => 
            by
              have d : coeff x [] = 0 := by rfl
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
                rw [coeff, monomCoeff, p, Nat.zero_add] at hyp
                let step := coeff_support t x hyp
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

def equalOnSupport{X: Type}[DecidableEq X](l: List X)(f g : X → Nat) : Prop :=
  match l with
  | [] => true
  | h :: t =>
    (f h = g h) ∧ (equalOnSupport t f g)

theorem equal_on_support_of_equal{X: Type}[DecidableEq X](l: List X)(f g : X → Nat):
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

theorem mem_of_equal_on_support{X: Type}[DecidableEq X](l: List X)
    (f g : X → Nat)(x : X)(mhyp: x ∈ l) : 
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

def decideEqualOnSupport{X: Type}[DecidableEq X](l: List X)(f g : X → Nat) :
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


instance {X: Type}[DecidableEq X]{l: List X}{f g : X → Nat} :
    Decidable (equalOnSupport l f g) := decideEqualOnSupport l f g

def decideEquiv{X: Type}[DecidableEq X](s₁ s₂ : FormalSum X) : 
  Decidable (s₁ ≅ s₂) := 
        let c₁ := fun x => coeff x s₁
        let c₂ := fun x => coeff x s₂
        if ch₁ : equalOnSupport s₁.support c₁ c₂ then
          if ch₂ : equalOnSupport s₂.support c₁ c₂ then
            Decidable.isTrue ( 
              by
              apply equalCoeffs
              intro x
              cases (Nat.eq_zero_or_pos <| c₁ x) with
              | inl hz₁ => 
                  cases (Nat.eq_zero_or_pos <| c₂ x) with
                | inl hz₂ =>
                    have ceq: c₁ x = c₂ x := 
                      by rw [hz₁, hz₂] 
                    exact ceq
                | inr hp => 
                  have lem : x ∈ s₂.support := by 
                      apply coeff_support
                      assumption
                  let lem' :=   
                    mem_of_equal_on_support s₂.support c₁ c₂ x lem ch₂
                  exact lem'
              | inr hp => 
                have lem : x ∈ s₁.support := by 
                    apply coeff_support
                    assumption
                let lem' :=   
                  mem_of_equal_on_support s₁.support c₁ c₂ x lem ch₁
                exact lem'
              )
          else
            Decidable.isFalse (
              by
                intro contra
                have ceq: c₁ = c₂ := by
                  apply funext
                  intro x
                  apply coeff_well_defined
                  assumption
                let lem :=
                  equal_on_support_of_equal s₂.support c₁ c₂ ceq 
                contradiction
            )
        else
          Decidable.isFalse (
            by
              intro contra
              have ceq: c₁ = c₂ := by
                apply funext
                intro x
                apply coeff_well_defined
                assumption
              let lem :=
                equal_on_support_of_equal s₁.support c₁ c₂ ceq 
              contradiction
          )
  
instance {X: Type}[DecidableEq X]{s₁ s₂ : FormalSum X} : 
  Decidable (s₁ ≅ s₂) := decideEquiv s₁ s₂
