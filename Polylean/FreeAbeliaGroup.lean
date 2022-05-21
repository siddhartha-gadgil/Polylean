import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
import Polylean.Morphisms
import Polylean.ProductGroups
import Polylean.EnumDecide
open SubNegMonoid

-- currently mainly experiments


section Zhom

variable {A : Type} [abg : AddCommGroup A]

def zhom (a: A) : ℤ → A := 
  fun n => abg.gsmul n a

theorem gsmul_succ (n: ℤ) (x : A) : gsmul (n+1) x = x + gsmul n x  := by 
    cases n  
    case ofNat k => 
      apply abg.gsmul_succ'
    case negSucc k => 
      induction k with
      | zero => 
        simp
        simp [add_zero]
        have l : -[1+ 0] + 1 = 0 := by rfl
        rw [l]
        have l₀ : gsmul 0 x = 0 := by apply abg.gsmul_zero'
        rw [l₀]
        simp
        rw [abg.gsmul_neg']
        simp
        let l : gsmul 1 x = 
                x + gsmul (0) x := abg.gsmul_succ' 0 x
        rw [l]
        rw [l₀]
        simp
      | succ l ih => 
        have l₀ : -[1+ Nat.succ l] + 1 = -[1+ l] := by rfl
        rw [l₀]
        rw [abg.gsmul_neg']
        rw [abg.gsmul_neg']
        simp

        let l₁ := abg.gsmul_succ' (l + 1) x
        simp at l₁
        rw [l₁]
        simp
        let y := gsmul (l + 1) x
        show -y = x + -(x + y)
        apply Eq.symm
        conv =>
          lhs
          arg 2
          rw [add_comm]
        let l₁ : y + (x + -(y + x)) = y + -y := 
            by
              conv =>
                rhs
                rw [add_comm]
              rw [neg_add_self]
              rw [← add_assoc]
              let l₃ := add_comm (y + x) (- (y + x))
              rw [l₃]
              rw [neg_add_self]
        let l₂ := add_left_cancel l₁
        assumption      


theorem isHom₁ (x : A) (n : ℤ) (m: Nat) : 
      zhom x (n + m) = zhom x n + zhom x m :=
  by 
    induction m with
    | zero =>
      simp [zhom]
      rw [abg.gsmul_zero']
      simp     
    | succ k ih =>
      simp [zhom]
      simp [zhom] at ih
      rw [← add_assoc]
      simp
      let l₁ := abg.gsmul_succ' k x
      simp at l₁
      rw [l₁]
      simp
      let l₂ := gsmul_succ (n + k) x
      simp at l₂
      rw [l₂] 
      rw [ih]
      simp
      conv =>
        lhs
        rw [← add_assoc]
        arg 1
        rw [add_comm]
      rw [← add_assoc]

theorem isHom₂ (x : A) (n m : Nat) : 
        zhom x ((Int.negSucc n) + (Int.negSucc m)) = 
          zhom x (Int.negSucc m) + zhom x (Int.negSucc n) :=
  by
    simp [zhom]
    repeat (rw [abg.gsmul_neg'])
    simp
    simp [Int.add]
    have l₀ : -[1+ n] + -[1+ m] = -[1+ (n + m) + 1] := by rfl
    rw [l₀]
    rw [abg.gsmul_neg']
    simp
    have l₁ : ((n : ℤ) + m + 1 + 1) = (n + 1) + (m + 1) := by 
        rw [← add_assoc]
        simp [add_comm]
        rw [← add_assoc]
        simp [add_comm]
    rw [l₁]
    simp 
    let l₂ := isHom₁ x (n  + 1) (m + 1)
    simp [zhom] at l₂
    rw [l₂]
    simp
    let a := gsmul (n + 1) x
    let b := gsmul (m + 1) x
    show -(a + b) = -b + -a
    have lab : (-(a + b) + a) + b = (-b + -a + a) + b := by 
          conv =>
            lhs
            rw [add_assoc]
          rw [neg_add_self]
          let la := add_assoc (-b) (-a) (a + b)
          rw [← add_assoc] at la
          rw [la]
          simp      
    let lab₁ := add_right_cancel lab 
    let lab₂ := add_right_cancel lab₁
    assumption


theorem zhom_is_hom (x: A) (n m : ℤ) :
  zhom x (n + m) = zhom x n + zhom x m := by
  cases m
  case ofNat k =>
    apply isHom₁ x n k
  case negSucc k =>
    cases n
    case ofNat l =>
      let l₀ := isHom₁ x (Int.negSucc k) l
      rw [add_comm] at l₀
      conv =>
        rhs
        rw [add_comm]
      assumption
    case negSucc l =>
      let l₁ := isHom₂ x l k
      conv =>
        rhs
        rw [add_comm]
      assumption
  
theorem zhom_one (x : A) : zhom x 1 = x := by
  simp [zhom]
  let l : gsmul 1 x = x + gsmul 0 x := abg.gsmul_succ' 0 x
  rw [l]
  rw [abg.gsmul_zero' x]
  simp [add_zero]
  
instance zhomHom(a : A) : AddCommGroup.Homomorphism  (zhom a) := 
  ⟨zhom_is_hom a⟩

theorem unique_morphism_nat (f g : ℤ → A)[AddCommGroup.Homomorphism f]
        [AddCommGroup.Homomorphism g]: 
          f 1 = g 1  → ∀ n: ℕ, f (n + 1) = g (n + 1) := by
          intro hyp
          intro n
          induction n with
          | zero =>
            simp [hyp]            
          | succ k ih => 
            let lf := add_dist f (Nat.succ k) 1
            rw [lf]
            let lg := add_dist g (Nat.succ k) 1
            rw [lg]
            rw [hyp]
            simp [add_right_cancel]
            assumption

theorem unique_morphism (f g : ℤ → A)[AddCommGroup.Homomorphism f]
        [AddCommGroup.Homomorphism g]: f 1 = g 1  → f = g := by
          intro hyp
          have fzero : f (Int.ofNat Nat.zero) = 0 := 
            by
                apply zero_image f
          have gzero : g (Int.ofNat Nat.zero) = 0 := 
            by
                apply zero_image g
          apply funext
          intro n
          cases n
          case ofNat k =>
            cases k
            case zero => 
              rw [fzero, gzero]
            case succ k' =>
              apply unique_morphism_nat f g hyp
          case negSucc k =>
            have fn : f (Int.negSucc k)  = -f (k + 1) := by
              let l := neg_push f (k + 1) 
              rw [← l]
              rfl
            have gn : g (Int.negSucc k)  = -g (k + 1) := by
              let l := neg_push g (k + 1) 
              rw [← l]
              rfl
            rw [fn, gn]
            let l := unique_morphism_nat f g hyp k
            rw [l]           



end Zhom

class FreeAbelianGroup(F: Type)[AddCommGroup F]
  (X: Type)(i: X → F) where
  inducedMap : (A: Type) →  [AddCommGroup A] →  (X → A) → (F → A)
  induced_extends{A: Type}[AddCommGroup A] : ∀ f : X → A, (inducedMap A f) ∘ i = f
  induced_hom: (A: Type) → [abg : AddCommGroup A] → 
      (f : X → A) →  AddCommGroup.Homomorphism (@inducedMap A abg f)
  unique_extension{A: Type}[AddCommGroup A] 
    (f g : F → A)[AddCommGroup.Homomorphism f][AddCommGroup.Homomorphism g] :
       f ∘ i = g ∘ i  → f = g 

theorem unique_extension{F: Type}[AddCommGroup F]
  {X: Type}(i: X → F)[fgp : FreeAbelianGroup F X i]{A: Type}[AddCommGroup A] 
    (f g : F → A)[AddCommGroup.Homomorphism f][AddCommGroup.Homomorphism g] :
       f ∘ i = g ∘ i  → f = g := fgp.unique_extension f g

def unitBasis : Unit → ℤ  := fun _ => 1

instance intFree : FreeAbelianGroup ℤ Unit unitBasis where
  inducedMap := fun A _ f => zhom (f ())
  induced_extends := by
    intro A _ f
    apply funext; intro u
    simp [unitBasis]
    apply zhom_one 

  induced_hom := by
    intro A abg f
    simp
    exact ⟨zhom_is_hom (f ())⟩
  unique_extension := by
    intro A abg f g fh gh hyp
    let at1 := congrFun hyp ()
    simp [unitBasis] at at1
    apply unique_morphism f g at1

open EnumDecide

def decideHomsEqual{F: Type}[AddCommGroup F]
  (X: Type)(i: X → F)[fgp : FreeAbelianGroup F X i]
  {A: Type}[AddCommGroup A][DecidableEq A][DecideForall X]
    (f g : F → A)[AddCommGroup.Homomorphism f][AddCommGroup.Homomorphism g] :
      Decidable (f = g) := 
        if c : ∀ x : X, f (i x) = g (i x) then 
        by
          apply Decidable.isTrue
          apply unique_extension i f g
          apply funext
          intro x  
          exact c x
        else by
          apply Decidable.isFalse
          intro contra
          let c' : ∀ (x : X), f (i x) = g (i x) := by
            intro x
            apply congrFun contra (i x)
          contradiction 

instance decHomsEqual{F: Type}[AddCommGroup F]
  {X: Type}{i: X → F}[fgp : FreeAbelianGroup F X i]
  {A: Type}[AddCommGroup A][DecidableEq A][DecideForall X]
    (f g : F → A)[AddCommGroup.Homomorphism f][AddCommGroup.Homomorphism g] :
      Decidable (f = g) := by apply decideHomsEqual X i

section Product

variable {A B : Type _} [AddCommGroup A] [AddCommGroup B]
variable {X_A X_B : Type _} (i_A : X_A → A) (i_B : X_B → B)
variable [FAb_A : FreeAbelianGroup A X_A i_A] [FAb_B : FreeAbelianGroup B X_B i_B]

def ι : (X_A ⊕ X_B) → A × B
  | Sum.inl x_a => (i_A x_a, 0)
  | Sum.inr x_b => (0, i_B x_b)

def inducedMap (G : Type _) [AddCommGroup G] (f : X_A ⊕ X_B → G) : A × B → G
  | (a, b) =>
    let f_A : X_A → G := f ∘ Sum.inl
    let f_B : X_B → G := f ∘ Sum.inr
    let ϕ_A : A → G := FAb_A.inducedMap _ G f_A
    let ϕ_B : B → G := FAb_B.inducedMap _ G f_B
    ϕ_A a + ϕ_B b

instance : FreeAbelianGroup (A × B) (X_A ⊕ X_B) (@ι A B _ _ X_A X_B i_A i_B) :=
  {
    inducedMap := inducedMap i_A i_B
    induced_extends := sorry
    induced_hom := sorry
    unique_extension := sorry
  }

end Product

namespace Z3

-- elements in the basis `X` of Z3 ; to be mapped by inclusion
def  ex : Unit ⊕ Unit ⊕ Unit := Sum.inl ()
def  ey : Unit ⊕ Unit ⊕ Unit := Sum.inr (Sum.inl ())
def  ez : Unit ⊕ Unit ⊕ Unit := Sum.inr (Sum.inr ())

end Z3