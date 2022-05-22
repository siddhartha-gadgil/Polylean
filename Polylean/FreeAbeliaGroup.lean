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
  (X: Type) where
  i: X → F
  inducedMap : (A: Type) →  [AddCommGroup A] →  (X → A) → (F → A)
  induced_extends{A: Type}[AddCommGroup A] : ∀ f : X → A, (inducedMap A f) ∘ i = f
  induced_hom: (A: Type) → [abg : AddCommGroup A] → 
      (f : X → A) →  AddCommGroup.Homomorphism (@inducedMap A abg f)
  unique_extension{A: Type}[AddCommGroup A] 
    (f g : F → A)[AddCommGroup.Homomorphism f][AddCommGroup.Homomorphism g] :
       f ∘ i = g ∘ i  → f = g 

theorem unique_extension{F: Type}[AddCommGroup F]
  {X: Type}[fgp : FreeAbelianGroup F X]{A: Type}[AddCommGroup A] 
    (f g : F → A)[AddCommGroup.Homomorphism f][AddCommGroup.Homomorphism g] :
       f ∘ fgp.i = g ∘ fgp.i  → f = g := fgp.unique_extension f g

@[inline] def fromBasis {F: Type}[AddCommGroup F]
  {X: Type}[fag : FreeAbelianGroup F X]{A: Type}[AddCommGroup A]
  (f: X → A) : F → A := by
    apply fag.inducedMap
    exact f

instance fromBasisHom {F: Type}[AddCommGroup F]
  {X: Type}[fag : FreeAbelianGroup F X]{A: Type}[AddCommGroup A]
  {f: X → A} : @AddCommGroup.Homomorphism F A _ _ 
    (@fromBasis F _ X  fag A _ f) := by
    apply fag.induced_hom

@[inline] def fromBasisFamily (F: Type)[AddCommGroup F]
  {X: Type}[fag : FreeAbelianGroup F X]{A: Type}[AddCommGroup A](D: Type)
  (f: D → X → A) : D →  F → A := by
    intro p
    apply fag.inducedMap
    exact f p

instance inducedHomomorphism (F : Type) [AddCommGroup F] {X : Type} [fag : FreeAbelianGroup F X]
  {A : Type} [abg : AddCommGroup A] (f : X → A) : AddCommGroup.Homomorphism (fag.inducedMap A f) :=
    fag.induced_hom A f

instance fromBasisFamilyHom {F: Type}[AddCommGroup F]
  {X: Type}[fag : FreeAbelianGroup F X]{A: Type}[AddCommGroup A]{D : Type}
  {f: D → X → A}{p : D} :  @AddCommGroup.Homomorphism F A _ _ 
    ((@fromBasisFamily F _ X  fag A _ D f) p) := by
    apply fag.induced_hom

instance fromBasisHom' {F: Type}[AddCommGroup F]
  {X: Type}[fag : FreeAbelianGroup F X]{A: Type}[AddCommGroup A]
  {f: X → A} : @AddCommGroup.Homomorphism F A _ _ 
    (fag.inducedMap A f) := by
    apply fag.induced_hom


def unitBasis : Unit → ℤ  := fun _ => 1

instance intFree : FreeAbelianGroup ℤ Unit  where
  i := unitBasis
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

-- example
abbrev double : ℤ → ℤ := fromBasis (fun _ : Unit => 2)

def dblHom : AddCommGroup.Homomorphism (double ) := inferInstance

abbrev egAction : Fin 2 → ℤ → ℤ 
| ⟨0, _⟩ => fromBasis (fun _ : Unit => 1)
| ⟨1, _⟩ => fromBasis (fun _ : Unit => -1)

def egHom₀  : AddCommGroup.Homomorphism (egAction 0) := inferInstance

-- def egHom (x: Fin 2)  : AddCommGroup.Homomorphism (egAction x) := inferInstance -- fails


-- decidability

def decideHomsEqual{F: Type}[AddCommGroup F]
  (X: Type)[fgp : FreeAbelianGroup F X]
  {A: Type}[AddCommGroup A][DecidableEq A][DecideForall X]
    (f g : F → A)[AddCommGroup.Homomorphism f][AddCommGroup.Homomorphism g] :
      Decidable (f = g) := 
        if c : ∀ x : X, f (fgp.i x) = g (fgp.i x) then 
        by
          apply Decidable.isTrue
          apply fgp.unique_extension f g
          apply funext
          intro x  
          exact c x
        else by
          apply Decidable.isFalse
          intro contra
          let c' : ∀ (x : X), f (fgp.i x) = g (fgp.i x) := by
            intro x
            apply congrFun contra (fgp.i x)
          contradiction 

instance decHomsEqual{F: Type}[AddCommGroup F]
  {X: Type}[fgp : FreeAbelianGroup F X]
  {A: Type}[AddCommGroup A][DecidableEq A][DecideForall X]
    (f g : F → A)[AddCommGroup.Homomorphism f][AddCommGroup.Homomorphism g] :
      Decidable (f = g) := by apply decideHomsEqual X 

-- proof of being an action

def egActionBasis' : Fin 2 → Unit → ℤ 
| ⟨0, _⟩ => fun _ => 1
| ⟨1, _⟩ => fun _ => -1

abbrev egAction' := fromBasisFamily ℤ (Fin 2)  (egActionBasis')

def egHom' (x: Fin 2)  : 
  AddCommGroup.Homomorphism (egAction' x) := inferInstance -- works!

def egHom'' (x y: Fin 2)  : 
  AddCommGroup.Homomorphism <| 
      (egAction' x) ∘ (egAction' y) := inferInstance -- works!

theorem egIsAction: ∀ (x y: Fin 2), 
  (egAction' x) ∘ (egAction' y) = egAction' (x + y) := by decide -- works!
section Product

variable {A B : Type _} [AddCommGroup A] [AddCommGroup B]
variable {X_A X_B : Type _} 
variable [FAb_A : FreeAbelianGroup A X_A] [FAb_B : FreeAbelianGroup B X_B ]

def ι : (X_A ⊕ X_B) → A × B
  | Sum.inl x_a => (FAb_A.i x_a, 0)
  | Sum.inr x_b => (0, FAb_B.i x_b)

def inducedMap (G : Type _) [AddCommGroup G] (f : X_A ⊕ X_B → G) : A × B → G
  | (a, b) =>
    let f_A : X_A → G := f ∘ Sum.inl
    let f_B : X_B → G := f ∘ Sum.inr
    let ϕ_A : A → G := FAb_A.inducedMap  G f_A
    let ϕ_B : B → G := FAb_B.inducedMap  G f_B
    ϕ_A a + ϕ_B b

instance prodFree : FreeAbelianGroup (A × B) (X_A ⊕ X_B)  :=
  {
    i := ι
    inducedMap := inducedMap 
    induced_extends := by
      intro G GrpG f
      simp [inducedMap]
      apply funext
      intro x
      simp
      cases x
      · rename_i x_A
        simp [ι]
        have fA_extends := congrFun (FAb_A.induced_extends (f ∘ Sum.inl)) x_A
        simp at fA_extends
        rw [fA_extends]
        have : FreeAbelianGroup.inducedMap G (f ∘ Sum.inr) (0 : B) = (0 : G) := by
              rw [zero_image (FAb_B.inducedMap G (f ∘ Sum.inr))]
        rw [this, add_zero]
      · rename_i x_B
        simp [ι]
        have fB_extends := congrFun (FAb_B.induced_extends (f ∘ Sum.inr)) x_B
        simp at fB_extends
        rw [fB_extends]
        have : FreeAbelianGroup.inducedMap G (f ∘ Sum.inl) (0 : A) = (0 : G) := by
          rw [zero_image (FAb_A.inducedMap G (f ∘ Sum.inl))]
        rw [this, zero_add]
    induced_hom := by
      intro G GrpG f
      apply AddCommGroup.Homomorphism.mk
      intro (a, b)
      intro (a', b')
      simp [inducedMap, DirectSum.directSum_mul]
      rw [add_dist (FAb_A.inducedMap G (f ∘ Sum.inl)), add_dist (FAb_B.inducedMap G (f ∘ Sum.inr))]
      rw [add_assoc, add_assoc, add_left_cancel_iff, ← add_assoc, ← add_assoc, add_right_cancel_iff, add_comm]
    unique_extension := by
      intro G GrpG f g Homf Homg
      intro h
      apply funext
      intro (a, b)
      have coordsplit : (a, b) = (a, 0) + (0, b) := by
        have := DirectSum.directSum_add a 0 0 b
        rw [zero_add, add_zero] at this
        exact Eq.symm this
      rw [coordsplit, Homf.add_dist, Homg.add_dist]
      have A_unique : f ∘ ι₁ = g ∘ ι₁ := by
        apply FAb_A.unique_extension (f ∘ ι₁) (g ∘ ι₁)
        apply funext
        intro x_A
        simp [ι₁]
        have := congrFun h (Sum.inl x_A)
        simp [ι] at this
        assumption
      have B_unique : f ∘ ι₂ = g ∘ ι₂ := by
        apply FAb_B.unique_extension (f ∘ ι₂) (g ∘ ι₂)
        apply funext
        intro x_B
        simp [ι₂]
        have := congrFun h (Sum.inr x_B)
        simp [ι] at this
        assumption
      have acoordeq : f (a, 0) = g (a, 0) := congrFun A_unique a
      have bcoordeq : f (0, b) = g (0, b) := congrFun B_unique b
      rw [acoordeq, bcoordeq]
  }

end Product

namespace Z3

-- elements in the basis `X` of Z3 ; to be mapped by inclusion
def  ex : Unit ⊕ Unit ⊕ Unit := Sum.inl ()
def  ey : Unit ⊕ Unit ⊕ Unit := Sum.inr (Sum.inl ())
def  ez : Unit ⊕ Unit ⊕ Unit := Sum.inr (Sum.inr ())

def onX {α : Type _} : α × α × α →   Unit ⊕ Unit ⊕ Unit → α 
| (a, _, _), (Sum.inl _) => a
| (_, b, _), (Sum.inr (Sum.inl _)) => b
| (_, _, c), (Sum.inr (Sum.inr _)) => c


instance free : FreeAbelianGroup (ℤ × ℤ × ℤ) (Unit ⊕ Unit ⊕ Unit) :=
        inferInstance

end Z3
