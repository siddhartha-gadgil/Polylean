import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Defs
import Polylean.SMul

/-!
Free module over a ring `R` over a set `X`. It is assumed that both `R` and `X` have decidable equality. This is to obtain decidable equality for the elements of the module, which we do. We choose our definition to allow both such computations and to prove results.

The definition is as a quotient of *Formal Sums*, which are simply lists of pairs `(a,x)` where `a` is a coefficient in `R` and `x` is a term in `X`. We associate to such a formal sum a coordinate function `X → R`. We see that having the same coordinate functions gives an equivalence relation on the formal sums. The free module is then defined as the corresponding quotient of such formal sums.

We also give an alternative description via moves, which is more convenient for universal properties.
-/

variable {R : Type} [Ring R] [DecidableEq R]

variable {X : Type} [DecidableEq X]

/-! I. Formal sums and coordinate functions 
  * define formal sums as List (R × X)
  * define coordinate functions X → R for formal sums
  * define (weak) support, relate non-zero coordinates and decide equality 
-/
section FormalSumCoords

/-- Formal Sums -/
abbrev FormalSum (R X : Type) [Ring R] [DecidableEq R][DecidableEq X] :=
  List (R × X)

/-- coordinates for a formal sum with one term.
-/
def monomCoeff (R X : Type) [Ring R] [DecidableEq R][DecidableEq X](x₀ : X) (nx : R × X) : R :=
  match (nx.2 == x₀) with
  | true => nx.1
  | false => 0

/-- homomorphism property for coordinates for a formal sum with one term. -/
theorem monom_coords_hom  (x₀ x : X) (a b : R) : monomCoeff R X x₀ (a + b, x) = monomCoeff R X x₀ (a, x) + monomCoeff R X x₀ (b, x) := by
  repeat
    (
      rw [monomCoeff])
  cases x == x₀ <;> simp

/-- associativity of scalar multiplication coordinates for a formal sum with one term. -/
theorem monom_coords_mul (x₀ : X) (a b : R) : monomCoeff R X x₀ (a * b, x) = a * monomCoeff R X x₀ (b, x) := by
  repeat
    (
      rw [monomCoeff])
  cases x == x₀ <;> simp

/-- coordinates for a formal sum with one term with scalar `0`.
-/
theorem monom_coords_at_zero (x₀ x : X) : monomCoeff R X x₀ (0, x) = 0 := by
  rw [monomCoeff]
  cases x == x₀ <;> rfl

/-- coordinates for a formal sum -/
def FormalSum.coords  : FormalSum R X → X → R
  | [], _ => 0
  | h :: t, x₀ => monomCoeff R X x₀ h + coords t x₀

/-- support for a formal sum in a weak sense (coordinates may vanish on this) -/
def FormalSum.support  (s : FormalSum R X) : List X :=
  s.map <| fun (_, x) => x

open FormalSum

/-- support contains elements `x : X` where the coordinate is not `0` -/
theorem nonzero_coord_in_support  (s : FormalSum R X) : ∀ x : X, 0 ≠ s.coords x → x ∈ s.support :=
  match s with
  | [] => fun x hyp => by
    have d : coords [] x = (0 : R) := by
      rfl
    rw [d] at hyp
    contradiction
  | h :: t => by
    intro x hyp
    let (a₀, x₀) := h
    have d : support ((a₀, x₀) :: t) = x₀ :: (support t) := by
      rfl
    rw [d]
    match p : x₀ == x with
    | true =>
      have eqn : x₀ = x := of_decide_eq_true p
      rw [eqn]
      apply List.mem_of_elem_eq_true
      simp [List.elem]
    | false =>
      rw [coords, monomCoeff, p, zero_add] at hyp
      let step := nonzero_coord_in_support t x hyp
      apply List.mem_of_elem_eq_true
      simp [List.elem]
      have p' : (x == x₀) = false := by
        have eqn := of_decide_eq_false p
        have eqn' : ¬(x = x₀) := by
          intro contra
          let contra' := Eq.symm contra
          contradiction
        exact decide_eq_false eqn'
      rw [p']
      apply List.elem_eq_true_of_mem
      exact step

/-- being equal on all elements is a given list
-/
def equalOnSupport  (l : List X) (f g : X → R) : Prop :=
  match l with
  | [] => true
  | h :: t => (f h = g h) ∧ (equalOnSupport t f g)

/-- equal functions are equal on arbitrary supports-/
theorem equal_on_support_of_equal  (l : List X) (f g : X → R) :
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

/-- functions equal on support `l` are equal on each `x ∈ l`-/
theorem mem_of_equal_on_support  (l : List X) (f g : X → R) (x : X)(mhyp : x ∈ l) : equalOnSupport l f g → f x = g x :=
  match l with
  | [] => by
    contradiction
  | h :: t => by
    intro hyp
    simp [equalOnSupport] at hyp
    cases mhyp
    exact hyp.left
    have inTail : x ∈ t := by
      assumption
    have step := mem_of_equal_on_support t f g x inTail hyp.right
    exact step

/-- decidability of equality on support-/
def decideEqualOnSupport  (l : List X) (f g : X → R) : Decidable (equalOnSupport l f g) :=
  match l with
  | [] =>
    Decidable.isTrue
      (by
        simp [equalOnSupport])
  | h :: t => by
    simp [equalOnSupport]
    cases (decideEqualOnSupport t f g)with
    | isTrue hs =>
      exact
        (if c : f h = g h then (Decidable.isTrue ⟨c, hs⟩)
        else by
          apply Decidable.isFalse
          intro contra
          have contra' := contra.left
          contradiction)
    | isFalse hs =>
      apply Decidable.isFalse
      intro contra
      have contra' := contra.right
      contradiction



/-- decidability of equality on support -/
instance {X : Type} [DecidableEq X] {R : Type} [DecidableEq R] {l : List X} {f g : X → R} : Decidable (equalOnSupport l f g) :=
  decideEqualOnSupport l f g

end FormalSumCoords

/-! II. Quotient Free Module 
  * define relation by having equal coordinates
  * show this is an equivalence relation and take quotient -/
section QuotientFreeModule


/-- relation by equal coordinates-/
def eqlCoords (R X : Type) [Ring R] [DecidableEq R][DecidableEq X](s₁ s₂ : FormalSum R X) : Prop :=
  s₁.coords = s₂.coords

namespace eqlCoords

/-- relation by equal coordinates is reflexive -/
theorem refl  (s : FormalSum R X) : eqlCoords R X s s :=
  by
  rfl

/-- relation by equal coordinates is  symmetric -/
theorem symm  {s₁ s₂ : FormalSum R X} : eqlCoords R X s₁ s₂ → eqlCoords R X s₂ s₁ := by
  intro hyp
  apply funext
  intro x
  apply Eq.symm
  exact congrFun hyp x

/-- relation by equal coordinates is transitive -/
theorem trans  {s₁ s₂ s₃ : FormalSum R X} : eqlCoords R X s₁ s₂ → eqlCoords R X s₂ s₃ → eqlCoords R X s₁ s₃ := by
  intro hyp₁ hyp₂
  apply funext
  intro x
  have l₁ := congrFun hyp₁ x
  have l₂ := congrFun hyp₂ x
  exact Eq.trans l₁ l₂

/-- relation by equal coordinates is an equivalence relation -/
theorem is_equivalence  : Equivalence (eqlCoords R X) :=
  { refl := refl, symm := symm, trans := trans }

end eqlCoords

/-- setoid based on equal coordinates
-/
instance formalSumSetoid (R X : Type) [Ring R] [DecidableEq R][DecidableEq X] : Setoid (FormalSum R X) :=
  ⟨eqlCoords R X, eqlCoords.is_equivalence⟩

/-- Quotient free module -/
abbrev FreeModule (R X : Type) [Ring R] [DecidableEq R][DecidableEq X] :=
  Quotient (formalSumSetoid R X)

notation "⟦" a "⟧" => Quotient.mk' a

end QuotientFreeModule

/-! III. Decidable equality on quotient free modules
  * need to relate to Boolean equality to lift to quotient -/
section DecidableEqQuotFreeModule

namespace FreeModule

/-- decidable equality for quotient elements in the free module -/
def decideEqualQuotient  (s₁ s₂ : FormalSum R X) : Decidable (⟦s₁⟧ = ⟦s₂⟧) :=
  if ch₁ : equalOnSupport s₁.support s₁.coords s₂.coords then
    if ch₂ : equalOnSupport s₂.support s₁.coords s₂.coords then
      Decidable.isTrue
        (by
          apply Quotient.sound
          apply funext
          intro x
          exact
            if h₁ : (0 = s₁.coords x) then
              if h₂ : (0 = s₂.coords x) then by
                rw [← h₁, h₂]
              else by
                have lem : x ∈ s₂.support := by
                  apply nonzero_coord_in_support
                  assumption
                let lem' := mem_of_equal_on_support s₂.support s₁.coords s₂.coords x lem ch₂
                exact lem'
            else by
              have lem : x ∈ s₁.support := by
                apply nonzero_coord_in_support
                assumption
              let lem' := mem_of_equal_on_support s₁.support s₁.coords s₂.coords x lem ch₁
              exact lem')
    else
      Decidable.isFalse
        (by
          intro contra
          let lem := equal_on_support_of_equal s₂.support s₁.coords s₂.coords (Quotient.exact contra)
          contradiction)
  else
    Decidable.isFalse
      (by
        intro contra
        let lem := equal_on_support_of_equal s₁.support s₁.coords s₂.coords (Quotient.exact contra)
        contradiction)

instance  {s₁ s₂ : FormalSum R X} :
    Decidable (⟦s₁⟧ = ⟦s₂⟧) :=
  decideEqualQuotient s₁ s₂

/-- boolean equality on support -/
def beqOnSupport  (l : List X) (f g : X → R) :Bool :=
  l.all <| fun x => decide (f x = g x)

/-- equality on support from boolean equality -/
theorem eql_on_support_of_true {l : List X} {f g : X → R} : beqOnSupport l f g = true → equalOnSupport l f g := by
  intro hyp
  induction l with
  | nil =>
    simp [equalOnSupport]
  | cons h t step =>
    simp [equalOnSupport]
    simp [beqOnSupport, List.all] at hyp
    let p₂ := step hyp.right
    exact And.intro hyp.left p₂

/-- boolean equality on support gives equal quotients -/
theorem eqlquot_of_beq_support(s₁ s₂ : FormalSum R X)(c₁ : beqOnSupport s₁.support s₁.coords s₂.coords)(c₂ : beqOnSupport s₂.support s₁.coords s₂.coords) : ⟦s₁⟧ = ⟦s₂⟧ := 
        by
        let ch₁ := eql_on_support_of_true c₁
        let ch₂ := eql_on_support_of_true c₂
        apply Quotient.sound
        apply funext
        intro x
        exact
          if h₁ : (0 = s₁.coords x) then
            if h₂ : (0 = s₂.coords x) then by
              rw [← h₁, h₂]
            else by
              have lem : x ∈ s₂.support := by
                apply nonzero_coord_in_support
                assumption
              let lem' := mem_of_equal_on_support s₂.support s₁.coords s₂.coords x lem ch₂
              exact lem'
          else by
            have lem : x ∈ s₁.support := by
              apply nonzero_coord_in_support
              assumption
            let lem' := mem_of_equal_on_support s₁.support s₁.coords s₂.coords x lem ch₁
            exact lem'


/--
boolean equality for the quotient via lifting
-/
def beq_quot  (x₁ x₂ : FreeModule R X) : Bool := by
  apply Quotient.lift₂ (fun (s₁ s₂ : FormalSum R X) => decide (⟦s₁⟧ = ⟦s₂⟧))
  intro a₁ b₁ a₂ b₂ eqv₁ eqv₂
  let eq₁ : ⟦a₁⟧ = ⟦a₂⟧ := Quot.sound eqv₁
  let eq₂ : ⟦b₁⟧ = ⟦b₂⟧ := Quot.sound eqv₂
  simp [eq₁, eq₂]
  exact x₁
  exact x₂

/--
boolean equality for the quotient is equality
-/
def eq_of_beq_true  : ∀ x₁ x₂ : FreeModule R X, x₁.beq_quot x₂ = true → x₁ = x₂ := by
  let f :=
    @Quotient.ind₂ (FormalSum R X) (FormalSum R X) (formalSumSetoid R X) (formalSumSetoid R X)
      (fun (x₁ x₂ : FreeModule R X) => x₁.beq_quot x₂ = true → x₁ = x₂)
  apply f
  intro s₁ s₂ eqv
  let eql := of_decide_eq_true eqv
  assumption

/--
boolean inequality for the quotient is inequality
-/
def neq_of_beq_false  : ∀ x₁ x₂ : FreeModule R X, x₁.beq_quot x₂ = false → Not (x₁ = x₂) := by
  let f :=
    @Quotient.ind₂ (FormalSum R X) (FormalSum R X) (formalSumSetoid R X) (formalSumSetoid R X)
      (fun (x₁ x₂ : FreeModule R X) => x₁.beq_quot x₂ = false → Not (x₁ = x₂))
  apply f
  intro s₁ s₂ neqv
  let neql := of_decide_eq_false neqv
  assumption

/--
decidable equality for the free module
-/
def decEq  (x₁ x₂ : FreeModule R X) : Decidable (x₁ = x₂) := by
  match p : x₁.beq_quot x₂ with
  | true =>
    apply Decidable.isTrue
    apply FreeModule.eq_of_beq_true
    assumption
  | false =>
    apply Decidable.isFalse
    apply FreeModule.neq_of_beq_false
    assumption

/--
decidable equality for the free module
-/
instance {X : Type} [DecidableEq X] : DecidableEq (FreeModule R X) := fun x₁ x₂ => x₁.decEq x₂

/-- coordinates well defined on the quotient  
-/
theorem equal_coords_of_approx (s₁ s₂ : FormalSum R X): s₁ ≈ s₂ → s₁.coords = s₂.coords := by
    intro hyp
    apply funext; intro x₀
    exact congrFun hyp x₀

/-- coordinates for the quotient -/
def coordinates (x₀ : X) : FreeModule R X →  R := by
  apply Quotient.lift (fun s : FormalSum R X => s.coords x₀)
  intro a b
  intro hyp
  let l :=  equal_coords_of_approx _ _ hyp
  exact congrFun l x₀ 

end FreeModule
end DecidableEqQuotFreeModule

/-! IV. Module structure  -/
section ModuleStruture


open FormalSum
namespace FormalSum
/-- scalar multiplication on formal sums-/
def scmul  : R → FormalSum R X → FormalSum R X
  | _, [] => []
  | r, (h :: t) =>
    let (a₀, x₀) := h
    (r * a₀, x₀) :: (scmul r t)

/-- coordinates after scalar multiplication -/
theorem scmul_coords  (r : R) (s : FormalSum R X) (x₀ : X) : (r * s.coords x₀) = (s.scmul r).coords x₀ := by
  induction s with
  | nil =>
    simp [coords]
  | cons h t ih =>
    simp [scmul, coords, monom_coords_mul, left_distrib, ih]

/-- scalar multiplication on the Free Module-/
def FreeModule.scmul  : R → FreeModule R X → FreeModule R X := by
  intro r
  let f : FormalSum R X → FreeModule R X := fun s => ⟦s.scmul r⟧
  apply Quotient.lift f
  intro s₁ s₂
  simp
  intro hypeq
  apply Quotient.sound
  apply funext
  intro x₀
  have l₁ := scmul_coords r s₁ x₀
  have l₂ := scmul_coords r s₂ x₀
  rw [← l₁, ← l₂]
  rw [hypeq]

/-- coordinates add when appending -/
theorem append_coords  (s₁ s₂ : FormalSum R X) (x₀ : X) : (s₁.coords x₀) + (s₂.coords x₀) = (s₁ ++ s₂).coords x₀ := by
  induction s₁ with
  | nil =>
    simp [coords]
  | cons h t ih =>
    simp [coords, ← ih, add_assoc]

/-- coordinates well defined up to equivalence -/
theorem append_equiv  (s₁ s₂ t₁ t₂ : FormalSum R X) :(s₁ ≈ s₂) → (t₁ ≈ t₂) → s₁ ++ t₁ ≈ s₂ ++ t₂ := by
    intro eqv₁ eqv₂
    apply funext
    intro x₀
    rw [← append_coords]
    rw [← append_coords]
    have eq₁ : eqlCoords R X s₁ s₂ := by assumption
    have ls : coords s₁ x₀ = coords s₂ x₀ := by 
      apply congrFun eqv₁
    have lt : coords t₁ x₀ = coords t₂ x₀ := by 
      apply congrFun eqv₂
    rw [← ls, ← lt]

end FormalSum

/-- addition of elements in the free module -/
def FreeModule.add  : FreeModule R X → FreeModule R X → FreeModule R X := by
  let f : FormalSum R X → FormalSum R X → FreeModule R X := fun s₁ s₂ => ⟦s₁ ++ s₂⟧
  apply Quotient.lift₂ f
  intro a₁ b₁ a₂ b₂
  simp
  intro eq₁ eq₂
  apply Quotient.sound
  apply funext
  intro x₀
  have l₁ := append_coords a₁ b₁ x₀
  have l₂ := append_coords a₂ b₂ x₀
  rw [← l₁, ← l₂]
  rw [eq₁, eq₂]

instance  : Add (FreeModule R X) :=
  ⟨FreeModule.add⟩

instance  : SMul R (FreeModule R X) :=
  ⟨FreeModule.scmul⟩
namespace FormalSum

/-- associativity for scalar multiplication for formal sums -/
theorem action  (a b : R) (s : FormalSum R X) : (s.scmul b).scmul a = s.scmul (a * b) := by
  induction s with
  | nil =>
    simp [scmul]
  | cons h t ih =>
    simp [scmul, ih, mul_assoc]

/-- distributivity for the module operations -/
theorem act_sum (a b : R) (s : FormalSum R X) : (s.scmul a) ++ (s.scmul b) ≈  s.scmul (a + b) := by
  induction s with
  | nil =>
    simp [scmul]
    apply eqlCoords.refl
  | cons h t ih =>
    apply funext; intro x₀
    let il₁ := congrFun ih x₀    
    rw [← append_coords]
    simp [scmul, coords, right_distrib, monom_coords_hom]
    rw [← append_coords] at il₁ 
    rw [← il₁]
    simp
    conv =>
      lhs
      rw [add_assoc]
      arg 2
      rw [← add_assoc]
      arg 1
      rw [add_comm]
    conv =>
      lhs
      rw [add_assoc]
      rw [← add_assoc]
    

end FormalSum

namespace FreeModule

/-- associativity for scalar and ring products -/
theorem module_action  (a b : R) (x : FreeModule R X) : a • (b • x) = (a * b) • x := by
  apply @Quotient.ind (motive := fun x : FreeModule R X => a • (b • x) = (a * b) • x)
  intro s
  apply Quotient.sound
  rw [FormalSum.action]
  apply eqlCoords.refl

/-- commutativity of addition -/
theorem addn_comm  (x₁ x₂ : FreeModule R X) : x₁ + x₂ = x₂ + x₁ := by
  apply @Quotient.ind₂ (motive := fun x₁ x₂ : FreeModule R X => x₁ + x₂ = x₂ + x₁)
  intro s₁ s₂
  apply Quotient.sound
  apply funext
  intro x₀
  let lm₁ := append_coords s₁ s₂ x₀
  let lm₂ := append_coords s₂ s₁ x₀
  rw [← lm₁, ← lm₂]
  simp [add_comm]

theorem add_assoc_aux  (s₁ : FormalSum R X) (x₂ x₃ : FreeModule R X) : (⟦s₁⟧ + x₂) + x₃ = ⟦s₁⟧ + (x₂ + x₃) := by
  apply @Quotient.ind₂ (motive := fun x₂ x₃ : FreeModule R X => (⟦s₁⟧ + x₂) + x₃ = ⟦s₁⟧ + (x₂ + x₃))
  intro x₂ x₃
  apply Quotient.sound
  apply funext
  intro x₀
  rw [← append_coords]
  rw [← append_coords]
  rw [← append_coords]
  rw [← append_coords]
  simp [add_assoc]

/-- associativity of addition -/
theorem addn_assoc  (x₁ x₂ x₃ : FreeModule R X) : (x₁ + x₂) + x₃ = x₁ + (x₂ + x₃) := by
  apply @Quotient.ind (motive := fun x₁ : FreeModule R X => (x₁ + x₂) + x₃ = x₁ + (x₂ + x₃))
  intro x₁
  apply add_assoc_aux

def zero : FreeModule R X := ⟦[]⟧

/-- adding zero-/
theorem addn_zero (x: FreeModule R X) : x + zero = x := by
  apply @Quotient.ind (motive := fun x : FreeModule R X => x + zero = x)
  intro x
  apply Quotient.sound
  apply funext
  intro x₀
  rw [← append_coords]
  simp [add_zero, coords]

/-- adding zero-/
theorem zero_addn (x: FreeModule R X) : zero + x = x := by
  apply @Quotient.ind (motive := fun x : FreeModule R X => zero + x = x)
  intro x
  apply Quotient.sound
  apply funext
  intro x₀
  rw [← append_coords]
  simp [add_zero, coords]

/-- distributivity for addition of module elements -/
theorem elem_distrib  (a : R) (x₁ x₂ : FreeModule R X) : a • (x₁ + x₂) = a • x₁ + a • x₂ := by
  apply @Quotient.ind₂ (motive := fun x₁ x₂ : FreeModule R X => a • (x₁ + x₂) = a • x₁ + a • x₂)
  intro s₁ s₂
  apply Quotient.sound
  apply funext
  intro x₀
  rw [← scmul_coords]
  rw [← append_coords]
  rw [← append_coords]
  rw [← scmul_coords]
  rw [← scmul_coords]
  simp [left_distrib]

/-- distributivity with respect to scalars -/
theorem coeffs_distrib (a b: R)(x: FreeModule R X) : a • x + b • x = (a + b) • x:= by
  apply @Quotient.ind (motive := fun x : FreeModule R X => 
    a • x + b • x = (a + b) • x)
  intro s
  apply Quotient.sound
  apply funext
  intro x₀
  let l := act_sum a b s
  let l'' := congrFun l x₀
  exact l''

/-- multiplication by `1: R` -/
theorem unit_coeffs (x: FreeModule R X) : (1 : R) • x =  x:= by
  apply @Quotient.ind (motive := fun x : FreeModule R X => 
    (1 : R) • x =  x)
  intro s
  apply Quotient.sound
  apply funext
  intro x₀
  let l := scmul_coords 1 s x₀
  rw [← l]
  simp

/-- multiplication by `0 : R` -/
theorem zero_coeffs (x: FreeModule R X) : (0 : R) • x =  ⟦ [] ⟧:= by
  apply @Quotient.ind (motive := fun x : FreeModule R X => 
    (0 : R) • x =  ⟦ [] ⟧)
  intro s
  apply Quotient.sound
  apply funext
  intro x₀
  let l := scmul_coords 0 s x₀
  rw [← l]
  simp [coords]

/-- The module is an additive commutative group, mainly proved as a check -/
instance : AddCommGroup (FreeModule R X) :=
  {
    zero := ⟦ []⟧
    add := FreeModule.add
    add_assoc := FreeModule.addn_assoc
    add_zero := FreeModule.addn_zero
    zero_add := FreeModule.zero_addn
    neg := fun x => (-1 : R) • x

    nsmul_zero' := by intros; rfl
    nsmul_succ' := by intros; rfl
    sub_eq_add_neg := by 
      intro x y 
      rfl
    gsmul_zero' := by intros; rfl
    gsmul_succ' := by intros; rfl
    gsmul_neg' := by intros; rfl

    add_left_neg := by 
        intro x
        let l := FreeModule.coeffs_distrib (-1 : R) (1 : R) x
        simp at l
        rw [FreeModule.unit_coeffs] at l
        rw [FreeModule.zero_coeffs] at l
        exact l

    add_comm := FreeModule.addn_comm
  }

end FreeModule

end ModuleStruture

/-! V. Equivalent definition of the relation via moves 
  * define elementary moves on formal sums 
  * show coordinates equal if and only if related by elementary moves
  * hence can define map on Free Module when invariant under elementary moves 
  -/

section ElementaryMoves

open FormalSum
/-- Elementary moves for formal sums -/
inductive ElementaryMove (R X : Type) [Ring R] [DecidableEq R][DecidableEq X] : FormalSum R X → FormalSum R X → Prop where
  | zeroCoeff (tail : FormalSum R X) (x : X) (a : R) (h : a = 0) : ElementaryMove R X ((a, x) :: tail) tail
  | addCoeffs (a b : R) (x : X) (tail : FormalSum R X) : 
    ElementaryMove R X ((a, x) :: (b, x) :: tail) ((a + b, x) :: tail)
  | cons (a : R) (x : X) (s₁ s₂ : FormalSum R X) : ElementaryMove R X s₁ s₂ → ElementaryMove R X ((a, x) :: s₁) ((a, x) :: s₂)
  | swap (a₁ a₂ : R) (x₁ x₂ : X) (tail : FormalSum R X) :
    ElementaryMove R X ((a₁, x₁) :: (a₂, x₂) :: tail) ((a₂, x₂) :: (a₁, x₁) :: tail)

def FreeModuleAux (R X : Type) [Ring R] [DecidableEq R][DecidableEq X] :=
  Quot (ElementaryMove R X)

namespace FormalSum

/-- image in the quotient (i.e., actual, not formal, sum) -/
def sum  (s : FormalSum R X) : FreeModuleAux R X :=
  Quot.mk (ElementaryMove R X) s

/-- equivalence by having the same image -/
def equiv  (s₁ s₂ : FormalSum R X) : Prop :=
  s₁.sum = s₂.sum

infix:65 " ≃ " => FormalSum.equiv

/-- coordinates are invariant under moves -/
theorem coords_move_invariant (x₀ : X) (s₁ s₂ : FormalSum R X) (h : ElementaryMove R X s₁ s₂) : coords s₁ x₀ = coords s₂ x₀ := by
  induction h with
  | zeroCoeff tail x a hyp =>
    simp [coords, hyp, monom_coords_at_zero]
  | addCoeffs a b x tail =>
    simp [coords, monom_coords_at_zero, ← add_assoc, monom_coords_hom]
  | cons a x s₁ s₂ r step =>
    simp [coords, step]
  | swap a₁ a₂ x₁ x₂ tail =>
    simp [coords, ← add_assoc, add_comm]

end FormalSum

/-- coordinates on the quotients-/
def FreeModuleAux.coeff (x₀ : X) : FreeModuleAux R X → R :=
  Quot.lift (fun s => s.coords x₀) (coords_move_invariant  x₀)

namespace FormalSum

/-- commutative diagram for coordinates -/
theorem coeff_factors (x : X) (s : FormalSum R X) : FreeModuleAux.coeff  x (sum s) = s.coords x := by
  simp [FreeModuleAux.coeff]
  apply @Quot.liftBeta (r := ElementaryMove R X) (f := fun s => s.coords x)
  apply coords_move_invariant

/-- coordinates well-defined under the equivalence generated by moves-/
theorem coords_well_defined  (x : X) (s₁ s₂ : FormalSum R X) : s₁ ≃ s₂ → s₁.coords x = s₂.coords x := by
  intro hyp
  have l : FreeModuleAux.coeff x (sum s₂) = s₂.coords x := by
    simp [coeff_factors, hyp]
  rw [← l]
  rw [← coeff_factors]
  rw [hyp]

/-- cons respects equivalence -/
theorem cons_equiv_of_equiv  (s₁ s₂ : FormalSum R X) (a : R) (x : X) : s₁ ≃ s₂ → (a, x) :: s₁ ≃ (a, x) :: s₂ := by
  intro h
  let f : FormalSum R X → FreeModuleAux R X := fun s => sum <| (a, x) :: s
  let wit : (s₁ s₂ : FormalSum R X) → (ElementaryMove R X s₁ s₂) → f s₁ = f s₂ := by
    intro s₁ s₂ hyp
    apply Quot.sound
    apply ElementaryMove.cons
    assumption
  let g := Quot.lift f wit
  let factorizes : (s : FormalSum R X) → g (s.sum) = sum ((a, x) :: s) := Quot.liftBeta f wit
  rw [equiv]
  rw [← factorizes]
  rw [← factorizes]
  rw [h]

/-- if a coordinate `x` for a formal sum `s` is non-zero, `s` is related by moves to a formal sum with first term `x` with coefficient its coordinates, and the rest shorter than `s` -/
theorem nonzero_coeff_has_complement  (x₀ : X)(s : FormalSum R X) : 0 ≠ s.coords x₀ → (∃ ys : FormalSum R X, (((s.coords x₀, x₀) :: ys) ≃ s) ∧ (List.length ys < s.length)) := by
  induction s with
  | nil =>
    intro contra
    contradiction
  | cons head tail hyp =>
    let (a, x) := head
    intro pos
    cases c : x == x₀ with
    | true =>
      let k := FormalSum.coords tail x₀
      have lem : a + k = coords ((a, x) :: tail) x₀ := by
        rw [coords, monomCoeff, c]
      have c'' : x = x₀ := of_decide_eq_true c
      rw [c'']
      rw [c''] at lem
      exact
        if c' : (0 = k) then by
          have lIneq : tail.length < List.length ((a, x) :: tail) := by
            simp [List.length_cons]
          rw [← c', add_zero] at lem
          rw [← lem]
          exact ⟨tail, rfl, lIneq⟩
        else by
          let ⟨ys, eqnStep, lIneqStep⟩ := hyp c'
          have eqn₁ : (a, x₀) :: (k, x₀) :: ys ≃ (a + k, x₀) :: ys := by
            apply Quot.sound
            apply ElementaryMove.addCoeffs
          have eqn₂ : (a, x₀) :: (k, x₀) :: ys ≃ (a, x₀) :: tail := by
            apply cons_equiv_of_equiv
            assumption
          have eqn : (a + k, x₀) :: ys ≃ (a, x₀) :: tail := Eq.trans (Eq.symm eqn₁) eqn₂
          rw [← lem]
          have lIneq : ys.length < List.length ((a, x₀) :: tail) := by
            apply Nat.le_trans lIneqStep
            simp [List.length_cons, Nat.le_succ]
          exact ⟨ys, eqn, lIneq⟩
    | false =>
      let k := coords tail x₀
      have lem : k = coords ((a, x) :: tail) x₀ := by
        simp [coords, monomCoeff, c, zero_add]
      rw [← lem] at pos
      let ⟨ys', eqnStep, lIneqStep⟩ := hyp pos
      rw [← lem]
      let ys := (a, x) :: ys'
      have lIneq : ys.length < ((a, x) :: tail).length := by
        simp [List.length_cons]
        apply Nat.succ_lt_succ
        exact lIneqStep
      have eqn₁ : (k, x₀) :: ys ≃ (a, x) :: (k, x₀) :: ys' := by
        apply Quot.sound
        apply ElementaryMove.swap
      have eqn₂ : (a, x) :: (k, x₀) :: ys' ≃ (a, x) :: tail := by
        apply cons_equiv_of_equiv
        assumption
      have eqn : (k, x₀) :: ys ≃ (a, x) :: tail := by
        exact Eq.trans eqn₁ eqn₂
      exact ⟨ys, eqn, lIneq⟩

/-- if all coordinates are zero, then moves relate to the empty sum -/
theorem equiv_e_of_zero_coeffs  (s : FormalSum R X) (hyp : ∀ x : X, s.coords x = 0) : s ≃ [] :=
  let canc : IsAddLeftCancel R :=
    ⟨fun a b c h => by
      rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]⟩
  match mt : s with
  | [] => rfl
  | h :: t => by
    let (a₀, x₀) := h
    let hyp₀ := hyp x₀
    rw [coords] at hyp₀
    have c₀ : monomCoeff R X x₀ (a₀, x₀) = a₀ := by
      simp [monomCoeff]
    rw [c₀] at hyp₀
    exact
      if hz : a₀ = 0 then by
        rw [hz] at hyp₀
        rw [zero_add] at hyp₀
        have tail_coeffs : ∀ x : X, coords t x = 0 := by
          intro x
          simp [coords]
          exact
            if c : (x₀ = x) then by
              rw [← c]
              assumption
            else by
              let hx := hyp x
              simp [coords, monomCoeff] at hx
              have lf : (x₀ == x) = false := decide_eq_false c
              rw [lf] at hx
              simp [zero_add] at hx
              assumption
        have dec : t.length < (h :: t).length := by
          simp [List.length_cons]
        let step : t ≃ [] := by
          apply equiv_e_of_zero_coeffs
          exact tail_coeffs
        rw [hz]
        have ls : (0, x₀) :: t ≃ t := by
          apply Quot.sound
          apply ElementaryMove.zeroCoeff
          rfl
        exact Eq.trans ls step
      else by
        have non_zero : 0 ≠ coords t x₀ := by
          intro contra'
          let contra := Eq.symm contra'
          rw [contra, add_zero] at hyp₀
          contradiction
        let ⟨ys, eqnStep, lIneqStep⟩ := nonzero_coeff_has_complement x₀ t non_zero
        have tail_coeffs : ∀ x : X, coords ys x = 0 := by
          intro x
          simp [coords]
          exact
            if c : (x₀ = x) then by
              rw [← c]
              let ceq := coords_well_defined x₀ _ _ eqnStep
              simp [coords, monomCoeff] at ceq
              let pad : coords t x₀ = coords t x₀ + 0 := by
                simp [add_zero]
              let ceq' := Eq.trans ceq pad
              let ceq'' := add_left_cancel ceq'
              assumption
            else by
              let hx := hyp x
              simp [coords, monomCoeff] at hx
              have lf : (x₀ == x) = false := decide_eq_false c
              rw [lf] at hx
              simp [zero_add] at hx
              let ceq := coords_well_defined x _ _ eqnStep
              simp [coords, monomCoeff, lf] at ceq
              rw [hx] at ceq
              exact ceq
        have d : ys.length < (h :: t).length := by
          simp [List.length_cons]
          apply Nat.le_trans lIneqStep
          apply Nat.le_succ
        let step : ys ≃ [] := by
          apply equiv_e_of_zero_coeffs
          exact tail_coeffs
        let eqn₁ := cons_equiv_of_equiv _ _ (coords t x₀) x₀ step
        let eqn₂ : t ≃ (coords t x₀, x₀) :: [] := Eq.trans (Eq.symm eqnStep) eqn₁
        let eqn₃ := cons_equiv_of_equiv _ _ a₀ x₀ eqn₂
        apply Eq.trans eqn₃
        have eqn₄ : sum [(a₀, x₀), (coords t x₀, x₀)] = sum [(a₀ + coords t x₀, x₀)] := by
          apply Quot.sound
          apply ElementaryMove.addCoeffs
        apply Eq.trans eqn₄
        rw [hyp₀]
        apply Quot.sound
        apply ElementaryMove.zeroCoeff
        rfl
  termination_by
  _ R X s h => s.length decreasing_by
  assumption

/-- if coordinates are equal, the sums are related by moves -/
theorem equiv_of_equal_coeffs  (s₁ s₂ : FormalSum R X) (hyp : ∀ x : X, s₁.coords x = s₂.coords x) : s₁ ≃ s₂ :=
  let canc : IsAddLeftCancel R :=
    ⟨fun a b c h => by
      rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]⟩
  match mt : s₁ with
  | [] =>
    have coeffs : ∀ x : X, s₂.coords x = 0 := by
      intro x
      let h := hyp x
      rw [← h]
      rfl
    let zl := equiv_e_of_zero_coeffs s₂ coeffs
    Eq.symm zl
  | h :: t =>
    let (a₀, x₀) := h
    by
    exact
      if p : 0 = a₀ then by
        have eq₁ : (a₀, x₀) :: t ≃ t := by
          apply Quot.sound
          apply ElementaryMove.zeroCoeff
          apply Eq.symm
          assumption
        have dec : t.length < (h :: t).length := by
          simp [List.length_cons]
        have eq₂ : t ≃ s₂ := by
          apply equiv_of_equal_coeffs t s₂
          intro x
          let ceq := coords_well_defined x ((a₀, x₀) :: t) t eq₁
          simp [← ceq, hyp]
        exact Eq.trans eq₁ eq₂
      else by
        let a₁ := coords t x₀
        exact
          if p₁ : 0 = a₁ then by
            have cf₂ : s₂.coords x₀ = a₀ := by
              rw [← hyp]
              simp [coords, ← p₁, Nat.add_zero, monomCoeff]
            let ⟨ys, eqn, ineqn⟩ :=
              nonzero_coeff_has_complement x₀ s₂
                (by
                  rw [cf₂]
                  assumption)
            let cfs := fun x => coords_well_defined x _ _ eqn
            rw [cf₂] at cfs
            let cfs' := fun (x : X) => Eq.trans (hyp x) (Eq.symm (cfs x))
            simp [coords] at cfs'
            have dec : t.length < (h :: t).length := by
              simp [List.length_cons]
            let step := equiv_of_equal_coeffs t ys cfs'
            let step' := cons_equiv_of_equiv t ys a₀ x₀ step
            rw [cf₂] at eqn
            exact Eq.trans step' eqn
          else by
            let ⟨ys, eqn, ineqn⟩ := nonzero_coeff_has_complement x₀ t p₁
            let s₃ := (a₀ + a₁, x₀) :: ys
            have eq₁ : (a₀, x₀) :: (a₁, x₀) :: ys ≃ s₃ := by
              apply Quot.sound
              let lem := ElementaryMove.addCoeffs a₀ a₁ x₀ ys
              exact lem
            have eq₂ : (a₀, x₀) :: (a₁, x₀) :: ys ≃ (a₀, x₀) :: t := by
              apply cons_equiv_of_equiv
              assumption
            have eq₃ : s₃ ≃ s₂ := by
              have bd : ys.length + 1 < t.length + 1 := by
                apply Nat.succ_lt_succ
                exact ineqn
              apply equiv_of_equal_coeffs
              intro x
              rw [← hyp x]
              simp [coords]
              let d := coords_well_defined x _ _ eqn
              rw [coords] at d
              rw [← d]
              simp [monom_coords_hom, coords, add_assoc]
            apply Eq.trans (Eq.trans (Eq.symm eq₂) eq₁) eq₃
  termination_by
  _ R X s _ _ => s.length decreasing_by
  assumption

/-- lifting functions to the move induced quotient -/
theorem func_eql_of_move_equiv  {β : Sort u} (f : FormalSum R X → β) : (∀ s₁ s₂ : FormalSum R X, ∀ mv : ElementaryMove R X s₁ s₂, f s₁ = f s₂) → (∀ s₁ s₂ : FormalSum R X, s₁ ≈ s₂ → f s₁ = f s₂) :=
  by
  intro hyp
  let fbar : FreeModuleAux R X → β := Quot.lift f hyp
  let fct : ∀ s : FormalSum R X, f s = fbar (sum s) := by
    apply Quot.liftBeta
    apply hyp
  intro s₁ s₂ sim
  have ec : eqlCoords R X s₁ s₂ := sim
  rw [eqlCoords] at ec
  have pullback : sum s₁ = sum s₂ := by
    apply equiv_of_equal_coeffs
    intro x
    exact congrFun ec x
  simp [fct, pullback]

end FormalSum
end ElementaryMoves

section NormRepr

/-! 
VI. Basic `Repr`

A basic `Repr` on Free Modules, mainly for debugging. This is implemented by constructing a norm ball containing all the non-zero coordinates, and then making a list of non-zero coordinates
-/

theorem fst_le_max (a b : Nat): a ≤ max a b  := by
    simp [max]
    exact if c:b < a 
          then by
              simp [if_pos c]
          else by
              simp [if_neg c]
              apply le_of_not_lt
              assumption
            
theorem snd_le_max (a b : Nat): b ≤ max a b  := by
    simp [max]
    exact if c:b < a 
    then by 
      simp [if_pos c]
      apply le_of_lt
      assumption
    else by 
      simp [if_neg c]

theorem eq_fst_or_snd_of_max (a b : Nat) : (max a b = a) ∨ (max a b = b) := by
      simp [max]
      exact if c:b < a 
        then by
          simp [if_pos c]
        else by
          simp [if_neg c]

def maxNormSuccOnSupp (norm: X → Nat)(crds : X → R)(s: List X) : Nat :=
  match s with
  | [] => 0
  | head :: tail =>
      if crds head ≠ 0 then 
        max (norm head + 1) (maxNormSuccOnSupp norm crds tail)
      else
        maxNormSuccOnSupp norm crds tail        
    
theorem max_in_support (norm: X → Nat)(crds : X → R)(s: List X) : maxNormSuccOnSupp norm crds s > 0 → 
  ∃ x : X, crds x ≠ 0 ∧ maxNormSuccOnSupp norm crds s = norm x + 1 := by
  intro h
  induction s with
  | nil => 
    simp [maxNormSuccOnSupp] at h
  | cons head tail ih => 
    exact if c : crds head =0 then
      by 
        simp [maxNormSuccOnSupp, c]
        simp [maxNormSuccOnSupp, c] at h
        exact  ih h
        
    else by    
        simp [maxNormSuccOnSupp, c]
        simp [maxNormSuccOnSupp, c] at h
        let sl := eq_fst_or_snd_of_max (norm head + 1) (maxNormSuccOnSupp norm crds tail)
        cases sl
        case inr p =>
            rw [p]
            rw [p] at h
            exact  ih h 
        case inl p =>
            rw [p]
            rw [p] at h
            exact ⟨head, And.intro c rfl⟩

theorem supp_below_max(norm: X → Nat)(crds : X → R)(s: List X) : (x: X) → x ∈ s →  crds x ≠ 0 → norm x + 1 ≤ maxNormSuccOnSupp norm crds s := by
    intro x h₁ h₂
    cases h₁
    case head as => 
      rw [maxNormSuccOnSupp]
      simp [h₂]
      apply fst_le_max  
    case tail a as th =>
      rw [maxNormSuccOnSupp]
      let l := supp_below_max norm crds as  x  th h₂ 
      exact if c:crds a ≠ 0 then
        by
        simp [c]
        apply Nat.le_trans l 
        apply snd_le_max
      else
        by 
        simp [c]
        exact l

theorem supp_zero_of_max_zero(norm: X → Nat)(crds : X → R)(s: List X) : maxNormSuccOnSupp norm crds s = 0 → 
    (x: X) → x ∈ s →  crds x = 0 := fun hyp x hm =>
      if c:crds x = 0 then c 
      else by 
        simp
        let l := supp_below_max norm crds s x hm c 
        rw [hyp] at l
        let l' := Nat.zero_lt_succ (norm x)
        contradiction

def FormalSum.normSucc (norm : X → Nat)(s: FormalSum R X) : Nat :=
      maxNormSuccOnSupp norm s.coords (s.support)

open FormalSum
theorem normsucc_le(norm : X → Nat)(s₁ s₂: FormalSum R X)(eql : s₁ ≈ s₂): s₁.normSucc norm ≤ s₂.normSucc norm := 
      if c:s₁.normSucc norm = 0 then 
      by
        rw [c]
        apply Nat.zero_le 
      else by
        simp [FormalSum.normSucc]
        simp [FormalSum.normSucc] at c
        let c' : maxNormSuccOnSupp norm (coords s₁) (support s₁) > 0 :=
            by
            cases Nat.eq_zero_or_pos (maxNormSuccOnSupp norm (coords s₁) (support s₁))
            contradiction
            assumption
        let l := max_in_support norm s₁.coords s₁.support c'
        let ⟨x₀, p⟩:= l
        let nonzr' := p.left
        let l := congrFun eql x₀
        rw [l] at nonzr'
        let nonzr : 0 ≠ s₂.coords x₀ := by
          intro hyp
          let l' := Eq.symm hyp
          contradiction
        let in_supp := nonzero_coord_in_support s₂ x₀ nonzr
        rw [p.right]
        simp
        apply supp_below_max norm s₂.coords s₂.support x₀ in_supp nonzr'

theorem norm_succ_eq(norm : X → Nat)(s₁ s₂: FormalSum R X)(eql : s₁ ≈ s₂):
    s₁.normSucc norm = s₂.normSucc norm := by
      apply Nat.le_antisymm <;> apply normsucc_le
      assumption
      apply eqlCoords.symm
      assumption

class NormCube (α : Type) where
  norm : α → Nat
  cube : Nat → List α

def normCube (α : Type) [nc : NormCube α](k: Nat)  := nc.cube k

instance natCube : NormCube Nat := ⟨id, fun n => (List.range n).reverse⟩

instance finCube {k: Nat} : NormCube (Fin (Nat.succ k)) := 
    let i : Nat → Fin (Nat.succ k) := fun n => ⟨n % (Nat.succ k), by 
          apply Nat.mod_lt
          apply Nat.zero_lt_succ
          ⟩
    ⟨fun j => j.val, fun n => (List.range (min (k + 1) n)).reverse.map i⟩


instance intCube : NormCube ℤ where
  norm := Int.natAbs
  cube : Nat → List ℤ := fun n => 
      (List.range (n)).reverse.map (Int.ofNat) ++
      (List.range (n - 1)).map (Int.negSucc)

instance prodCube {α β : Type} [na: NormCube α] [nb :NormCube β] :  NormCube (α × β) where
  norm : (α × β) → Nat := 
    fun ⟨a, b⟩ => max (na.norm a) (nb.norm b) 
  cube : Nat → List (α × β) :=
    fun n => 
      (na.cube n).bind (fun a => 
        (nb.cube n).map  (fun b => 
          (a, b)))

def FreeModule.normBound (x: FreeModule R X)[nx : NormCube X] : Nat := by
  let f : FormalSum R X → Nat := fun s => s.normSucc (nx.norm)
  apply Quotient.lift f
  apply norm_succ_eq
  exact x

-- this should be viewable directly if `R` and `X` are, as in our case
def FreeModule.coeffList (x: FreeModule R X)[nx : NormCube X] : List (R × X) := 
   (nx.cube (x.normBound)).filterMap fun x₀ => 
      let a := x.coordinates x₀
      if a =0 then none else some (a, x₀)

-- basic repr 
instance basicRepr [nx : NormCube X][Repr X][Repr R]: Repr (FreeModule R X) := 
  ⟨fun x _ => reprStr (x.coeffList)⟩

end NormRepr
