import Polylean.FreeAbelianGroup
import Polylean.Experiments.AddTree

section defs

def pow_times (T : Type _) : ℕ → Type _
  | Nat.zero => Unit
  | Nat.succ n => T × (pow_times T n)

instance : Pow (Type _) ℕ where
    pow := pow_times

def pow_sum (T : Type _) : ℕ → Type _
  | Nat.zero => Empty
  | Nat.succ n => T ⊕ (pow_sum T n)

inductive Vector (T : Type _) : ℕ → Type
  | nil : Vector T Nat.zero
  | cons : T → {n : ℕ} → Vector T n → Vector T (Nat.succ n)

def Vector.map (ϕ : T → S) : Vector T n → Vector S n
  | nil => nil
  | cons t v => cons (ϕ t) (map ϕ v)

def Vector.get : Vector T n → Fin n → T
  | Vector.cons a _, ⟨Nat.zero, _⟩ => a
  | Vector.cons _ as, ⟨Nat.succ m, h⟩ => get as ⟨m, Nat.le_of_succ_le_succ h⟩

theorem Vector.get_map (f : T → S) (v : Vector T n) (fn : Fin n) : f (v.get fn) = (v.map f).get fn := by
  induction v with
    | nil => cases fn; contradiction
    | cons a v' ih =>
      match fn with
        | ⟨Nat.zero, _⟩ => rw [get, map, get]
        | ⟨Nat.succ m, _⟩ => rw [get, map, get, ih]

def Vector.toList {A : Type _} {n : ℕ} : Vector A n → List A
  | Vector.nil => List.nil
  | Vector.cons a v' => List.cons a (toList v')

def Vector.toArray {A : Type _} {n : ℕ} : Vector A n → Array A :=
  λ v => v.toList.toArray

theorem Vector.listlength {A : Type _} {n : ℕ} (v : Vector A n) : v.toList.length = n := by
  induction v with
    | nil => rfl
    | cons _ _ ih => rw [toList, List.length, ih]

theorem List.arraylist {A : Type _} (l : List A) : l.toArray.toList = l := by
  induction l with
    | nil => rfl
    | cons _ _ ih =>
      sorry
      -- simp [toArray, toArrayAux, Array.mkEmpty, Array.push, concat]
      -- simp [toArray, Array.mkEmpty] at ih

theorem Array.dataarray {A : Type _} (a : Array A) : a.data.toArray = a := by
  sorry

theorem List.arraydata {A : Type _} (l : List A) : l.toArray.data = l := sorry

theorem Array.listarray {A : Type _} (a : Array A) : a.toList.toArray = a := by
  match a with
    | ⟨l⟩ =>
      -- apply congrArg Array.mk
      induction l with
        | nil => rfl
        | cons _ _ ih =>
          -- [toList, foldr]
          sorry


theorem List.arraysize {A: Type _} (l : List A) : l.toArray.size = l.length := by
  rw [Array.size, arraydata]

theorem Vector.arraysize {A : Type _} {n : ℕ} (v : Vector A n) : v.toArray.size = n := by
  rw [toArray, List.arraysize, listlength]

theorem Array.getfromvector (v : Vector A n) (fn : Fin _) : Array.get (v.toArray) fn = v.get ((Vector.arraysize v) ▸ fn) := by
  induction v with
    | nil => cases fn; contradiction
    | cons a v' ih =>
      simp [Vector.toArray, Array.get]
      have := List.arraydata (Vector.toList (Vector.cons a v'))
      sorry

theorem Vector.mapcomp (ϕ : T → S) (ψ : S → R) {n : ℕ} : (v : Vector T n) → Vector.map ψ (Vector.map ϕ v) = Vector.map (ψ ∘ ϕ) v
  | nil => rfl
  | cons t v' => by simp only [map]; rw [mapcomp _ _ v']; rfl

instance : AddCommGroup Unit :=
  {
    add := λ _ _ => Unit.unit
    add_assoc := λ _ _ _ => rfl
    zero := Unit.unit
    add_zero := λ _ => rfl
    zero_add := λ _ => rfl
    nsmul_zero' := by intros; rfl
    nsmul_succ' := by intros; rfl
    neg := λ _ => Unit.unit
    sub_eq_add_neg := by intros; rfl
    gsmul_zero' := by intros; rfl
    gsmul_succ' := by intros; rfl
    gsmul_neg' := by intros; rfl
    add_left_neg := λ _ => rfl
    add_comm := λ _ _ => rfl
  }

def ℤpowgroup : (n : ℕ) → AddCommGroup (ℤ ^ n)
    | Nat.zero => inferInstanceAs (AddCommGroup Unit)
    | Nat.succ n => @DirectSum.directSum ℤ (pow_times ℤ n) _ (ℤpowgroup n)

instance ℤgrp (n : ℕ) : AddCommGroup (ℤ ^ n) := ℤpowgroup n

instance (n : ℕ) : AddCommGroup (pow_times ℤ n) := ℤpowgroup n

instance : FreeAbelianGroup Unit Empty :=
{
  i := Empty.rec _
  inducedMap := λ A _ _ _ => (0 : A)
  induced_extends := λ _ => funext (Empty.rec _)
  induced_hom := λ _ _ _ => {add_dist := fun | Unit.unit, Unit.unit => by simp}
  unique_extension := λ _ _ _ _ _ => funext (fun | Unit.unit => by simp)
}

def ℤpowfreegroup (n : ℕ) : FreeAbelianGroup (ℤ ^ n) (pow_sum Unit n)  :=
match n with
  | Nat.zero => inferInstanceAs (FreeAbelianGroup Unit Empty)
  | Nat.succ n => @prodFree _ _ _ (inferInstanceAs (AddCommGroup (ℤ ^ n))) _ _ _ (ℤpowfreegroup n)

instance ℤfreegrp (n : ℕ) : FreeAbelianGroup (ℤ ^ n) (pow_sum Unit n) := ℤpowfreegroup n

instance (n : ℕ) : FreeAbelianGroup (pow_times ℤ n) (pow_sum Unit n) := ℤpowfreegroup n

def unit_pow_vect {T : Type _} {n : ℕ} (v : Vector T n) : pow_sum Unit n → T :=
match n with
  | Nat.zero => Empty.rec _
  | Nat.succ m =>
    match v with
      | Vector.cons t v' => λ s => Sum.casesOn s (fun | Unit.unit => t) (unit_pow_vect v')

def zeros : (n : ℕ) → ℤ ^ n
| Nat.zero => ()
| Nat.succ n => Prod.mk (0 : ℤ) (zeros n)

def ℤbasis : (n : ℕ) → Vector (ℤ ^ n) n
| Nat.zero => Vector.nil
| Nat.succ n => Vector.cons (Prod.mk (1 : ℤ) (zeros n)) (ℤbasis n |>.map ι₂)

theorem zero_zero : (n : ℕ) → (0 : ℤ ^ n) = (zeros n)
| Nat.zero => rfl
| Nat.succ m => by rw [zeros, ← zero_zero m]; rfl

end defs

section

def induced_map {A : Type _} [AddCommGroup A] {n : ℕ} (v : Vector A n) : ℤ^n → A :=
FreeAbelianGroup.inducedMap A (unit_pow_vect v)

instance ind_hom {A : Type _} [AddCommGroup A] {n : ℕ} (v : Vector A n) : AddCommGroup.Homomorphism (induced_map v) := FreeAbelianGroup.induced_hom A _

theorem map_basis {A : Type _} [AddCommGroup A] : {m : ℕ} → (v : Vector A m) → (Vector.map (FreeAbelianGroup.inducedMap A (unit_pow_vect v)) (ℤbasis m)) = v
| _, Vector.nil => rfl
| Nat.succ m, Vector.cons t v' => by
  simp [Vector.map]
  apply And.intro
  · have : Prod.mk (1 : ℤ) (zeros m) = (ℤfreegrp (Nat.succ m)).i (Sum.inl () : Unit ⊕ (pow_sum Unit m)) := by
      rw [← zero_zero, FreeAbelianGroup.left_incl]; apply congrArg; rfl
    rw [this]
    apply ( congrFun ((ℤfreegrp (Nat.succ m)).induced_extends (unit_pow_vect (Vector.cons t v'))) (Sum.inl ()) )
  · have ih := map_basis v'
    rw [Vector.mapcomp, ← ih]
    apply congrFun
    apply congrArg
    have : unit_pow_vect v' = (unit_pow_vect (Vector.cons t v')) ∘ Sum.inr := by apply funext; intro; simp [unit_pow_vect]
    rw [ih, this, FreeAbelianGroup.induced_right]

end

-- adding here for the timebeing to avoid breaking the rest of the code
@[simp] theorem AddCommGroup.Homomorphism.neg_dist {A B : Type _} [AddCommGroup A] [AddCommGroup B] (ϕ : A → B) [AddCommGroup.Homomorphism ϕ]
  : ∀ a a' : A, ϕ (a - a') = ϕ a - ϕ a' := by
  intros
  repeat (rw [sub_eq_add_neg])
  simp

section AddTreeGroup

variable (t : IndexAddTree)
variable {A : Type _} [AddCommGroup A] [Repr A]
variable {n : ℕ} (v : Vector A (n.succ)) -- basisImages

instance prodrepr (A B : Type _) [Repr A] [Repr B] : Repr (A × B) := inferInstance

def ℤprodrepr : (n : ℕ) → Repr (ℤ ^ n)
    | Nat.zero => inferInstanceAs (Repr Unit)
    | Nat.succ m => @prodrepr ℤ (ℤ ^ m) _ (ℤprodrepr m)

instance (n : ℕ) : Repr (ℤ ^ n) := ℤprodrepr n

def vectsizepos {α : Type _} {m : ℕ} (w : Vector α m.succ) : w.toArray.size > 0 := by
  rw [GT.gt]
  apply Eq.substr (Vector.arraysize w)
  apply Nat.zero_lt_succ

theorem IndexAddTree.trees_consistent : IndexAddTree.foldMap t v.toArray (vectsizepos v) =
                         (induced_map v) (IndexAddTree.foldMap t (ℤbasis n.succ).toArray (vectsizepos _)) := by
  induction t with
    | leaf a =>
      simp [foldMap]
      rw [Array.getfromvector, Array.getfromvector, Vector.get_map (induced_map v), induced_map, map_basis]
      apply congrArg
      sorry
    | negLeaf a =>
      simp [foldMap]
      rw [Array.getfromvector, Array.getfromvector, Vector.get_map (induced_map v), induced_map, map_basis]
      apply congrArg
      sorry
    | node _ _ ihl ihr => simp [ihl, ihr, foldMap]
    | subNode _ _ ihl ihr => simp [ihl, ihr, foldMap]

#check Array.get
#print Fin.ofNat'
#check Vector.get_map

end AddTreeGroup


section formalexample

def n : ℕ := 3

open Vector in
def ν {A : Type _} [AddCommGroup A] (v : Vector A n) :=
    match v with
      | cons x (cons y (cons z nil)) => x + (y - z) + z - x = y

theorem valid_iff_free_basis : (∀ {A : Type _} [AddCommGroup A], ∀ v : Vector A n, ν v) ↔ (ν (ℤbasis n)) := by
  apply Iff.intro
  · intro h
    apply h
  · intro h
    intro A _ v
    have ϕ := induced_map v
    have := congrArg ϕ h
    simp only [ι₁, ι₂, zeros] at this
    simp only [AddCommGroup.Homomorphism.add_dist] at this
    sorry

theorem eqn_valid {A : Type _} [AddCommGroup A] : ∀ v : Vector A n, ν v :=
  (Iff.mpr valid_iff_free_basis) rfl

end formalexample
