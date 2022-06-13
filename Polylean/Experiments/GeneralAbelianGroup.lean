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

section arrays_lists

theorem List.arraylist {A : Type _} (l : List A) : l.toArray.toList = l := by
  induction l with
    | nil => rfl
    | cons _ _ ih =>
      sorry

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

theorem Array.getfromlist : (l : List T) → (fn : Fin _) → Array.get (l.toArray) fn = l.get ((List.arraysize l) ▸ fn) := sorry

theorem List.maplength {T S : Type _} (ϕ : T → S) : (l : List T) → l.length = (l.map ϕ).length
  | List.nil => rfl
  | List.cons h t => by rw [List.length, List.map, List.length, maplength ϕ t]

theorem List.mapget {T S : Type _} (ϕ : T → S) : (l : List T) → (i : ℕ) → (h : i < List.length l) → ϕ (l.get ⟨i, h⟩) = (l.map ϕ).get ⟨i, Eq.subst (maplength ϕ l) h⟩
  | List.nil, _, h => by contradiction
  | List.cons _ _, Nat.zero, _ => by simp [get, map]
  | List.cons _ t, Nat.succ m, h => by simp [get, map]; rfl

def List.mapcomp (ϕ : T → S) (ψ : S → R) : (l : List T) → List.map ψ (List.map ϕ l) = List.map (ψ ∘ ϕ) l
  | nil => rfl
  | cons _ l' => by simp only [map]; rw [mapcomp _ _ l']; rfl

end arrays_lists

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

def unit_pow_list {T : Type _} {n : ℕ} (l : List T) (h : l.length = n) : pow_sum Unit n → T :=
match n with
  | Nat.zero => Empty.rec _
  | Nat.succ m =>
    match l with
      | List.cons t l' => λ s => Sum.casesOn s (fun | Unit.unit => t) (unit_pow_list l' (by rw [List.length, ← Nat.succ_eq_add_one] at h; injection h; assumption))

def zeros : (n : ℕ) → ℤ ^ n
| Nat.zero => ()
| Nat.succ n => Prod.mk (0 : ℤ) (zeros n)

def ℤbasis : (n : ℕ) → List (ℤ ^ n)
| Nat.zero => List.nil
| Nat.succ n => List.cons (Prod.mk (1 : ℤ) (zeros n)) (ℤbasis n |>.map ι₂)

theorem zero_zero : (n : ℕ) → (0 : ℤ ^ n) = (zeros n)
| Nat.zero => rfl
| Nat.succ m => by rw [zeros, ← zero_zero m]; rfl

end defs

section

def induced_map {A : Type _} [AddCommGroup A] {n : ℕ} (l : List A) (h : l.length = n) : ℤ^n → A :=
FreeAbelianGroup.inducedMap A (unit_pow_list l h)

instance ind_hom {A : Type _} [AddCommGroup A] {n : ℕ} (l : List A) (h : l.length = n) : AddCommGroup.Homomorphism (induced_map l h) := FreeAbelianGroup.induced_hom A _

theorem map_basis {A : Type _} [AddCommGroup A] : {m : ℕ} → (l : List A) → (h : l.length = m) → (List.map (induced_map l h) (ℤbasis m)) = l
| Nat.zero, List.nil, _ => rfl
| Nat.succ m, List.cons t l', h' => by
  simp [List.map]
  apply And.intro
  · have : Prod.mk (1 : ℤ) (zeros m) = (ℤfreegrp (Nat.succ m)).i (Sum.inl () : Unit ⊕ (pow_sum Unit m)) := by
      rw [← zero_zero, FreeAbelianGroup.left_incl]; apply congrArg; rfl
    rw [this]
    apply ( congrFun ((ℤfreegrp (Nat.succ m)).induced_extends (unit_pow_list (List.cons t l') h')) (Sum.inl ()) )
  · have h'' := h'
    rw [List.length, Nat.add_one, Nat.succ_inj'] at h''
    have ih := map_basis l' h''
    have ind_cons : induced_map (t :: l') h' ∘ ι₂ = induced_map l' h'' := by
      rw [induced_map, induced_map]
      have : (unit_pow_list l' h'') = (unit_pow_list (List.cons t l') h') ∘ Sum.inr := by apply funext; intro; simp [unit_pow_list]
      rw [this, FreeAbelianGroup.induced_right]
    rw [ind_cons]
    exact ih

end


section AddTreeGroup

variable (t : IndexAddTree)
variable {A : Type _} [AddCommGroup A] [Repr A]
variable {n : ℕ} (l : List A) (h : l.length = n) (hpos : n > 0) -- basisImages

instance prodrepr (A B : Type _) [Repr A] [Repr B] : Repr (A × B) := inferInstance

def ℤprodrepr : (n : ℕ) → Repr (ℤ ^ n)
    | Nat.zero => inferInstanceAs (Repr Unit)
    | Nat.succ m => @prodrepr ℤ (ℤ ^ m) _ (ℤprodrepr m)

instance (n : ℕ) : Repr (ℤ ^ n) := ℤprodrepr n

lemma larrlengthpos : Array.size (List.toArray l) > 0 := by
  rw [GT.gt, List.arraysize, h]
  exact hpos

lemma ℤbasisarrlengthpos : Array.size (List.toArray (ℤbasis n)) > 0 := by
  rw [GT.gt, List.arraysize]
  let rec ℤbasislen : ∀ m : ℕ, List.length (ℤbasis m) = m
    | Nat.zero => rfl
    | Nat.succ m' => by rw [ℤbasis, List.length, Nat.add_one, ← List.maplength, ℤbasislen m']
  rw [ℤbasislen]
  assumption

theorem IndexAddTree.trees_consistent : IndexAddTree.foldMap t l.toArray (larrlengthpos l h hpos) =
                         (induced_map l h) (IndexAddTree.foldMap t (ℤbasis n).toArray (ℤbasisarrlengthpos hpos)) := by
  induction t with
    | leaf a =>
      simp [foldMap]
      rw [Array.getfromlist, Array.getfromlist, List.mapget (induced_map l h)]
      have := map_basis l h
      -- rw [this]
      -- apply congrArg
      sorry
    | negLeaf a =>
      simp [foldMap]
      apply congrArg
      rw [Array.getfromlist, Array.getfromlist, List.mapget (induced_map l h)]
      have := map_basis l h
      simp [this]
      sorry
    | node _ _ ihl ihr => simp [ihl, ihr, foldMap]
    | subNode _ _ ihl ihr => simp [ihl, ihr, foldMap]

end AddTreeGroup

/-
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
-/
