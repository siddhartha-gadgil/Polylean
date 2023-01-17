import Polylean.FreeAbelianGroup
import Experiments.AddTree

section ArraysAndLists

-- a lemma about the `toArrayAux` function needed for the next theorem
lemma List.aux_append {α : Type _} (l : List α) : ∀ l' : List α, List.toArrayAux l {data := l'} = {data := l' ++ l} := by
  induction l with
    | nil =>
      intro
      simp [toArrayAux]
    | cons h t ih =>
      intro l'
      simp [toArrayAux, Array.push, concat]
      rw [ih (concat l' h)]
      simp
      let rec concat_append (a : α) (l₁ : List α) (l₂ : List α) : concat l₁ a ++ l₂ = l₁ ++ (a :: l₂)  := by
        induction l₁ with
          | nil => simp [concat]
          | cons h t ih => simp [concat]; assumption
      apply concat_append

-- converting a list to an array and then extracting the data preserves the list
@[simp] theorem List.arraydata {A : Type _} (l : List A) : l.toArray.data = l := by
  rw [toArray, Array.mkEmpty, List.aux_append]
  simp

-- the size of a list is preserved when coverted to an array and back
@[simp] theorem List.arraysize {α : Type _} (l : List α) : l.toArray.size = l.length := by
  rw [Array.size, arraydata]

-- a helper lemma for solving rewriting issues with `Fin`
theorem List.get_index_eq : {l l' : List α} → (hl : l = l') → (i : ℕ) → (bnd : i < l.length) → l.get ⟨i, bnd⟩ = l'.get ⟨i, hl ▸ bnd⟩
  | _, _, rfl, _, _ => rfl

-- getting the `i`th element of an array is the same as getting the `i`th element of the corresponding list
@[simp] theorem Array.getfromlist : (l : List T)  → (i : ℕ) → (h : i < l.length) → Array.get (l.toArray) ⟨i, Eq.substr l.arraysize h⟩ = l.get ⟨i, h⟩
  | List.nil, _, h => by contradiction
  | List.cons hd tl, Nat.zero, _ => by rw [get, List.get_index_eq (List.arraydata (hd :: tl)), List.get]
  | List.cons _ _, Nat.succ m, h => by rw [get, List.get_index_eq (List.arraydata _), List.get]

theorem List.maplength {T S : Type _} (ϕ : T → S) : (l : List T) → l.length = (l.map ϕ).length
  | List.nil => rfl
  | List.cons h t => by rw [List.length, List.map, List.length, maplength ϕ t]

-- the value of a function `ϕ` on the `i`th element of a list `l` is the same as the value of the `i`th element of the list `map ϕ l`
theorem List.mapget {T S : Type _} (ϕ : T → S) : (l : List T) → (i : ℕ) → (h : i < List.length l) → ϕ (l.get ⟨i, h⟩) = (l.map ϕ).get ⟨i, Eq.subst (maplength ϕ l) h⟩
  | List.nil, _, _ => by contradiction
  | List.cons _ _, Nat.zero, _ => by simp [get, map]
  | List.cons _ _, Nat.succ _, _ => by simp [get, map]; rfl

def List.mapcomp (ϕ : T → S) (ψ : S → R) : (l : List T) → List.map ψ (List.map ϕ l) = List.map (ψ ∘ ϕ) l
  | nil => rfl
  | cons _ l' => by simp only [map]; rw [mapcomp _ _ l']; rfl

theorem List.cons_len_eq_succ : List.length (h :: tl) = Nat.succ m → List.length tl = m := by
  intro hyp
  rw [length, ← Nat.succ_eq_add_one] at hyp
  injection hyp
  assumption

-- replaced the `foldl` definition
def List.sum {α : Type _} [Add α] [Zero α] : List α → α
  | [] => 0
  | h :: t => h + sum t

end ArraysAndLists

section Defs

-- iterated product
def pow_times (T : Type _) : ℕ → Type _
  | Nat.zero => Unit
  | Nat.succ n => T × (pow_times T n)

instance : Pow (Type _) ℕ where
    pow := pow_times

-- iterated direct sums
def pow_sum (T : Type _) : ℕ → Type _
  | Nat.zero => Empty
  | Nat.succ n => T ⊕ (pow_sum T n)

def zipWith {α β γ : Type _} (ϕ : α → β → γ) : {n : ℕ} → α ^ n → (l : List β) → (l.length = n) → List γ
  | .zero, .(Unit.unit), .([]), rfl => []
  | .succ _, (a, as), b :: bs, h => (ϕ a b) :: (zipWith ϕ as bs $ List.cons_len_eq_succ h)

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

-- ℤ^n is a group
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

-- ℤ^n is a free Abelian group
instance ℤfreegrp (n : ℕ) : FreeAbelianGroup (ℤ ^ n) (pow_sum Unit n) := ℤpowfreegroup n

instance (n : ℕ) : FreeAbelianGroup (pow_times ℤ n) (pow_sum Unit n) := ℤpowfreegroup n

-- takes a list of values in `T` of length `n` and returns a function from `Unit ⊕ Unit ⊕ ... n times ... ⊕ Unit → T`
-- mapping the elements of `pow_sum Unit n` to the corresponding elements of `T` in order
def unitBasisMap {T : Type _} : {n : ℕ} → (l : List T) → (l.length = n) → pow_sum Unit n → T
  | Nat.zero, .([]), .(rfl) => Empty.rec _
  | Nat.succ _, List.cons t l', h =>
             λ s => Sum.casesOn s
                  (fun | Unit.unit => t)
                  (unitBasisMap l' $ List.cons_len_eq_succ h)

def zeros : (n : ℕ) → ℤ ^ n
| Nat.zero => ()
| Nat.succ n => Prod.mk (0 : ℤ) (zeros n)

-- returns a basis of `ℤ^n`
def ℤbasis : (n : ℕ) → List (ℤ ^ n)
| Nat.zero => List.nil
| Nat.succ n => List.cons (Prod.mk (1 : ℤ) (zeros n)) (ℤbasis n |>.map ι₂)

@[simp] def ℤbasislen : ∀ m : ℕ, List.length (ℤbasis m) = m
    | Nat.zero => rfl
    | Nat.succ m' => by rw [ℤbasis, List.length, Nat.add_one, ← List.maplength, ℤbasislen m']

theorem zero_zero : (n : ℕ) → (0 : ℤ ^ n) = (zeros n)
| Nat.zero => rfl
| Nat.succ m => by rw [zeros, ← zero_zero m]; rfl


end Defs


section InducedFreeMap

-- the unique map `ϕ : ℤ^n → A` taking the basis elements to the given list of values `l`
def inducedFreeMap {A : Type _} [AddCommGroup A] {n : ℕ} (l : List A) (h : l.length = n) : ℤ^n → A :=
FreeAbelianGroup.inducedMap A (unitBasisMap l h)

-- the above map is a group homomorphism
instance ind_hom {A : Type _} [AddCommGroup A] {n : ℕ} (l : List A) (h : l.length = n) : AddCommGroup.Homomorphism (inducedFreeMap l h) := FreeAbelianGroup.induced_hom A _

-- a normal form for images of free group elements
theorem map_free_elem {A : Type _} [AddCommGroup A] : {m : ℕ} → (l : List A) → (h : l.length = m) → (x : ℤ ^ m) → (inducedFreeMap l h) x = (List.sum $ zipWith SubNegMonoid.gsmul x l h)
  | .zero, .([]), .(rfl), .(Unit.unit) => rfl
  | .succ m', a :: as, h, (x, xs) => by
      rw [inducedFreeMap, unitBasisMap, FreeAbelianGroup.inducedMap, ℤfreegrp, ℤpowfreegroup, prodFree]
      simp only [inducedProdMap]
      rw [FreeAbelianGroup.inducedMap, intFree]
      simp only [zhom, Function.comp]
      let ih := map_free_elem as (List.cons_len_eq_succ h) xs
      rw [inducedFreeMap] at ih
      rw [ih, zipWith, List.sum]

-- a proof that the above map takes the basis elements to the elements in the list
theorem map_basis {A : Type _} [AddCommGroup A] : {m : ℕ} → (l : List A) → (h : l.length = m) → (List.map (inducedFreeMap l h) (ℤbasis m)) = l
  | .zero, .([]), .(rfl) => rfl
  | .succ m, .cons a l', h => by
    rw [ℤbasis, List.map, map_free_elem, zipWith, List.sum, List.mapcomp]
    let rec zero_zip_sum : (n : ℕ) → (l : List A) → (hyp : l.length = n) → (List.sum <| zipWith SubNegMonoid.gsmul (zeros n) l hyp) = (0 : A)
      | .zero, .([]), .(rfl) => rfl
      | .succ m, a :: l', hyp => by rw [zeros, zipWith, List.sum, SubNegMonoid.gsmul_zero', zero_zip_sum m, add_zero]
    have ind_cons : inducedFreeMap (a :: l') h ∘ ι₂ = inducedFreeMap l' _ := by
      rw [inducedFreeMap, inducedFreeMap]
      have : (unitBasisMap l' $ List.cons_len_eq_succ h) = (unitBasisMap (List.cons a l') h) ∘ Sum.inr := by apply funext; intro; simp [unitBasisMap]
      rw [this, FreeAbelianGroup.induced_right]
    rw [zero_zip_sum, ind_cons, add_zero, map_basis, SubNegMonoid.gsmul_one]

end InducedFreeMap


section AddTreeGroup

variable (t : IndexAddTree)
variable {A : Type _} [AddCommGroup A] [Repr A]
variable {n : ℕ} (l : List A) (h : l.length = n) (hpos : n > 0) -- basisImages

-- a few helper results and lemmas

instance prodrepr (A B : Type _) [Repr A] [Repr B] : Repr (A × B) := inferInstance

def ℤprodrepr : (n : ℕ) → Repr (ℤ ^ n)
    | Nat.zero => inferInstanceAs (Repr Unit)
    | Nat.succ m => @prodrepr ℤ (ℤ ^ m) _ (ℤprodrepr m)

instance (n : ℕ) : Repr (ℤ ^ n) := ℤprodrepr n

-- some useful lemmas to deal with theorems about `Fin`
lemma Fin.eq_of_eq_of_Nat' : {i m n : ℕ} → (h : m = n) → (hm : m > 0) → Fin.val (Fin.ofNat' i hm) = Fin.val (Fin.ofNat' i (h ▸ hm))
  | _, _, _, rfl, _ => rfl

lemma Fin.eq_val_bound : {m n : ℕ} → {f : Fin m} → (m = n) → (f.val < n)
  | _, _, ⟨_, prf⟩, rfl => prf


-- taking an abstract tree to a given list of `n` elements of group `A` is equivalent to
-- first taking it to the basis of `ℤ^n` and then apply the `inducedFreeMap`
theorem IndexAddTree.fold_tree_freegroup_eq : IndexAddTree.foldMap t l.toArray (by simp [h, hpos]) =
                         (inducedFreeMap l h) (IndexAddTree.foldMap t (ℤbasis n).toArray (by simp [hpos])) := by
  induction t with
    | leaf _ =>
        simp [foldMap]
        rw [Array.getfromlist, Array.getfromlist, List.mapget (inducedFreeMap l h), List.get_index_eq (map_basis l h)]
        apply congrArg
        apply Fin.eq_of_val_eq; simp
        subst h
        apply Fin.eq_of_eq_of_Nat'; simp
        all_goals (apply Fin.eq_val_bound; simp)
    | negLeaf _ =>
        simp [foldMap]
        apply congrArg
        rw [Array.getfromlist, Array.getfromlist, List.mapget (inducedFreeMap l h), List.get_index_eq (map_basis l h)]
        apply congrArg
        apply Fin.eq_of_val_eq; simp
        subst h
        apply Fin.eq_of_eq_of_Nat'; simp
        all_goals (apply Fin.eq_val_bound; simp)
    | node _ _ ihl ihr => simp [ihl, ihr, foldMap]
    | subNode _ _ ihl ihr => simp [ihl, ihr, foldMap]

end AddTreeGroup



/-

section FormalExample

abbrev n : ℕ := 3

open List in
def ν {A : Type _} [AddCommGroup A] (l : List A) (h : l.length = n) : Prop :=
    match l, h with
      | (cons x (cons y (cons z nil))), rfl => x + (y - z) + z - x = y

theorem valid_iff_free_basis : (∀ {A : Type} [AddCommGroup A], ∀ (l : List A) (h : l.length = n), ν l h) ↔ (ν (ℤbasis n) (ℤbasislen n)) := by
  apply Iff.intro
  · intro hyp
    exact hyp (ℤbasis n) (ℤbasislen n)
  · intro hyp
    intro A _ l h
    let ϕ := inducedFreeMap l rfl
    have basismap := map_basis l rfl
    sorry
    /-
    match l, h with
      | List.cons a (List.cons b (List.cons c List.nil)), rfl =>
        simp [ν, ℤbasis] at hyp
        have ϕmap := congrArg ϕ hyp
        simp at ϕmap
        simp only [ι₁, ι₂, zeros] at ϕmap
        simp [List.map, ℤbasis, ι₁, ι₂, zeros, unit_pow_list, h, map_basis] at basismap
        let ⟨ha, hb, hc⟩ := basismap
        simp [ha, hb, hc] at ϕmap
    -/

theorem eqn_valid {A : Type} [AddCommGroup A] : ∀ (l : List A) (h : l.length = n), ν l h :=
  (Iff.mpr valid_iff_free_basis) rfl

end FormalExample

-/
