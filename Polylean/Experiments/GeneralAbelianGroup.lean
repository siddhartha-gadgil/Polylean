import Polylean.FreeAbelianGroup

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

def Vector.map (ϕ : T → S) {n : ℕ} : Vector T n → Vector S n
  | nil => nil
  | cons t v => cons (ϕ t) (map ϕ v)

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

instance (n : ℕ) : AddCommGroup (ℤ ^ n) := ℤpowgroup n

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

instance (n : ℕ) : FreeAbelianGroup (ℤ ^ n) (pow_sum Unit n) := ℤpowfreegroup n

def unit_pow_vect {T : Type _} {n : ℕ} (v : Vector T n) : pow_sum Unit n → T :=
  match n with
    | Nat.zero => Empty.rec _
    | Nat.succ m =>
      match v with
        | Vector.cons t v' => λ s => Sum.casesOn s (fun | Unit.unit => t) (unit_pow_vect v')

def induced_map {A : Type _} [AddCommGroup A] {n : ℕ} (v : Vector A n) : ℤ^n → A :=
  FreeAbelianGroup.inducedMap A (unit_pow_vect v)

def zeros : (n : ℕ) → ℤ ^ n
  | Nat.zero => ()
  | Nat.succ n => Prod.mk (0 : ℤ) (zeros n)

def ℤbasis : (n : ℕ) → Vector (ℤ ^ n) n
  | Nat.zero => Vector.nil
  | Nat.succ n => Vector.cons (Prod.mk (1 : ℤ) (zeros n)) (ℤbasis n |>.map (Prod.mk (0 : ℤ) .))

#check @FreeAbelianGroup.induced_extends
#check @FreeAbelianGroup.i
#check @FreeAbelianGroup.induced_hom

@[simp] theorem zero_zero : (n : ℕ) → (0 : ℤ ^ n) = (zeros n)
  | Nat.zero => rfl
  | Nat.succ m => by rw [zeros, ← zero_zero m]; rfl

theorem induced_ext {A : Type _} [AddCommGroup A] (n : ℕ) (v : Vector A n) : (ℤbasis n |>.map (induced_map v)) = v :=
  match n, v with
    | Nat.zero, Vector.nil => rfl
    | Nat.succ m, Vector.cons a v' => by
      let induced_extends := @FreeAbelianGroup.induced_extends (ℤ ^ (Nat.succ m)) _ _ _ _ _ (unit_pow_vect (Vector.cons a v'))
      simp [Vector.map]
      apply And.intro
      · have i_val : @FreeAbelianGroup.i _ _ (Unit ⊕ pow_sum Unit m) _ (Sum.inl ()) = Prod.mk (1 : ℤ) (zeros m) := by simp [FreeAbelianGroup.i, ι]
        rw [← i_val]
        apply congrFun induced_extends (Sum.inl ())
      · sorry

instance ind_hom {A : Type _} [AddCommGroup A] {n : ℕ} (v : Vector A n) : AddCommGroup.Homomorphism (induced_map v) := FreeAbelianGroup.induced_hom A _
