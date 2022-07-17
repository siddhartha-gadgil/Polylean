import Polylean.FreeAbelianGroup
import Polylean.Experiments.Vector

section FreeGroupPow

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


def zipWith {α β γ : Type _} (ϕ : α → β → γ) : {n : ℕ} → α ^ n → Vector β n → Vector γ n
  | .zero, .(Unit.unit), _ => .nil
  | .succ _, (a, as), .cons b bs => .cons (ϕ a b) (zipWith ϕ as bs)

abbrev Vector.sum {α : Type _} [Add α] [Zero α] : Vector α n → α := Vector.foldr (· + ·) 0


@[instance] def ℤpowgroup : (n : ℕ) → AddCommGroup (ℤ ^ n)
    | Nat.zero => inferInstanceAs (AddCommGroup Unit)
    | Nat.succ n => @DirectSum.directSum ℤ (pow_times ℤ n) _ (ℤpowgroup n)

instance (n : ℕ) : AddCommGroup (pow_times ℤ n) := inferInstanceAs (AddCommGroup (ℤ ^ n))

@[instance] def ℤpowfreegroup (n : ℕ) : FreeAbelianGroup (ℤ ^ n) (pow_sum Unit n)  :=
match n with
  | .zero => inferInstanceAs (FreeAbelianGroup Unit Empty)
  | .succ n => @prodFree _ _ _ (inferInstanceAs (AddCommGroup (ℤ ^ n))) _ _ _ (ℤpowfreegroup n)

instance (n : ℕ) : FreeAbelianGroup (pow_times ℤ n) (pow_sum Unit n) := ℤpowfreegroup n


-- takes a list of values in `T` of length `n` and returns a function from `Unit ⊕ Unit ⊕ ... n times ... ⊕ Unit → T`
-- mapping the elements of `pow_sum Unit n` to the corresponding elements of `T` in order
def unitBasisMap {α : Type _} : {n : ℕ} → Vector α n → pow_sum Unit n → α
  | Nat.zero, .nil => Empty.rec _
  | Nat.succ _, .cons a v => λ s => Sum.casesOn s (fun | Unit.unit => a) (unitBasisMap v)

def zeros : (n : ℕ) → ℤ ^ n
| .zero => ()
| .succ n => Prod.mk (0 : ℤ) (zeros n)

-- returns a basis of `ℤ^n`
def ℤbasis : (n : ℕ) → Vector (ℤ ^ n) n
| .zero => .nil
| .succ n => .cons (Prod.mk (1 : ℤ) (zeros n)) (ℤbasis n |>.map ι₂)

end FreeGroupPow


section InducedFreeMap

-- the unique map `ϕ : ℤ^n → A` taking the basis elements to the given list of values `l`
def inducedFreeMap {A : Type _} [AddCommGroup A] {n : ℕ} (v : Vector A n) : ℤ^n → A :=
  FreeAbelianGroup.inducedMap A (unitBasisMap v)

-- the above map is a group homomorphism
instance ind_hom {A : Type _} [AddCommGroup A] {n : ℕ} (v : Vector A n) : AddCommGroup.Homomorphism (inducedFreeMap v) := FreeAbelianGroup.induced_hom A _

-- a normal form for images of free group elements
theorem map_free_elem {A : Type _} [AddCommGroup A] : {m : ℕ} → (v : Vector A m) → (x : ℤ ^ m) → (inducedFreeMap v) x = (zipWith SubNegMonoid.gsmul x v |>.sum)
  | .zero, .nil, .(Unit.unit) => rfl
  | .succ m', .cons a as, (x, xs) => by
      rw [inducedFreeMap, unitBasisMap, FreeAbelianGroup.inducedMap, ℤpowfreegroup, prodFree]
      simp only [inducedProdMap]
      rw [FreeAbelianGroup.inducedMap, intFree]
      simp only [zhom, Function.comp]
      let ih := map_free_elem as xs
      rw [inducedFreeMap] at ih
      rw [ih, zipWith, Vector.sum, Vector.sum, Vector.foldr]

-- a proof that the above map takes the basis elements to the elements in the list
theorem map_basis {A : Type _} [AddCommGroup A] : {m : ℕ} → (v : Vector A m) → (ℤbasis m |>.map (inducedFreeMap v)) = v
  | .zero, .nil => rfl
  | .succ m, .cons a v => by
    rw [ℤbasis, Vector.map, map_free_elem, zipWith, Vector.sum, Vector.foldr, Vector.map_comp]
    let rec zero_zip_sum : (n : Nat) → (v : Vector A n) → (zipWith SubNegMonoid.gsmul (zeros n) v |>.foldr (· + ·) 0) = (0 : A)
      | .zero, .nil => rfl
      | .succ m, .cons a v' => by rw [zeros, zipWith, Vector.foldr, SubNegMonoid.gsmul_zero', zero_add]; apply zero_zip_sum
    have ind_cons : inducedFreeMap (.cons a v) ∘ ι₂ = inducedFreeMap v := by
      rw [inducedFreeMap, inducedFreeMap]
      have : (unitBasisMap v) = (unitBasisMap (.cons a v)) ∘ Sum.inr := by apply funext; intro; simp [unitBasisMap]
      rw [this, FreeAbelianGroup.induced_right]
    rw [zero_zip_sum, ind_cons, add_zero, map_basis, SubNegMonoid.gsmul_one]

end InducedFreeMap
