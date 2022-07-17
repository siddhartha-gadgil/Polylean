inductive Vector (α : Type _) : Nat → Type _
  | nil : Vector α .zero
  | cons : {n : Nat} → α → Vector α n → Vector α n.succ

/-
infixr:120 " ∣ " => Vector.cons
notation " % " => Vector.nil
#check 2 ∣ 3 ∣ 5 ∣ %
-/

def Vector.map (f : α → β) : Vector α n → Vector β n
  | nil => nil
  | cons a v => cons (f a) (map f v)

def Vector.foldl (f : α → β → α) (a : α) : Vector β n → α
  | nil => a
  | cons b v => foldl f (f a b) v

def Vector.foldr (f : β → α → α) (a : α) : Vector β n → α
  | nil => a
  | cons b v => f b (foldr f a v)

def Vector.get : Vector α n → (i : Nat) → (i < n) → α
  | nil, _, _ => by contradiction
  | cons a _, .zero, _ => a
  | cons _ v, .succ j, h => get v j $ Nat.lt_of_succ_lt_succ h

def Vector.get! [Inhabited α] : Vector α n → (i : Nat) → α
  | nil, _ => panic! "Out of bounds"
  | cons a _, .zero => a
  | cons _ v, .succ j => get! v j

theorem Vector.map_comp (ϕ : α → β) (ψ : β → γ) : ∀ v : Vector α n, (v |>.map ϕ |>.map ψ) = (v |>.map (ψ ∘ ϕ))
  | nil => rfl
  | cons a v => by rw [map, map, map, map_comp]; rfl

theorem Vector.map_get (ϕ : α → β) : ∀ v : Vector α n, ∀ i : Nat, ∀ (h : i < n), ϕ (v.get i h) = (v |>.map ϕ |>.get i h)
  | nil, _, _ => by contradiction
  | cons _ _, .zero, _ => by rw [get, map, get]
  | cons _ _, .succ _, _ => by rw [get, map, get]; apply map_get

theorem Vector.get_index_eq {v v' : Vector α n} : v = v' → (k : Nat) → (hk : k < n) → v.get k hk = v'.get k hk
  | rfl, _, _ => rfl

theorem Vector.get!_of_get [Inhabited α] : (k : Nat) → (v : Vector α n) → (hk : k < n) → v.get! k = v.get k hk
  | _, .nil, _ => by contradiction
  | .zero, .cons _ _, _ => rfl
  | .succ _, .cons _ _, _ => by rw [get!, get]; apply get!_of_get
