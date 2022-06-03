import Polylean.Morphisms
import Polylean.GroupAction

/-
Metabelian groups are group extensions `1 → K → G → Q → 1` with both the kernel and the quotient abelian. Such an extension is determined by data:

* a group action of `Q` on `K`
* a cocyle `c: Q → Q → K`

We have to define the cocycle condition and construct a group structure on a structure extending `K × Q`. The main step is to show that the cocyle condition implies associativity.
-/


/-
A cocycle associated with a certain action of `Q` on `K` via automorphisms is a function from `Q × Q` to `K` satisfying
a certain requirement known as the "cocycle condition". This allows one to define an associative multiplication operation on the set `K × Q` as shown below.
The requirement `c 0 0 = (0 : K)` is not strictly necessary and mainly for convenience.
-/
class Cocycle {Q K : Type _} [AddCommGroup Q] [AddCommGroup K] [α : AddCommGroup.ActionByAutomorphisms Q K]
  (c : Q → Q → K) where
  cocycleId : c 0 0 = (0 : K)
  cocycleCondition : ∀ q q' q'' : Q, c q q' + c (q + q') q'' = q • c q' q'' + c q (q' + q'')

namespace Cocycle

/-
A few deductions from the cocycle condition.
-/

variable {Q K : Type _} [AddCommGroup Q] [AddCommGroup K]
variable [α : AddCommGroup.ActionByAutomorphisms Q K]
variable (c : Q → Q → K) [cocycle : Cocycle c]

attribute [simp] cocycleId

@[simp] theorem leftId : ∀ {q : Q}, c 0 q = (0 : K) := by
  intro q
  have := Eq.symm $ cocycle.cocycleCondition 0 0 q
  rw [zero_add, zero_add, add_right_cancel_iff, cocycle.cocycleId, AddCommGroup.Action.id_action] at this
  assumption

@[simp] theorem rightId : ∀ {q : Q}, c q 0 = (0 : K) := by
  intro q
  have := cocycle.cocycleCondition q 0 0
  rw [add_zero, add_zero, add_right_cancel_iff, cocycle.cocycleId, AddCommGroup.ActionByAutomorphisms.act_zero] at this
  assumption

theorem invRel : ∀ q : Q, c q (-q) = q • (c (-q) q) := by
  intro q
  have := cocycle.cocycleCondition q (-q) q
  rw [add_left_neg, add_right_neg, leftId c, rightId c, add_zero, add_zero] at this
  assumption

theorem invRel' : ∀ q : Q, c (-q) q = (-q) • (c q (-q)) := by
  intro q
  have := invRel c (-q)
  rw [neg_neg] at this
  assumption

end Cocycle

namespace MetabelianGroup

variable {Q K : Type _} [AddCommGroup Q] [AddCommGroup K]
variable [α : AddCommGroup.ActionByAutomorphisms Q K]
variable (c : Q → Q → K) [cocycle : Cocycle c]

/-
The multiplication operation defined using the cocycle.
The cocycle condition is crucially used in showing associativity and other properties.
-/
def mul : (K × Q) → (K × Q) → (K × Q)
  | (k, q), (k', q') => (k + (q • k') + c q q', q + q')

def e : K × Q := (0, 0)

def inv : K × Q → K × Q
  | (k, q) => (- ((-q) • (k  + c q (-q))), -q)

theorem left_id : ∀ (g : K × Q), mul c e g = g
  | (k, q) => by simp [e, mul]; rw [AddCommGroup.Action.id_action]

theorem right_id : ∀ (g : K × Q), mul c g e = g
  | (k, q) => by simp [e, mul]; rw [AddCommGroup.ActionByAutomorphisms.act_zero, add_zero]

theorem left_inv : ∀ (g : K × Q), mul c (inv c g) g = e
  | (k , q) => by
    simp [mul, inv, e]
    rw [cocycle.invRel' c q, add_assoc, ← AddCommGroup.ActionByAutomorphisms.add_dist, add_left_neg]

theorem right_inv : ∀ (g : K × Q), mul c g (inv c g) = e
  | (k, q) => by
    simp [mul, inv, e]
    rw [AddCommGroup.ActionByAutomorphisms.neg_push, ← AddCommGroup.Action.compatibility, add_right_neg, AddCommGroup.Action.id_action, add_assoc, add_comm _ (c _ _), ← add_assoc, add_right_neg]

theorem mul_assoc : ∀ (g g' g'' : K × Q), mul c (mul c g g') g'' =  mul c g (mul c g' g'')
  | (k, q), (k', q'), (k'', q'') => by
    simp [mul]
    apply And.intro
    · rw [AddCommGroup.ActionByAutomorphisms.add_dist, add_assoc, add_assoc, add_assoc, add_assoc, add_assoc, add_left_cancel_iff,
         AddCommGroup.ActionByAutomorphisms.add_dist, add_assoc, add_left_cancel_iff,
         AddCommGroup.Action.compatibility, ← add_assoc, ← add_assoc, add_comm (c q q') _, add_assoc, add_assoc, add_left_cancel_iff]
      exact cocycle.cocycleCondition q q' q'' -- the cocycle condition implies associativity
    · rw [add_assoc]

-- A proof that `K × Q` can be given a group structure using the above multiplication operation
instance metabeliangroup : Group (K × Q) :=
  {
    mul := mul c,
    mul_assoc := mul_assoc c,
    one := e,
    mul_one := right_id c,
    one_mul := left_id c,

    inv := inv c,
    mul_left_inv := left_inv c,

    div_eq_mul_inv := by intros; rfl

    npow_zero' := by intros; rfl,
    npow_succ' := by intros; rfl,

    gpow_zero' := by intros; rfl,
    gpow_succ' := by intros; rfl,
    gpow_neg' := by intros; rfl,
  }

end MetabelianGroup

section Exactness

/-
The Metabelian construction gives a group `M` that is an extension of `Q` by `K`, i.e., one that fits in the short exact sequence
1 -> K -> M -> Q -> 1
This section describes the inclusion of `K` into `M` and shows that it is an isomorphism onto the subgroup of elements `(k, 0)` of `M (= K × Q)`.
This isomorphism is later used in proving that `P` is torsion-free from the fact that `ℤ³` is torsion-free.
-/

variable (Q K : Type _) [AddCommGroup Q] [AddCommGroup K]
variable [α : AddCommGroup.ActionByAutomorphisms Q K]
variable (c : Q → Q → K) [cocycle : Cocycle c]

instance G : Group (K × Q) := MetabelianGroup.metabeliangroup c

-- this is the subgroup of the metabelian group that occurs as
-- the image of the inclusion of `K` and the kernel of the projection onto `Q`.
def Metabelian.Kernel := subType (λ ((k, q) : K × Q) => q = (0 : Q))

def Metabelian.Kernel.inclusion : K → (Metabelian.Kernel Q K)
  | k => ⟨(k, 0), rfl⟩

def Metabelian.Kernel.K_projection : (Metabelian.Kernel Q K) → K
  | ⟨(k, _), _⟩ => k

instance : subGroup (λ ((k, q) : K × Q) => q = (0 : Q)) where
  mul_closure := by
    intro ⟨ka, qa⟩ ⟨kb, qb⟩; intro hqa hqb
    show (Mul.mul (ka, qa) (kb, qb)).snd = 0
    simp [Mul.mul, MetabelianGroup.mul] at *
    rw [hqa, hqb, add_zero]
  inv_closure := by
    intro ⟨ka, qa⟩; intro h
    simp [Inv.inv, MetabelianGroup.inv] at *
    apply neg_eq_of_add_eq_zero
    rw [h, add_zero]
  id_closure := rfl

instance kernel_group : Group (Metabelian.Kernel Q K) :=
  subGroup.Group _

instance kernel_inclusion : Group.Homomorphism (subType.val (λ ((k, q) : K × Q) => q = (0 : Q))) := inferInstance

theorem Metabelian.Kernel.mul_comm : ∀ k k' : Metabelian.Kernel Q K, k * k' = k' * k := by
  intro ⟨⟨ka, 0⟩, rfl⟩; intro ⟨⟨kb, 0⟩, rfl⟩
  apply subType.eq_of_val_eq
  show Mul.mul (ka, (0 : Q)) (kb, 0) = Mul.mul (kb, 0) (ka, 0)
  simp [Mul.mul, MetabelianGroup.mul]; rw [AddCommGroup.Action.id_action, AddCommGroup.Action.id_action, add_comm]

instance : AddCommGroup (Metabelian.Kernel Q K) := Group.to_additive (Metabelian.Kernel.mul_comm _ _ _)

instance : AddCommGroup.Homomorphism (Metabelian.Kernel.inclusion Q K) where
  add_dist := by
    intro k k'
    simp [Metabelian.Kernel.inclusion]
    apply subType.eq_of_val_eq
    show (k + k', (0 : Q)) = Mul.mul (k, 0) (k', 0)
    simp [Mul.mul, MetabelianGroup.mul]; rw [AddCommGroup.Action.id_action]

instance : AddCommGroup.Homomorphism (Metabelian.Kernel.K_projection Q K) where
  add_dist := by
    intro ⟨⟨k, 0⟩, rfl⟩; intro ⟨⟨k', 0⟩, rfl⟩
    simp [Metabelian.Kernel.K_projection, MetabelianGroup.mul]; rw [AddCommGroup.Action.id_action]

instance : AddCommGroup.Isomorphism K (Metabelian.Kernel Q K) :=
  {
    map := Metabelian.Kernel.inclusion Q K
    mapHom := inferInstance
    inv := Metabelian.Kernel.K_projection Q K
    invHom := inferInstance
    idSrc := by apply funext; intro; simp [Metabelian.Kernel.K_projection, Metabelian.Kernel.inclusion]
    idTgt := by apply funext; intro ⟨⟨k, 0⟩, rfl⟩; simp [Metabelian.Kernel.K_projection, Metabelian.Kernel.inclusion]
  }

end Exactness
