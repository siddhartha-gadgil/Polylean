import Mathlib.Algebra.Hom.Group
import Mathlib.GroupTheory.Submonoid.Basic
import Polylean.Cocycle

/-!
Metabelian groups are group extensions `1 → K → G → Q → 1` with both the kernel and the quotient abelian. Such an extension is determined by data:

* a group action of `Q` on `K`
* a cocyle `c: Q → Q → K`

We define the cocycle condition and construct a group structure on a structure extending `K × Q`. The main step is to show that the cocyle condition implies associativity.
-/

namespace MetabelianGroup

variable {Q K : Type _} [AddGroup Q] [AddCommGroup K]
variable (c : Q → Q → K) [ccl : Cocycle c]

declare_aesop_rule_sets [Metabelian]

/-- The multiplication operation defined using the cocycle.
The cocycle condition is crucially used in showing associativity and other properties. -/
@[reducible, aesop norm unfold (rule_sets [Metabelian])] 
def mul : (K × Q) → (K × Q) → (K × Q)
  | (k, q), (k', q') => (k + (q +ᵥ k') + c q q', q + q')

/-- The identity element of the Metabelian group, 
  which is the ordered pair of the identities of the individual groups. -/
@[reducible, aesop norm unfold (rule_sets [Metabelian])] 
def e : K × Q := (0, 0)

/-- The inverse operation of the Metabelian group. -/
@[reducible, aesop norm unfold (rule_sets [Metabelian])] 
def inv : K × Q → K × Q
  | (k, q) => (- ((-q) +ᵥ (k  + c q (-q))), -q)

/-!
Some of the standard lemmas to show that `K × Q` has the structure of a group with the above operations.
-/

@[aesop norm (rule_sets [Metabelian])] 
lemma left_id : ∀ (g : K × Q), mul c e g = g
  | (k, q) => by aesop (rule_sets [Cocycle, Metabelian])

@[aesop norm (rule_sets [Metabelian])]
lemma right_id : ∀ (g : K × Q), mul c g e = g
  | (k, q) => by aesop (rule_sets [Cocycle, Metabelian, AutAction])

@[aesop norm (rule_sets [Metabelian])]
lemma left_inv : ∀ (g : K × Q), mul c (inv c g) g = e
  | (k , q) => by
    have := Cocycle.inv_rel' c q
    aesop (rule_sets [Metabelian, Cocycle, AutAction])

@[aesop norm (rule_sets [Metabelian])]
lemma right_inv : ∀ (g : K × Q), mul c g (inv c g) = e
  | (k, q) => by aesop (rule_sets [Metabelian, Cocycle, AutAction])

@[aesop unsafe (rule_sets [Metabelian])]
theorem mul_assoc : ∀ (g g' g'' : K × Q), mul c (mul c g g') g'' =  mul c g (mul c g' g'')
  | (k, q), (k', q'), (k'', q'') => by
    aesop (rule_sets [Metabelian, Cocycle, AutAction]) 
        (options := {terminal := false, warnOnNonterminal := false})
    · simp only [add_assoc, add_left_cancel_iff]
      rw [add_left_comm, add_left_cancel_iff]
      -- The cocycle condition is precisely what is required for the associativity of multiplication
      exact ccl.cocycle_condition q q' q''
    · apply add_assoc

-- A proof that `K × Q` can be given a group structure using the above multiplication operation
instance metabelianGroup : Group (K × Q) :=
  {
    mul := mul c,
    one := e,
    inv := inv c,

    mul_one := right_id c,
    one_mul := left_id c,
    mul_assoc := mul_assoc c,

    mul_left_inv := left_inv c,
    div_eq_mul_inv := by intros; rfl
  }

end MetabelianGroup


section Exactness

/-
The Metabelian construction gives a group `M` that is an extension of `Q` by `K`, i.e., one that fits in the short exact sequence
1 -> K -> M -> Q -> 1
This section describes the inclusion of `K` into `M` and shows that it is an isomorphism onto the subgroup of elements `(k, 0)` of `M (= K × Q)`.
This isomorphism is later used in proving that `P` is torsion-free from the fact that `ℤ³` is torsion-free.
-/

variable (K Q : Type _) [AddCommGroup K] [AddCommGroup Q]
variable (c : Q → Q → K) [ccl : Cocycle c]

instance : Group (K × Q) := MetabelianGroup.metabelianGroup c

-- this is the subgroup of the metabelian group that occurs as
-- the image of the inclusion of `K` and the kernel of the projection onto `Q`.
def Metabelian.Kernel : Set (K × Q)
  | (_, q) => q = 0

def Metabelian.Kernel.inclusion : K → (Metabelian.Kernel K Q)
  | k => ⟨(k, 0), rfl⟩

def Metabelian.Kernel.projection : (Metabelian.Kernel K Q) → K
  | ⟨(k, _), _⟩ => k

instance : Submonoid (K × Q) where
  carrier := Metabelian.Kernel K Q
  mul_mem' := by
    intro ⟨_, qa⟩ ⟨_, qb⟩ (hqa : qa = 0) (hqb : qb = 0)
    subst hqa hqb
    show 0 + 0 = 0
    rw [add_zero]
  one_mem' := rfl

/-
instance : subGroup (λ ((_, q) : K × Q) => q = (0 : Q)) where
  mul_closure := by
    intro ⟨ka, qa⟩ ⟨kb, qb⟩; intro (hqa : qa = 0) (hqb : qb = 0)
    subst hqa hqb
    reduceGoal
    rw [add_zero]
  inv_closure := by
    intro ⟨ka, qa⟩; intro (h : qa = 0)
    subst h
    reduceGoal
    rw [neg_zero]
  id_closure := rfl

instance kernel_group : Group (Metabelian.Kernel Q K) :=
  subGroup.Group _

instance kernel_inclusion : Group.Homomorphism (subType.val (λ ((_, q) : K × Q) => q = (0 : Q))) := inferInstance

theorem Metabelian.Kernel.mul_comm : ∀ k k' : Metabelian.Kernel Q K, k * k' = k' * k := by
  intro ⟨⟨ka, 0⟩, rfl⟩; intro ⟨⟨kb, 0⟩, rfl⟩
  apply subType.eq_of_val_eq
  show (ka, (0 : Q)) * (kb, 0) = (kb, 0) * (ka, 0)
  repeat (rw [MetabelianGroup.mult])
  simp only [add_zero, Cocycle.cocycleId, AddCommGroup.Action.id_action, add_comm]

instance kernel_addgroup : AddCommGroup (Metabelian.Kernel Q K) :=
  Group.to_additive (Metabelian.Kernel.mul_comm Q K c)

instance : AddCommGroup.Homomorphism (Metabelian.Kernel.inclusion Q K) where
  add_dist := by
    intro k k'
    show _ = ⟨(k, 0) * (k', 0), _⟩
    apply subType.eq_of_val_eq
    show ((k + k'), (0 : Q)) = (k, (0 : Q)) * (k', (0 : Q))
    rw [MetabelianGroup.mult]
    simp only [add_zero, Cocycle.cocycleId, AddCommGroup.Action.id_action, add_comm]

instance : AddCommGroup.Homomorphism (Metabelian.Kernel.projection Q K) where
  add_dist := by
    intro ⟨⟨k, 0⟩, rfl⟩; intro ⟨⟨k', 0⟩, rfl⟩
    -- show (Metabelian.Kernel.projection Q K) ⟨(k, (0 : Q)) * (k', (0 : Q)), _⟩ = k + k'
    show (fun (k, _) => k) ((k, (0 : Q)) * (k', (0 : Q))) = k + k'
    reduceGoal
    -- show k + (0 : Q) +ᵥ k' + c 0 0 = k + k'
    simp

instance : AddCommGroup.Isomorphism K (Metabelian.Kernel Q K) :=
  {
    map := Metabelian.Kernel.inclusion Q K
    mapHom := inferInstance
    inv := Metabelian.Kernel.projection Q K
    invHom := inferInstance
    idSrc := by 
              apply funext
              intro x
              show (Metabelian.Kernel.projection Q K) ((Metabelian.Kernel.inclusion Q K) x) = x 
              rw [Metabelian.Kernel.projection, Metabelian.Kernel.inclusion]
    idTgt := by 
              apply funext 
              intro ⟨⟨k, 0⟩, rfl⟩
              show (Metabelian.Kernel.inclusion Q K) ((Metabelian.Kernel.projection Q K) ⟨⟨k, 0⟩, rfl⟩) = ⟨⟨k, 0⟩, rfl⟩
              rw [Metabelian.Kernel.projection, Metabelian.Kernel.inclusion]
  }

end Exactness
-/