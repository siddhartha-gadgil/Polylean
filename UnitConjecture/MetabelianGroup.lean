import Mathlib.Algebra.Hom.Group
import Mathlib.GroupTheory.Submonoid.Operations
import UnitConjecture.Cocycle
import UnitConjecture.Tactics.AesopRuleSets

/-!

## Metabelian groups

Metabelian groups are group extensions `1 → K → G → Q → 1` with both the kernel and the quotient Abelian. 
Such an extension is determined by data:

* a group action of `Q` on `K` by automorphisms
* a cocyle `c: Q → Q → K`

We define the cocycle condition and construct a group structure on a structure extending `K × Q`. 
The main step is to show that the cocyle condition implies associativity.
-/

namespace MetabelianGroup

variable {Q K : Type _} [AddGroup Q] [AddCommGroup K]
variable (c : Q → Q → K) [ccl : Cocycle c]

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

set_option synthInstance.checkSynthOrder false in -- HACK
/-- A group structure on `K × Q` using the above multiplication operation. -/
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

@[aesop norm simp (rule_sets [Metabelian])]
theorem mul_def {k k' : K} {q q' : Q} : (k, q) * (k', q') = (k + (q +ᵥ k') + c q q', q + q') := rfl

lemma kernel_pow (k : K) (n : ℕ) : (k, (0 : Q)) ^ n = (n • k, (0 : Q)) := by
  induction n <;>
      aesop (rule_sets [Metabelian, Cocycle]) 
      (add norm simp [pow_zero, pow_succ, zero_nsmul, succ_nsmul])


section Exactness

/-!
### Exactness

A proof that the Metabelian group `G` constructed as above indeed lies in middle of 
the short exact sequence `1 → K → G → Q → 1`.
-/

/-- The inclusion map from the kernel to the Metabelian group. -/
@[aesop norm unfold (rule_sets [Metabelian])]
def Kernel.inclusion : (Multiplicative K) →* (K × Q) :=
  { toFun := (·, (0 : Q)),
    map_one' := rfl,
    map_mul' := by aesop (rule_sets [Metabelian, Cocycle]) }

/-- A proof that the inclusion map is injective. -/
theorem Kernel.inclusion_inj : Function.Injective (Kernel.inclusion c) := by
  intros _ _; simp [Kernel.inclusion]

/--- The projection map from the Metabelian group to the quotient. -/
@[aesop norm unfold (rule_sets [Metabelian])]
def Quotient.projection : K × Q →* (Multiplicative Q) :=
  { toFun := Prod.snd,
    map_one' := rfl
    map_mul' := by intro ⟨_, _⟩ ⟨_, _⟩; rfl }

/-- A proof that the projection map is surjective. -/
theorem Quotient.projection_surj : Function.Surjective (Quotient.projection c) := by
  intro q
  use ⟨(0 : K), q⟩
  aesop

/-- A proof that the image of the first map is the kernel of the second map. -/
theorem exact_seq : MonoidHom.mrange (Kernel.inclusion c) = MonoidHom.mker (Quotient.projection c) := by
  ext ⟨_, _⟩; aesop (rule_sets [Metabelian]) (add norm [MonoidHom.mem_mker])

end Exactness

end MetabelianGroup