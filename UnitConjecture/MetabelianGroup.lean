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

lemma kernel_pow (k : K) (n : ℕ) : (k, (0 : Q)) ^ n = (n • k, (0 : Q)) := by
  induction n with
    | zero => rw [pow_zero, zero_nsmul]; rfl
    | succ m ih => 
      rw [pow_succ, ih, succ_nsmul]
      show (k + ((0 : Q) +ᵥ m • k) + c 0 0, 0 + 0) = (k + m • k, 0)
      rw [zero_vadd, ccl.cocycle_zero, add_zero, add_zero]

end MetabelianGroup