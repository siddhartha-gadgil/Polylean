import Polylean.GroupAction

/-
Metabelian groups are group extensions `1 → K → G → Q → 1` with both the kernel and the quotient abelian. Such an extension is determined by data:

* a group action of `Q` on `K`
* a cocyle `c: Q → Q → K`

We have to define the cocycle condition and construct a group structure on a structure extending `K × Q`. The main step is to show that the cocyle condition implies associativity.
-/

class Cocycle {Q K : Type _} [AddCommGroup Q] [AddCommGroup K] [α : AddCommGroup.ActionByAutomorphisms Q K]
  (c : Q → Q → K) where
  cocycleId : c 0 0 = (0 : K)
  cocycleCondition : ∀ q q' q'' : Q, c q q' + c (q + q') q'' = q • c q' q'' + c q (q' + q'')

namespace Cocycle

variable {Q K : Type _} [AddCommGroup Q] [AddCommGroup K]
variable [α : AddCommGroup.ActionByAutomorphisms Q K]
variable (c : Q → Q → K) [cocycle : Cocycle c]

theorem leftId : ∀ {q : Q}, c 0 q = (0 : K) := by
  intro q
  have := Eq.symm $ cocycle.cocycleCondition 0 0 q
  rw [zero_add, zero_add, add_right_cancel_iff, cocycle.cocycleId, AddCommGroup.Action.id_action] at this
  assumption

theorem rightId : ∀ {q : Q}, c q 0 = (0 : K) := by
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

def mul : (K × Q) → (K × Q) → (K × Q)
  | (k, q), (k', q') => (k + (q • k') + c q q', q + q')

def e : K × Q := (0, 0)

def inv : K × Q → K × Q
  | (k, q) => (- ((-q) • (k  + c q (-q))), -q)

theorem left_id : ∀ (g : K × Q), mul c e g = g
  | (k, q) => by simp [e, mul]; rw [cocycle.leftId, AddCommGroup.Action.id_action, add_zero]

theorem right_id : ∀ (g : K × Q), mul c g e = g
  | (k, q) => by simp [e, mul]; rw [cocycle.rightId, AddCommGroup.ActionByAutomorphisms.act_zero, add_zero, add_zero]

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
      exact cocycle.cocycleCondition q q' q''
    · rw [add_assoc]

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

section Product

variable {Q K : Type _} [AddCommGroup Q] [AddCommGroup K]

def trivial_mul : Q → K → K
  | _ => id

instance trivial_action : AddCommGroup.ActionByAutomorphisms Q K :=
  {
    sMul := trivial_mul
    id_action := rfl
    compatibility := rfl
    add_dist := λ b b' => rfl
  }

def trivial_cocycle : Q → Q → K
  | _, _ => 0

instance : @Cocycle Q K _ _ trivial_action trivial_cocycle :=
  {
    cocycleId := rfl
    cocycleCondition := λ _ _ _ => rfl
  }

theorem product_comm : ∀ g h : K × Q, MetabelianGroup.mul trivial_cocycle g h = MetabelianGroup.mul trivial_cocycle h g := by
  intro (k, q)
  intro (k', q')
  simp [MetabelianGroup.mul, trivial_cocycle]
  apply And.intro
  · have : ∀ q : Q, ∀ κ : K, q • κ = κ := λ _ _ => rfl
    rw [this, this, add_comm]
  · exact AddCommGroup.add_comm q q'

end Product

namespace DirectSum

instance to_additive {G : Type _} [Grp : Group G] (mul_comm : ∀ g h : G, g * h = h * g) : AddCommGroup G :=
  {
    add := Grp.mul
    add_assoc := Grp.mul_assoc
    zero := Grp.one
    add_zero := Grp.mul_one
    zero_add := Grp.one_mul

    neg := Grp.inv
    add_left_neg := Grp.mul_left_inv
    add_comm := mul_comm

    nsmul_succ' := by intros; rfl
    nsmul_zero' := by intros; rfl

    sub_eq_add_neg := by intros; rfl

    gsmul_zero' := by intros; rfl
    gsmul_succ' := by intros; rfl
    gsmul_neg' := by intros; rfl
  }

instance directSum {A B : Type _} [AddCommGroup A] [AddCommGroup B] : AddCommGroup (A × B) :=
  to_additive product_comm

end DirectSum
