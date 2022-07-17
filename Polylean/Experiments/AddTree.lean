import Lean.Meta 
import Lean.Elab
import Polylean.FreeAbelianGroup
import Std
import Lean
import Aesop
open Lean Meta Elab Nat Term Std

declare_aesop_rule_sets [AddTree]

@[aesop safe (rule_sets [AddTree]) [constructors, cases]] inductive AddTree (α : Type _) where
  | leaf : α → AddTree α 
  | negLeaf : AddTree α → AddTree α
  | node : AddTree α  → AddTree α  → AddTree α 
  | subNode: AddTree α  → AddTree α  → AddTree α
  deriving Repr

@[aesop norm (rule_sets [AddTree]) [unfold]] def AddTree.fold {α : Type u} [AddCommGroup α] : AddTree α → α
  | AddTree.leaf a => a
  | AddTree.negLeaf t => -(fold t)
  | AddTree.node l r =>  (fold l) + (fold r)
  | AddTree.subNode l r => (fold l) - (fold r)

@[aesop norm (rule_sets [AddTree]) [unfold]] def AddTree.map {α β : Type _} (f : α → β) : AddTree α → AddTree β
  | AddTree.leaf a => AddTree.leaf (f a)
  | AddTree.negLeaf a => AddTree.negLeaf (map f a)
  | AddTree.node l r => AddTree.node (map f l) (map f r)
  | AddTree.subNode l r => AddTree.subNode (map f l) (map f r)

@[aesop norm (rule_sets [AddTree]) [unfold]] def AddTree.reduce {α : Type _} : AddTree (AddTree α) → AddTree α
  | AddTree.leaf adt => adt
  | AddTree.negLeaf adt => AddTree.negLeaf (reduce adt)
  | AddTree.node lt rt => AddTree.node (reduce lt) (reduce rt)
  | AddTree.subNode lt rt => AddTree.subNode (reduce lt) (reduce rt)

section Instances
/-
Reference:  Monads, partial evaluations, and rewriting by Tobias Fritz and Paulo Perrone
https://arxiv.org/pdf/1810.06037.pdf
-/

instance : Functor AddTree where
    map := AddTree.map

attribute [aesop norm (rule_sets [AddTree]) [unfold]] Functor.map

instance : LawfulFunctor AddTree where
  map_const := rfl
  id_map := by intro _ t; induction t <;> aesop (rule_sets [AddTree])
  comp_map := by intro _ _ _ _ _ t; induction t <;> aesop (rule_sets [AddTree])

instance : Monad AddTree where
  pure := AddTree.leaf
  bind := λ adt f => (adt.map f).reduce

attribute [aesop norm (rule_sets [AddTree]) [unfold]] pure
attribute [aesop norm (rule_sets [AddTree]) [unfold]] bind

attribute [aesop norm (rule_sets [AddTree]) [unfold]] Seq.seq
attribute [aesop norm (rule_sets [AddTree]) [unfold]] SeqLeft.seqLeft
attribute [aesop norm (rule_sets [AddTree]) [unfold]] SeqRight.seqRight

instance : LawfulMonad AddTree where
  bind_pure_comp := by intro _ _ _ t; induction t <;> aesop (rule_sets [AddTree])
  bind_map := by intro _ _ _ t; induction t <;> aesop (rule_sets [AddTree])
  pure_bind := by aesop (rule_sets [AddTree])
  bind_assoc := by intro _ _ _ t; induction t <;> aesop (rule_sets [AddTree])
  seqLeft_eq := by intro _ _ t₁ t₂; induction t₁ <;> induction t₂ <;> aesop (rule_sets [AddTree])
  seqRight_eq := by intro _ _ t₁ t₂; induction t₁ <;> induction t₂ <;> aesop (rule_sets [AddTree])
  pure_seq := by intro _ _ _ t; induction t <;> aesop (rule_sets [AddTree])

end Instances

section Reflection

def hOp (fname : Name) : Expr → MetaM (Expr × Expr)
  | e@(.app (Expr.app _ a _) b _) => do
      guard $ e.isAppOf fname
      guard $ ← isDefEq (← inferType a) (← inferType e)
      guard $ ← isDefEq (← inferType b) (← inferType e)
      return (a, b)
  | _ => failure

def invOp (fname : Name) : Expr → MetaM Expr
 | e@(.app _ a _) => do
    guard $ e.isAppOf fname
    guard $ ← isDefEq (← inferType a) (← inferType e)
    return a
 | _ => failure

partial def treeM (e : Expr) : MetaM Expr :=
    hOp ``HAdd.hAdd e >>= (λ (a, b) => return ← mkAppM ``AddTree.node #[← treeM a, ← treeM b])    <|>
    hOp ``HSub.hSub e >>= (λ (a, b) => return ← mkAppM ``AddTree.subNode #[← treeM a, ← treeM b]) <|>
    invOp ``Neg.neg e >>= (λ a => return ← mkAppM ``AddTree.negLeaf #[← treeM a])                 <|>
    mkAppM ``AddTree.leaf #[e]

elab "tree#" s:term : term => do
  let e ← Term.elabTerm s none
  treeM e

#eval tree# -((2 + -3) - 1)

-- this is an alternative approach that directly analyses the syntax
partial def addtreeM : TermElab :=
  fun stx typ? => do
  match stx with
  | `(HAdd.hAdd _ _ _ _ $a:term $b:term) =>
    let l ← addtreeM a typ?
    let r ← addtreeM b typ?
    return mkApp2 (mkConst `AddTree.node) l r
  | `(HSub.hSub _ _ _ _ $a:term $b:term) =>
    let l ← addtreeM a typ?
    let r ← addtreeM b typ?
    return mkApp2 (mkConst `AddTree.subNode) l r
  | `(Neg.neg _ _ $a:term) =>
    let t ← addtreeM a typ?
    return mkApp (mkConst `AddTree.negLeaf) t
  | `($a:term) =>
    return mkApp (mkConst `AddTree.leaf) (← Term.elabTerm a typ?) -- this leads to an infinite recursion. Maybe creating a new syntax category will help

end Reflection


theorem AddTree.fold_tree_map_eq {A B : Type _} [AddCommGroup A] [AddCommGroup B]
  (φ : A → B) [Homφ : AddCommGroup.Homomorphism φ] (t : AddTree A) : φ t.fold = (t.map φ).fold := by
    induction t with
      | leaf a => rw [map, fold, fold] 
      | negLeaf t ih => rw [map, fold, fold, Homφ.neg_push, ih]
      | node l r ihl ihr => rw [map, fold, fold, Homφ.add_dist, ihl, ihr]
      | subNode l r ihl ihr => rw [map, fold, fold, Homφ.neg_dist, ihl, ihr]
