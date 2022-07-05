import Lean.Meta 
import Lean.Elab
import Polylean.Experiments.FinGenFreeAbGroup
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
  | AddTree.node l r =>  (fold l) + (fold r)
  | AddTree.negLeaf t => -(fold t)
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


section IndexAddTree

abbrev IndexAddTree := AddTree Nat 

@[simp] def AddTree.indexTree {α : Type u} [DecidableEq α] (t : AddTree α)
  (accum : Array α := #[]) : 
      IndexAddTree × (Array α) := 
  match t with
  | AddTree.leaf a => 
    match accum.getIdx? a with
    | some i => (AddTree.leaf i, accum)
    | none => (AddTree.leaf (accum.size), accum)
  | AddTree.node l r =>  
    let (lIdx, lAccum) := indexTree l accum
    let (rIdx, rAccum) := indexTree r lAccum
    (AddTree.node lIdx rIdx, rAccum)
  | AddTree.negLeaf t =>
    let (tIdx, accum') := indexTree t accum
    (AddTree.negLeaf tIdx, accum')
  | AddTree.subNode l r =>
    let (lIdx, lAccum) := indexTree l accum
    let (rIdx, rAccum) := indexTree r lAccum
    (AddTree.subNode lIdx rIdx, rAccum)

def IndexAddTree.map {α : Type _} [AddCommGroup α] [Repr α]
  (t : IndexAddTree) (basisImages : List α) : AddTree α :=
  if h:basisImages.length = 0 then
    AddTree.leaf (0 : α)
  else
    match t with
    | AddTree.leaf i => AddTree.leaf (basisImages.get $ Fin.ofNat' i $ Nat.pos_of_ne_zero h)
    | AddTree.negLeaf τ => AddTree.negLeaf (map τ basisImages)
    | AddTree.node l r => AddTree.node (map l basisImages) (map r basisImages)
    | AddTree.subNode l r => AddTree.subNode (map l basisImages) (map r basisImages)

end IndexAddTree


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

-- abbrev tree {α : Type _} (a : α) : AddTree α := tree# a


syntax (name := addtreeElab) "addTree#" term : term

partial def addtreeM : TermElab :=
  fun stx typ? => do
  match stx with
  | `(HAdd.hAdd _ _ _ _ $a:term $b:term) =>
    dbg_trace "Addition"
    let l ← addtreeM a typ?
    let r ← addtreeM b typ?
    return mkApp2 (mkConst `AddTree.node) l r
  | `(HSub.hSub _ _ _ _ $a:term $b:term) =>
    dbg_trace "Subtraction"
    let l ← addtreeM a typ?
    let r ← addtreeM b typ?
    return mkApp2 (mkConst `AddTree.subNode) l r
  | `(Neg.neg _ _ $a:term) =>
    dbg_trace "Negation"
    let t ← addtreeM a typ?
    return mkApp (mkConst `AddTree.negLeaf) t
  | `($a:term) =>
    dbg_trace "Leaf"
    return mkApp (mkConst `AddTree.leaf) (← Term.elabTerm a typ?) -- this leads to an infinite recursion. Maybe creating a new syntax category will help

end Reflection


theorem AddTree.fold_tree_map_eq {A B : Type _} [AddCommGroup A] [AddCommGroup B]
  (φ : A → B) [Homφ : AddCommGroup.Homomorphism φ] : (t : AddTree A) → φ t.fold = (t.map φ).fold := by 
    intro t
    induction t with
      | leaf a => rw [map, fold, fold] 
      | negLeaf a ih => rw [map, fold, fold, Homφ.neg_push, ih]
      | node l r ihl ihr => rw [map, fold, fold, Homφ.add_dist, ihl, ihr]
      | subNode l r ihl ihr => rw [map, fold, fold, Homφ.neg_dist, ihl, ihr]

inductive Hidden
  | conceal : {α : Sort _} → (a : α) → Hidden

def extractHidden (e : Expr) : MetaM Expr := do
  guard $ e.isAppOf ``Hidden.conceal
  match e with
  | .app _ v _ => return v
  | _ => failure

def AddTree.reduceTreeEqElm {α : Type} [DecidableEq α] [AddCommGroup α] (t : AddTree α) : α :=
  let ⟨it, ⟨l⟩⟩ := t.indexTree
  let n := l.length
  let ϕ : ℤ ^ n → α := inducedFreeMap l rfl
  let τ : AddTree (ℤ ^ n) := it.map (ℤbasis n)
  τ |>.map ϕ |> fold

def AddTree.reduceTreeEqn {α : Type _} [DecidableEq α] [AddCommGroup α] (t : AddTree α) : Hidden :=
  let ⟨it, ⟨l⟩⟩ := t.indexTree
  let n := l.length
  let ϕ : ℤ ^ n → α := inducedFreeMap l rfl
  let τ : AddTree (ℤ ^ n) := it.map (ℤbasis n)
  Hidden.conceal $ AddTree.fold_tree_map_eq ϕ τ

def AddTree.reduceProof (e : Expr) : MetaM Expr := do
  let t ← treeM e
  let prf ← extractHidden $ ← mkAppM ``AddTree.reduceTreeEqn #[t]
  let eqn ← inferType prf
  guard $ eqn.isEq -- checking that the equation is indeed an equation
  match eqn with
  | .app (.app _ lhs _) rhs _ => -- extracting the lhs and rhs of the equation
    -- showing that `rhs` and `e` are definitionally equal
    let rhs_eq_e ← mkFreshExprMVar (some $ ← mkEq rhs e)
    assignExprMVar rhs_eq_e.mvarId! (mkConst ``rfl)
    -- composing `lhs = rhs` and `rhs = e` by transitivity of equality
    let lhs_eq_e ← mkFreshExprMVar (some $ ← mkEq lhs e)
    assignExprMVar lhs_eq_e.mvarId! $ ← mkEqTrans prf rhs_eq_e
    -- reducing both sides of the equation and returning the expression
    -- reduce lhs_eq_e
    return lhs_eq_e
  | _ => failure

elab "reduceProof# " s:term : term => do
  let e ← Term.elabTerm s none
  AddTree.reduceProof e

-- #check reduceProof# ((1 : ℤ) + 2 + ((-3) + 5))
