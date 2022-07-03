import Lean.Meta 
import Lean.Elab
import Polylean.Experiments.FinGenFreeAbGroup
import Std
import Lean
open Lean Meta Elab Nat Term Std


inductive AddTree (α : Type _) where
  | leaf : α → AddTree α 
  | negLeaf : AddTree α → AddTree α
  | node : AddTree α  → AddTree α  → AddTree α 
  | subNode: AddTree α  → AddTree α  → AddTree α

@[reducible, simp] def AddTree.fold {α : Type u} [AddCommGroup α] : AddTree α → α
  | AddTree.leaf a => a
  | AddTree.node l r =>  (fold l) + (fold r)
  | AddTree.negLeaf t => -(fold t)
  | AddTree.subNode l r => (fold l) - (fold r)

@[reducible] def AddTree.elements {α : Type _} : AddTree α → List α
  | AddTree.leaf a => [a]
  | AddTree.negLeaf t => elements t
  | AddTree.node l r => (elements l) ++ (elements r)
  | AddTree.subNode l r => (elements l) ++ (elements r)

def AddTree.negate {α : Type _} : AddTree α → AddTree α
  | AddTree.leaf a => AddTree.negLeaf (AddTree.leaf a)
  | AddTree.negLeaf t => t
  | AddTree.node l r => AddTree.subNode l r
  | AddTree.subNode l r => AddTree.node l r

def AddTree.reduce {α : Type _} : AddTree (AddTree α) → AddTree α
  | AddTree.leaf adt => adt
  | AddTree.negLeaf adt => negate $ reduce adt
  | AddTree.node lt rt => AddTree.node (reduce lt) (reduce rt)
  | AddTree.subNode lt rt => AddTree.subNode (reduce lt) (reduce rt)

@[reducible, simp] def AddTree.map {α β : Type _} (f : α → β) : AddTree α → AddTree β
  | AddTree.leaf a => AddTree.leaf (f a)
  | AddTree.negLeaf a => AddTree.negLeaf (map f a)
  | AddTree.node l r => AddTree.node (map f l) (map f r)
  | AddTree.subNode l r => AddTree.subNode (map f l) (map f r)


/-
Reference:  Monads, partial evaluations, and rewriting by Tobias Fritz and Paulo Perrone
https://arxiv.org/pdf/1810.06037.pdf
-/

instance : Monad AddTree :=
  {
    pure := AddTree.leaf
    map := AddTree.map
    bind := λ adt f => (adt.map f).reduce
  }

-- instance : LawfulMonad AddTree := sorry


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
    | AddTree.leaf i => AddTree.leaf (basisImages.get (Fin.ofNat' i $ Nat.pos_of_ne_zero h))
    | AddTree.negLeaf τ => AddTree.negLeaf (map τ basisImages)
    | AddTree.node l r => AddTree.node (map l basisImages) (map r basisImages)
    | AddTree.subNode l r => AddTree.subNode (map l basisImages) (map r basisImages)

end IndexAddTree


section Reflection

def hOp (fname : Name) : Expr → MetaM (Expr × Expr)
  | e@(Expr.app (Expr.app _ a _) b _) => do
      guard $ e.isAppOf fname
      guard $ ← isDefEq (← inferType a) (← inferType e)
      guard $ ← isDefEq (← inferType b) (← inferType e)
      return (a, b)
  | _ => failure

def invOp (fname : Name) : Expr → MetaM Expr
 | e@(Expr.app _ a _) => do
    guard $ e.isAppOf fname
    guard $ ← isDefEq (← inferType a) (← inferType e)
    return a
 | _ => failure

partial def trieM (e : Expr) : MetaM Expr :=
    hOp ``HAdd.hAdd e >>= (λ (a, b) => return ← mkAppM ``AddTree.node #[← trieM a, ← trieM b])    <|>
    hOp ``HSub.hSub e >>= (λ (a, b) => return ← mkAppM ``AddTree.subNode #[← trieM a, ← trieM b]) <|>
    invOp ``Neg.neg e >>= (λ a => return ← mkAppM ``AddTree.negLeaf #[← trieM a])                 <|>
    mkAppM ``AddTree.leaf #[e]

elab "tree#" s:term : term => do
  let e ← Term.elabTerm s none
  trieM e

#check tree# ((2 + -3) - 1)

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

def elabTest : TermElabM Expr := do
  let s : Syntax ← `(2 + 3)
  addtreeM s .none

-- attribute [termElab addtreeElab] addtreeM -- adding the attribute in the usual way is not working, probably because the function is recursive and partial

end Reflection


theorem AddTree.fold_tree_map_eq {A B : Type _} [AddCommGroup A] [AddCommGroup B]
  (φ : A → B) [Homφ : AddCommGroup.Homomorphism φ] : (t : AddTree A) → φ t.fold = (t.map φ).fold := by 
    intro t
    induction t with
      | leaf a => rw [map, fold, fold] 
      | negLeaf a ih => rw [map, fold, fold, Homφ.neg_push, ih]
      | node l r ihl ihr => rw [map, fold, fold, Homφ.add_dist, ihl, ihr]
      | subNode l r ihl ihr => rw [map, fold, fold, Homφ.neg_dist, ihl, ihr]
