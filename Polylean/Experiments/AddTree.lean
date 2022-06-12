import Lean.Meta 
import Lean.Elab
import Mathlib.Algebra.Group.Defs
import Std
import Lean
open Lean Meta Elab Nat Term Std


def Lean.Expr.simplify(e: Expr) : MetaM Expr := do 
    let r ← simp e (← Simp.Context.mkDefault)
    return r.expr


def hOp? (fname: Name)(e : Expr)  : MetaM (Option (Expr × Expr)) := do
  let type ← inferType e
  if e.isAppOfArity fname 6 then
    let x := e.appFn!.appArg!
    let y := e.appArg!
    if (← isDefEq (← inferType x) type) &&
       (← isDefEq (← inferType y) type) then
      return some (x, y)
    else
      return none
  else
    return none

def invOp? (fname: Name)(e : Expr)  : MetaM (Option (Expr)) := do
  let type ← inferType e
  if e.isAppOfArity fname 4 then
    let y := e.appArg!
    if  (← isDefEq (← inferType y) type) then
      return some y
    else
      return none
  else
    return none

inductive AddTree (α : Type u)[Repr α] where
  | leaf : α → AddTree α 
  | negLeaf : α → AddTree α 
  | node : AddTree α  → AddTree α  → AddTree α 
  | subNode: AddTree α  → AddTree α  → AddTree α

def AddTree.fold {α : Type u}[AddCommGroup α][Repr α]  (t : AddTree α ) : α :=
  match t with
  | AddTree.leaf a => a
  | AddTree.node l r =>  (fold l) + (fold r)
  | AddTree.negLeaf a => -a
  | AddTree.subNode l r => (fold l) - (fold r)

def AddTree.foldMul {α : Type u}[CommGroup α][Repr α]  (t : AddTree α ) : α :=
  match t with
  | AddTree.leaf a => a
  | AddTree.node l r =>  (foldMul l) * (foldMul r)
  | AddTree.negLeaf a => a⁻¹ 
  | AddTree.subNode l r => (foldMul l) / (foldMul r)

abbrev IndexAddTree := AddTree Nat 

def AddTree.indexTree {α : Type u}[Repr α][DecidableEq α](t: AddTree α)
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
  | AddTree.negLeaf a => 
    match accum.getIdx? a with
    | some i => (AddTree.negLeaf i, accum)
    | none => (AddTree.negLeaf (accum.size), accum)
  | AddTree.subNode l r => 
    let (lIdx, lAccum) := indexTree l accum
    let (rIdx, rAccum) := indexTree r lAccum
    (AddTree.subNode lIdx rIdx, rAccum)

partial def treeM (e : Expr) : MetaM Expr := do
  match ← hOp? ``HAdd.hAdd e with
  | some (a, b) => do
    let l ← treeM a
    let r ← treeM b
    mkAppM ``AddTree.node #[l, r]
  | none  =>
  match ← hOp? ``HMul.hMul e with
  | some (a, b) => do
    let l ← treeM a
    let r ← treeM b
    mkAppM ``AddTree.node #[l, r]
  | none  =>
    match ← hOp? ``HSub.hSub e with
  | some (a, b) => do
    let l ← treeM a
    let r ← treeM b
    mkAppM ``AddTree.subNode #[l, r]
  | none  =>
  match ← hOp? ``HDiv.hDiv e with
  | some (a, b) => do
    let l ← treeM a
    let r ← treeM b
    mkAppM ``AddTree.subNode #[l, r]
  | none  =>
  match ← invOp? ``Neg.neg e with
  | some a => mkAppM ``AddTree.negLeaf #[e]
  | none  =>
  match ← invOp? ``Inv.inv e with
  | some a => mkAppM ``AddTree.negLeaf #[e]
  | none  =>
    mkAppM ``AddTree.leaf #[e]
