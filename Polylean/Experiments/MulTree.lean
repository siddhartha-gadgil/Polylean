import Lean.Meta 
import Lean.Elab
import Mathlib.Algebra.Group.Defs
import Std
import Lean
open Lean Meta Elab Nat Term Std


def Lean.Expr.simplify(e: Expr) : MetaM Expr := do 
    let r ← simp e (← Simp.Context.mkDefault)
    return r.expr


def mul? (e : Expr)  : MetaM (Option (Expr × Expr)) := do
  let type ← inferType e
  if e.isAppOfArity ``HMul.hMul 6 then
    let x := e.appFn!.appArg!
    let y := e.appArg!
    if (← isDefEq (← inferType x) type) &&
       (← isDefEq (← inferType y) type) then
      return some (x, y)
    else
      return none
  else
    return none

elab "splitmul#" s:term : term => do 
  let e ← Term.elabTerm s none
  let e ← e.simplify
  let r ← mul? e
  Term.synthesizeSyntheticMVarsNoPostponing
  let r' := r.get!
  let (a, b) := r'
  mkAppM ``Prod.mk #[a, b]

def prodFn(n m: Nat) := splitmul# (n * (m + 2)) 

#print prodFn

inductive MulTree (α : Type u)[HMul α α α][Repr α] where
  | leaf : α → MulTree α 
  | node : MulTree α  → MulTree α  → MulTree α 

def MulTree.fold {α : Type u}[HMul α α α][Repr α]  (t : MulTree α ) : α :=
  match t with
  | MulTree.leaf a => a
  | MulTree.node l r =>  (fold l) * (fold r)
  
partial def treeM (e : Expr) : MetaM Expr := do
  match ← mul? e with
  | none  => mkAppM ``MulTree.leaf #[e]
  | some (a, b) => do
    let l ← treeM a
    let r ← treeM b
    mkAppM ``MulTree.node #[l, r]

elab "tree#" s:term : term => do 
  let e ← Term.elabTerm s none
  treeM e

def egTree(n m: Nat)  := tree# ((n * m) * (m + 2))

#print egTree

#eval MulTree.fold <| egTree 2 3

def egTreeInv(n m: Nat) := (egTree n m).fold

example (n m: Nat) : egTreeInv n m = (n * m) * (m + 2) := rfl