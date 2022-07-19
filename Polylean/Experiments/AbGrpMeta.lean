import Polylean.Experiments.AddTree
import Polylean.Experiments.FinGenFreeAbGroup
import Lean
open Lean Meta Elab Tactic Nat

def kabstractVars (e : Expr) : List Expr → MetaM Expr
  | [] => return e
  | v :: vars => do
    let e' ← kabstract e v
    let f := mkLambda Name.anonymous BinderInfo.default (← inferType v) e'
    kabstractVars f vars

def AddTree.toLambdaTree (adt : Expr) : MetaM Expr := do kabstractVars adt (List.eraseDups $ ← leavesM adt)

elab "LambdaTree#" a:term : term => do
  let e ← Term.elabTerm a none
  let adt ← treeM e
  AddTree.toLambdaTree adt

#reduce (fun x y : ℤ => LambdaTree# (x + (y + x) - y)) 0 0
-- Output:
-- fun a a_1 => AddTree.subNode (AddTree.node (AddTree.leaf a_1) (AddTree.node (AddTree.leaf a) (AddTree.leaf a_1))) (AddTree.leaf a)
