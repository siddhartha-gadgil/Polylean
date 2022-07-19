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

def AddTree.toLambdaTree (adt : Expr) : MetaM Expr := do kabstractVars adt (← leavesM adt)

elab "LambdaTree#" a:term : term => do
  let e ← Term.elabTerm a none
  let adt ← treeM e
  let vrs ← AddTree.leavesM adt
  AddTree.toLambdaTree adt

#eval LambdaTree# (2 + (3 : ℤ))
