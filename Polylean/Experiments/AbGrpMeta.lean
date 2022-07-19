import Polylean.Experiments.AddTree
import Polylean.Experiments.FinGenFreeAbGroup
import Lean
open Lean Meta Elab Tactic Nat

/- Abstract the terms in the input list and create an iterated lambda term from the expression `e`. -/
def kabstractVars (e : Expr) : List Expr → MetaM Expr
  | [] => return e
  | v :: vars => do
    let e' ← kabstract e v -- abstract out the occurrences of the expression `v` in `e`
    let f := mkLambda Name.anonymous BinderInfo.default (← inferType v) e' -- create a λ-term from the above expression
    kabstractVars f vars

/- Convert an `AddTree` in the `Expr` form to an iterated lambda tree -/
def AddTree.toLambdaTree (adt : Expr) : MetaM Expr := do
  let leaves := List.eraseDups $ ← leavesM adt -- get the leaves of the tree
  let lambdaTree ← kabstractVars adt leaves -- abstract out the leaves of the tree to get an iterated lambda
  return lambdaTree
/- -- Experimental: Further generalization of the type
match (← inferType adt) with
    | .app _ typ _ => -- extract the type of the `AddTree`
      let abstractLambdaTree ← kabstract lambdaTree typ
      return mkForall Name.anonymous BinderInfo.default (mkSort $ mkLevelSucc $ mkLevelZeroEx ()) abstractLambdaTree
    | _ => failure
-/

elab "LambdaTree#" a:term : term => do
  let e ← Term.elabTerm a none
  let adt ← treeM e
  AddTree.toLambdaTree adt

#reduce (fun x y : ℤ => LambdaTree# (x + (y + x) - y)) _ _
-- Output: fun a a_1 => AddTree.subNode (AddTree.node (AddTree.leaf a_1) (AddTree.node (AddTree.leaf a) (AddTree.leaf a_1))) (AddTree.leaf a)

#reduce (fun (x y z : ℤ) => LambdaTree# x + y - z^2) _ _ _ -- here, `z^2` is treated as an atom since it does not use the additive group operations
-- Output: fun a a_1 a_2 => AddTree.subNode (AddTree.node (AddTree.leaf a_2) (AddTree.leaf a_1)) (AddTree.leaf a)

#reduce (fun (a b : ℤ^5) => LambdaTree# -(a + b - a - a + b)) _ _ -- Working with a group other than ℤ
-- Output: fun a a_1 => AddTree.negLeaf (AddTree.node (AddTree.subNode (AddTree.subNode (AddTree.node (AddTree.leaf a_1) (AddTree.leaf a)) (AddTree.leaf a_1)) (AddTree.leaf a_1)) (AddTree.leaf a))

variable {A : Type _} [AddCommGroup A]
#reduce (fun a b : A => LambdaTree# a + b - a + b) _ _ -- Working with an arbitrary Abelian group
-- Output: fun a a_1 => AddTree.node (AddTree.subNode (AddTree.node (AddTree.leaf a_1) (AddTree.leaf a)) (AddTree.leaf a_1)) (AddTree.leaf a)
