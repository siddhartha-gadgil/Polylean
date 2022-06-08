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