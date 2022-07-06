import Lean.Meta
import Lean.Elab
import Std
open Lean Meta Elab Term Std

namespace ProdSeq
/--
If an expression is a `PProd` (i.e., product of terms that may be proofs), returns the components of the product.
-/
def splitPProd? (expr: Expr) : TermElabM (Option (Expr × Expr)) :=
  do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (mkSort u)
    let β  ← mkFreshExprMVar (mkSort v)
    let a ← mkFreshExprMVar α 
    let b ← mkFreshExprMVar β 
    let f := mkAppN (Lean.mkConst ``PProd.mk [u, v]) #[α, β, a, b]
    if ← isDefEq f expr
      then
        Term.synthesizeSyntheticMVarsNoPostponing
        return some (← whnf a, ← whnf b)
      else 
        return none

/--
If an expression is a product of terms (which cannot be proofs), returns the components of the product.
-/
def splitProd?(expr: Expr) : TermElabM (Option (Expr × Expr)) :=
  do
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (mkSort (mkLevelSucc u))
    let β  ← mkFreshExprMVar (mkSort (mkLevelSucc v))
    let a ← mkFreshExprMVar α 
    let b ← mkFreshExprMVar β 
    let f := mkAppN (Lean.mkConst ``Prod.mk [u, v]) #[α, β, a, b]
    if ← isDefEq f expr
      then
        Term.synthesizeSyntheticMVarsNoPostponing
        return some (← whnf a, ← whnf b)
      else 
        return none

/--
If an expression is either a `PProd` (i.e., product of terms that may be proofs) or a product, returns the components.
-/
def split? (expr: Expr) : TermElabM (Option (Expr × Expr)) :=
    do
      let h? ← splitPProd? expr 
      let hp? ← splitProd? expr
      return h?.orElse (fun _ => hp?)

/--
serializes a list of expressions using `PProd` recursively.
-/
def pack : List Expr →  TermElabM Expr 
  | [] => return mkConst ``Unit.unit
  | x :: ys => 
    do
      let t ← pack ys
      let expr ← mkAppM `PProd.mk #[x, t]
      return expr

/--
serializes a list of expressions using products recursively - it is assumed that the expressions do not represent proofs.
-/
def packTerms : List Expr →  TermElabM Expr 
  | [] => return mkConst ``Unit.unit
  | x :: ys => 
    do
      let t ← packTerms ys
      if ← isProof x 
      then return t  
      else 
        let expr ← mkAppM `Prod.mk #[x, t]
        return expr

/--
deserialize a list of exressions; where the serialization can use `PProd` or products.
-/
partial def unpack (expr: Expr) : TermElabM (List Expr) :=
    do
      match (← split? expr) with
      | some (h, t) => return h :: (← unpack t) 
      | none =>
        do 
        unless (← isDefEq expr (mkConst `Unit.unit))
          do throwError m!"{expr} is neither product nor unit" 
        return []

infixr:65 ":::" => PProd.mk

def mkPair(e₁ e₂ : Expr) : MetaM Expr :=
  mkAppM  ``PProd.mk  #[e₁, e₂]

end ProdSeq
