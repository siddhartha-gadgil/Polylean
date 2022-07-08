import Lean.Meta 
import Lean.Elab
import Mathlib.Algebra.Group.Defs
import Polylean.Experiments.Tactics
import Std
import Lean
import Polylean.ProdSeq
import Polylean.Experiments.GeneralAbelianGroup
open Lean Meta Elab Nat Term Std ProdSeq ToExpr

instance (n: ℕ) : Inhabited (ℤ ^ n) := ⟨zeros n⟩

def ℤbasisElem(n : ℕ)(j : ℕ) : ℤ ^ n := (ℤbasis n |>.toArray)[j]

elab "ℤbasisElem#"  n:term "at" j:term  : term => do
      let nExp ← elabTerm n (some <| mkConst ``Nat)
      let jExp ← elabTerm j (some <| mkConst ``Nat)
      mkAppM ``ℤbasisElem #[nExp, jExp]

#eval ℤbasisElem# 3 at 1

def ℤbasisArrM (n: ℕ): MetaM (Array Expr) := do
  let mut arr := #[]
  for j in [0:n] do
    arr := arr.push (← mkAppM ``ℤbasisElem #[toExpr n, toExpr j])
  return arr

elab "arr#"  n:term "at" j:term  : term => do
      let nExp ← elabTerm n (some <| mkConst ``Nat)
      let jExp ← elabTerm j (some <| mkConst ``Nat)
      let n' ← exprNat nExp
      let j' ← exprNat jExp
      let arr ← ℤbasisArrM n'
      return arr[j']

#eval arr# 7 at 2

def toFreeM (e : Expr) : TermElabM Expr := do
  let t ← addTreeM e
  let (indTree, lst) ← AddTree.indexTreeM'' t
  let arr ←  ℤbasisArrM (lst.length)
  IndexAddTree.foldMapM indTree arr

elab "free#" t:term : term => do
  let e ← elabTerm t none
  toFreeM e

def egFree {α : Type u}[AddCommGroup α][Repr α][DecidableEq α][Inhabited α] 
    (x y : α) := free# (x + y + x - y + x + y)

#eval egFree (5 : ℤ) (2 : ℤ )

#check @inducedFreeMap

def inducedFreeMap!{A: Type}[AddCommGroup A](l: List A) :=
    @inducedFreeMap A _ l.length l rfl

def viaFreeM (e: Expr) : TermElabM Expr := do
  let t ← addTreeM e
  let (indTree, lst) ← AddTree.indexTreeM'' t
  let arr ←  ℤbasisArrM (lst.length)
  let freeElem ← IndexAddTree.foldMapM indTree arr
  let lstPackPair ←  listToExpr lst
  let (lstPack, α) := lstPackPair
  let fromFree ← mkAppOptM ``inducedFreeMap! #[some α, none, some lstPack]
  mkAppM' fromFree #[freeElem]

elab "viafree#" t:term : term => do
  let e ← elabTerm t none
  viaFreeM e

def egViaFree {α : Type}[AddCommGroup α][Repr α][DecidableEq α][Inhabited α] 
    (x y : α) := viafree# (x + y + x - y + x + y)

#eval egViaFree (5 : ℤ) (2 : ℤ )
