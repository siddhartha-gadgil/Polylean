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

#check Eq.refl

@[simp] def inducedFreeMap!{A: Type _}[AddCommGroup A](l: List A) :=
    @inducedFreeMap A _ l.length l rfl

instance ind_hom! {A : Type _} [AddCommGroup A]  (l : List A)  : AddCommGroup.Homomorphism (inducedFreeMap! l) := FreeAbelianGroup.induced_hom A _

def viaFreeM (e: Expr) : TermElabM Expr := do
  let t ← addTreeM e
  let (indTree, lst) ← AddTree.indexTreeM'' t
  let lstPackPair ←  listToExpr lst
  let (lstPack, α) := lstPackPair
  let pf ← mkAppM ``Eq.refl #[toExpr lst.length]
  let arr ←  ℤbasisArrM (lst.length)
  let freeElem ← IndexAddTree.foldMapM indTree arr
  let fromFree ← mkAppOptM 
      ``inducedFreeMap #[some α, none, some <| toExpr lst.length, some lstPack, some (pf)]
  mkAppM' fromFree #[freeElem]

elab "viafree#" t:term : term => do
  let e ← elabTerm t none
  viaFreeM e

def egViaFree {α : Type}[AddCommGroup α][Repr α][DecidableEq α][Inhabited α] 
    (x y : α) := viafree# (x + y + x - y + x + y)

#eval egViaFree (5 : ℤ) (2 : ℤ )

theorem induced_free_map_at{A : Type _} [AddCommGroup A][Inhabited A] {n : ℕ} (l : List A) (h : l.length = n)(k: ℕ) : 
  (inducedFreeMap l h) (ℤbasisElem n k) = (l.toArray)[k] := sorry

theorem egViaFreeEql{α : Type}[AddCommGroup α][Repr α][DecidableEq α][Inhabited α] 
    (x y : α) : x + y + x - y =  viafree# (x + y + x - y)  := by 
        simp
        have l₀ : (inducedFreeMap [x, y] (rfl: 2 = 2)) (ℤbasisElem 2 0) = x  := induced_free_map_at [x, y] rfl 0
        have l₁ :  (inducedFreeMap [x, y] (rfl: 2 = 2)) (ℤbasisElem 2 1) = y := induced_free_map_at [x, y] rfl 1
        rw [l₀, l₁]
        

