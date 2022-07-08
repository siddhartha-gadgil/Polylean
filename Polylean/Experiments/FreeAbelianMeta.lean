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

def ℤbasisElem (n : ℕ) (j : ℕ) (h : j < n) : ℤ ^ n := ℤbasis n |>.get ⟨j, by simp [h]⟩

section ToExpr

instance : ToExpr Int where
  toExpr :=
    fun
      | Int.ofNat n => mkApp (mkConst ``Int.ofNat) $ toExpr n
      | Int.negSucc n => mkApp (mkConst ``Int.negSucc) $ toExpr n
  toTypeExpr := mkConst ``Int

instance prodToExpr {A B : Type _} [ToExpr A] [ToExpr B] : ToExpr (A × B) := inferInstance

instance : ToExpr Unit where
  toExpr := fun | Unit.unit => mkConst ``Unit.unit
  toTypeExpr := mkConst ``Unit

@[instance] def powToExpr {A : Type _} [ToExpr A] : (n : ℕ) → ToExpr (A ^ n)
  | .zero => inferInstanceAs (ToExpr Unit)
  | .succ m => @prodToExpr _ _ inferInstance $ powToExpr m

instance {α : Type _} [ToExpr α] : ToExpr (List α) where
  toExpr :=
    let rec lstexpr : List α → Expr
      | .nil => mkConst ``List.nil
      | .cons h t => mkApp (mkApp (mkConst ``List.cons) $ toExpr h) $ lstexpr t
    lstexpr
  toTypeExpr := mkApp (mkConst ``List) $ toTypeExpr α

end ToExpr

section Decidable

-- Source : https://exlean.org/decidable-propositions-iii/

def asTrue (C : Prop) [Decidable C] : Prop :=
  if C then True else False

def ofAsTrue {C : Prop} : [Decidable C] → asTrue C → C
  | .isTrue c => λ _ => c
  | .isFalse _ => False.elim

notation "decTrivial" => ofAsTrue trivial

example : 2 < 5 := decTrivial

def decideM : MetaM Expr := mkAppM ``ofAsTrue #[mkConst ``trivial]

end Decidable

def zeroExpr : ℕ → TermElabM Expr
| 0 => return mkConst ``Unit.unit
| n + 1 => do mkAppM ``Prod.mk #[toExpr (0 : Int), ←  zeroExpr n]

def ℤbasisExpr : ℕ → ℕ → TermElabM Expr
| 0, _ => return mkConst ``Unit.unit
| n + 1, 0 => do mkAppM ``Prod.mk #[toExpr (1 : Int), ←  zeroExpr n]
| n + 1, k + 1 => do mkAppM ``Prod.mk #[toExpr (1 : Int), ← ℤbasisExpr n k]

elab "ℤbasisElem#"  n:term "at" j:term  : term => do
      let nExp ← elabTerm n (some <| mkConst ``Nat)
      let jExp ← elabTerm j (some <| mkConst ``Nat)
      mkAppM ``ℤbasisElem #[nExp, jExp, ← decideM]

elab "ℤbasisExpr#"  n:term "at" j:term  : term => do
      let nExp ← elabTerm n (some <| mkConst ``Nat)
      let jExp ← elabTerm j (some <| mkConst ``Nat)
      let n ← exprNat nExp
      let j ← exprNat jExp
      ℤbasisExpr n j

-- #eval ℤbasisElem# 3 at 1
#eval ℤbasisExpr# 3 at 1

def ℤbasisArrM (n: ℕ): TermElabM (Array Expr) := do
  let mut arr := #[]
  for j in [0:n] do
    arr := arr.push (← mkAppM ``ℤbasisElem #[toExpr n, toExpr j, ← decideM])
    -- arr := arr.push (← ℤbasisExpr n j)
  return arr

-- def ℤbasisArrM (n: ℕ): TermElabM (Array Expr) := do
--  return ℤbasis n |>.map toExpr |>.toArray

elab "arr#"  n:term "at" j:term  : term => do
      let nExp ← elabTerm n (some <| mkConst ``Nat)
      let jExp ← elabTerm j (some <| mkConst ``Nat)
      let n' ← exprNat nExp
      let j' ← exprNat jExp
      let arr ← ℤbasisArrM n'
      return arr[j']

-- #eval arr# 7 at 2

def toFreeM (e : Expr) : TermElabM Expr := do
  let t ← addTreeM e
  let (indTree, lst) ← AddTree.indexTreeM'' t
  let arr ←  ℤbasisArrM (lst.length)
  IndexAddTree.foldMapM indTree arr

elab "free#" t:term : term => do
  let e ← elabTerm t none
  toFreeM e

-- def egFree {α : Type u}[AddCommGroup α][Repr α][DecidableEq α][Inhabited α]
--    (x y : α) := free# (x + y + x - y + x + y)

-- #eval egFree (5 : ℤ) (2 : ℤ )

def provedLength{α : Type}(l: List α) : PSigma (fun n : ℕ  => l.length = n) := PSigma.mk (l.length) rfl


@[simp] def inducedFreeMap!{A: Type _}[AddCommGroup A](l: List A) :=
    @inducedFreeMap A _ l.length l rfl

instance ind_hom! {A : Type _} [AddCommGroup A]  (l : List A)  : AddCommGroup.Homomorphism (inducedFreeMap! l) := FreeAbelianGroup.induced_hom A _

def viaFreeM (e: Expr) : TermElabM Expr := do
  let t ← addTreeM e
  let (indTree, lst) ← AddTree.indexTreeM'' t
  let lstPackPair ←  listToExpr lst
  let (lstPack, α) := lstPackPair
  let pl ← mkAppM ``provedLength #[lstPack]
  let n ← exprNat (← mkAppM ``PSigma.fst #[pl])
  let pf ← mkAppM ``PSigma.snd #[pl]
  let pf' ← mkAppOptM 
      ``Eq.trans #[none, none, none, toExpr n, pf, 
        ← mkAppM ``Eq.refl #[toExpr n]]
  let n := lst.length
  let pf ← mkAppM ``Eq.refl #[toExpr lst.length]
  let arr ←  ℤbasisArrM n
  let freeElem ← IndexAddTree.foldMapM indTree arr
  let fromFree ← mkAppOptM 
      ``inducedFreeMap #[some α, none, some <| toExpr n, some lstPack, some (pf')]
  mkAppM' fromFree #[freeElem]

elab "viafree#" t:term : term => do
  let e ← elabTerm t none
  viaFreeM e

-- def egViaFree {α : Type}[AddCommGroup α][Repr α][DecidableEq α][Inhabited α]
--    (x y : α) := viafree# (x + y + x - y + x + y)

-- #eval egViaFree (5 : ℤ) (2 : ℤ )

theorem induced_free_map_at{A : Type _} [AddCommGroup A] {n : ℕ} (l : List A) (h : l.length = n) (k: ℕ) (hk : k < n) :
 (inducedFreeMap l h) (ℤbasisElem n k hk) = l.get ⟨k, h ▸ hk⟩ := by
   rw [ℤbasisElem, List.mapget (inducedFreeMap l h)]
   apply List.get_index_eq
   apply map_basis

/-
open AddCommGroup.Homomorphism
theorem egViaFreeEql{α : Type}[AddCommGroup α][Repr α][DecidableEq α][Inhabited α] 
    (x y : α) : x + y + x - y =  viafree# (x + y + x - y)  := by
        simp only [neg_dist, AddCommGroup.add_distrib, induced_free_map_at]
        have l₀ : #[x, y].getOp 0 = x := by rfl
        have l₁ : #[x, y].getOp 1 = y := by rfl
        -- rw[l₀, l₁]
        admit

#print egViaFreeEql
-/
