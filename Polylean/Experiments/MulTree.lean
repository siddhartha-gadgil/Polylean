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

def MulTree.leafCount {α : Type _} [HMul α α α] [Repr α] : MulTree α → ℕ
  | MulTree.leaf _ => Nat.zero.succ
  | MulTree.node l r => leafCount l + leafCount r

def MulTree.left {α : Type _} [HMul α α α] [Repr α] : MulTree α → α
  | MulTree.leaf lf => lf
  | MulTree.node l _ => left l

def MulTree.right {α : Type _} [HMul α α α] [Repr α] : MulTree α → α
  | MulTree.leaf lf => lf
  | MulTree.node _ r => right r

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



section treeexperiments

def t₁ : MulTree Nat := -- tree# (2 * (3 * 5))
 MulTree.node (MulTree.leaf 2) (MulTree.node (MulTree.leaf 3) (MulTree.leaf 5))

def t₂ : MulTree Nat :=
  MulTree.node (MulTree.leaf 6) (MulTree.leaf 5)

theorem prodeq : 2 * (3 * 5) = 6 * 5 := rfl

theorem prodred : 6 * 5 = 30 := rfl

theorem foldeq : t₁.fold = t₂.fold := rfl

end treeexperiments

open MulTree in
def Group.reduce {G : Type _} [Group G] [DecidableEq G] [Repr G] : (mt : MulTree G) → {μt : MulTree G // mt.fold = μt.fold}
  | leaf lf => ⟨leaf lf, rfl⟩
  | node l r =>
    if h:(l.right * r.left = (1 : G)) then
      match l, r with
        | leaf lf, leaf rf => ⟨leaf (1 : G), h⟩
        | node ll lr, r => ⟨node ll (node lr r), by apply mul_assoc⟩
        | l, node rl rr => ⟨node (node l rl) rr, by apply Eq.symm; apply mul_assoc⟩
    else
      match reduce l, reduce r with
        | ⟨l_, eql⟩, ⟨r_, eqr⟩ => ⟨node l_ r_, by
                                  repeat (rw [MulTree.fold])
                                  rw [eql, eqr]⟩
