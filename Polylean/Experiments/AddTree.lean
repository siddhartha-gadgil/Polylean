import Lean.Meta 
import Lean.Elab
import Mathlib.Algebra.Group.Defs
import Polylean.Experiments.Tactics
import Std
import Lean
open Lean Meta Elab Nat Term Std


def Lean.Expr.simplify(e: Expr) : MetaM Expr := do 
    let r ← simp e (← Simp.Context.mkDefault)
    return r.expr


def hOp? (fname: Name)(e : Expr)  : MetaM (Option (Expr × Expr)) := do
  let type ← inferType e
  if e.isAppOfArity fname 6 then
    let x := e.appFn!.appArg!
    let y := e.appArg!
    if (← isDefEq (← inferType x) type) &&
       (← isDefEq (← inferType y) type) then
      return some (x, y)
    else
      return none
  else
    return none

def invOp? (fname: Name)(e : Expr)  : MetaM (Option (Expr)) := do
  let type ← inferType e
  if e.isAppOfArity fname 4 then
    let y := e.appArg!
    if  (← isDefEq (← inferType y) type) then
      return some y
    else
      return none
  else
    return none

inductive AddTree (α : Type u)[Repr α] where
  | leaf : α → AddTree α 
  | negLeaf : α → AddTree α 
  | node : AddTree α  → AddTree α  → AddTree α 
  | subNode: AddTree α  → AddTree α  → AddTree α

def AddTree.fold {α : Type u}[AddCommGroup α][Repr α]  (t : AddTree α ) : α :=
  match t with
  | AddTree.leaf a => a
  | AddTree.node l r =>  (fold l) + (fold r)
  | AddTree.negLeaf a => -a
  | AddTree.subNode l r => (fold l) - (fold r)

def AddTree.foldMul {α : Type u}[CommGroup α][Repr α]  (t : AddTree α ) : α :=
  match t with
  | AddTree.leaf a => a
  | AddTree.node l r =>  (foldMul l) * (foldMul r)
  | AddTree.negLeaf a => a⁻¹ 
  | AddTree.subNode l r => (foldMul l) / (foldMul r)

abbrev IndexAddTree := AddTree Nat 

@[simp, reducible] def AddTree.indexTree {α : Type u}[Repr α][DecidableEq α](t: AddTree α)
  (accum : Array α := #[]) : 
      IndexAddTree × (Array α) := 
  match t with
  | AddTree.leaf a => 
    match accum.getIdx? a with
    | some i => (AddTree.leaf i, accum)
    | none => (AddTree.leaf (accum.size), accum.push a)
  | AddTree.node l r =>  
    let (lIdx, lAccum) := indexTree l accum
    let (rIdx, rAccum) := indexTree r lAccum
    (AddTree.node lIdx rIdx, rAccum)
  | AddTree.negLeaf a => 
    match accum.getIdx? a with
    | some i => (AddTree.negLeaf i, accum)
    | none => (AddTree.negLeaf (accum.size), accum.push a)
  | AddTree.subNode l r => 
    let (lIdx, lAccum) := indexTree l accum
    let (rIdx, rAccum) := indexTree r lAccum
    (AddTree.subNode lIdx rIdx, rAccum)

@[simp, reducible] def AddTree.indexTree₀  {α : Type u}[Repr α][DecidableEq α](t: AddTree α) := t.indexTree #[]

lemma Array.size_pos_if_index {α : Type _} [DecidableEq α] {arr : Array α} {a : α} {i : ℕ} : arr.getIdx? a = some i → arr.size > 0 := by
  rw [getIdx?, findIdx?, findIdx?.loop]
  exact if h:0 < arr.size then
    λ _ => h
  else by simp [h]

lemma Array.push_size_pos {α : Type _} (arr : Array α) (a : α) : (arr.push a).size > 0 := by
  match arr with
    | ⟨l⟩ =>
      simp only [push, size]
      induction l with
        | nil => simp only [List.concat, List.length]
        | cons _ _ _ => simp only [List.concat, List.length, Nat.add_one]; apply Nat.succ_pos

theorem pos_size {α : Type u}[Repr α][DecidableEq α] (t: AddTree α) : (arr : Array α) → (t.indexTree arr).2.size > 0 := by
  induction t with
    | leaf a =>
      simp only [AddTree.indexTree]
      intro arr
      match h:arr.getIdx? a with
        | some i => simp only [h]; exact Array.size_pos_if_index h
        | none => simp only [h]; apply Array.push_size_pos
    | negLeaf a =>
      simp only [AddTree.indexTree]
      intro arr
      match h:arr.getIdx? a with
        | some i => simp only [h]; exact Array.size_pos_if_index h
        | none => simp only [h]; apply Array.push_size_pos
    | node _ _ _ ihr => simp only [AddTree.indexTree]; intro arr; apply ihr
    | subNode _ _ _ ihr => simp only [AddTree.indexTree]; intro arr; apply ihr

partial def treeM (e : Expr) : MetaM Expr := do
  match ← hOp? ``HAdd.hAdd e with
  | some (a, b) => do
    let l ← treeM a
    let r ← treeM b
    mkAppM ``AddTree.node #[l, r]
  | none  =>
  match ← hOp? ``HMul.hMul e with
  | some (a, b) => do
    let l ← treeM a
    let r ← treeM b
    mkAppM ``AddTree.node #[l, r]
  | none  =>
    match ← hOp? ``HSub.hSub e with
  | some (a, b) => do
    let l ← treeM a
    let r ← treeM b
    mkAppM ``AddTree.subNode #[l, r]
  | none  =>
  match ← hOp? ``HDiv.hDiv e with
  | some (a, b) => do
    let l ← treeM a
    let r ← treeM b
    mkAppM ``AddTree.subNode #[l, r]
  | none  =>
  match ← invOp? ``Neg.neg e with
  | some a => mkAppM ``AddTree.negLeaf #[a]
  | none  =>
  match ← invOp? ``Inv.inv e with
  | some a => mkAppM ``AddTree.negLeaf #[a]
  | none  =>
      mkAppM ``AddTree.leaf #[e]

@[simp] def IndexAddTree.foldMap {α : Type u}[AddCommGroup α][Repr α] 
  (t : IndexAddTree)(basisImages: Array α)(h: basisImages.size > 0) : α :=
  match t with
  | AddTree.leaf i => basisImages.get (Fin.ofNat' i h)
  | AddTree.node l r =>
      let lImage := foldMap l basisImages h
      let rImage := foldMap r basisImages h  
      lImage + rImage
  | AddTree.negLeaf i => -basisImages.get (Fin.ofNat' i h)
  | AddTree.subNode l r => 
      let lImage := foldMap l basisImages h
      let rImage := foldMap r basisImages h  
      lImage - rImage

@[simp] def foldPair{α : Type u}[AddCommGroup α][Repr α] 
  (tb : IndexAddTree × Array α)(h: tb.snd.size > 0) : α  := 
  let (t, basisImages) := tb
  t.foldMap basisImages h

@[simp] def IndexAddTree.foldMapMul {α : Type u}[CommGroup α][Repr α] 
  (t : IndexAddTree)(basisImages: Array α)(h: basisImages.size > 0) : α :=
  match t with
  | AddTree.leaf i => basisImages.get (Fin.ofNat' i h)
  | AddTree.node l r =>
      let lImage := foldMapMul l basisImages h
      let rImage := foldMapMul r basisImages h  
      lImage * rImage
  | AddTree.negLeaf i => (basisImages.get (Fin.ofNat' i h))⁻¹
  | AddTree.subNode l r => 
      let lImage := foldMapMul l basisImages h
      let rImage := foldMapMul r basisImages h  
      lImage / rImage

elab "indexTree#" t:term : term => do
  let e ← elabTerm t none
  let t ← treeM e
  mkAppM ``AddTree.indexTree₀ #[t]

@[simp] def egInd {α : Type u}[AddCommGroup α][Repr α][DecidableEq α] (x y: α) := 
    indexTree# (x + y + x - y)
