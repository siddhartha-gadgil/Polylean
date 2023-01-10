import Lean.Meta 
import Lean.Elab
import Mathlib.Algebra.Group.Defs
import Polylean.Tactics.ReduceGoal
import Std
import Lean
import Polylean.Experiments.ProdSeq
open Lean Meta Elab Nat Term Std ProdSeq


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

inductive AddTree (α : Type _)[Repr α] where
  | leaf : α → AddTree α 
  | negLeaf : α → AddTree α 
  | node : AddTree α  → AddTree α  → AddTree α 
  | subNode: AddTree α  → AddTree α  → AddTree α

def AddTree.fold {α : Type _}[AddCommGroup α][Repr α]  (t : AddTree α ) : α :=
  match t with
  | AddTree.leaf a => a
  | AddTree.node l r =>  (fold l) + (fold r)
  | AddTree.negLeaf a => -a
  | AddTree.subNode l r => (fold l) - (fold r)

def AddTree.foldMul {α : Type _}[CommGroup α][Repr α]  (t : AddTree α ) : α :=
  match t with
  | AddTree.leaf a => a
  | AddTree.node l r =>  (foldMul l) * (foldMul r)
  | AddTree.negLeaf a => a⁻¹ 
  | AddTree.subNode l r => (foldMul l) / (foldMul r)

abbrev IndexAddTree := AddTree Nat 

@[inline] def AddTree.indexTree {α : Type _}[Repr α][DecidableEq α](t: AddTree α)
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

def AddTree.indexTreeM (t: AddTree Expr)(accumExpr : Expr) : 
      TermElabM Expr := do
  let accumL ← unpack accumExpr
  let accum := accumL.toArray
  match t with
  | AddTree.leaf a => 
    match ← accum.findIdxM? fun e => isDefEq e a with
    | some i => 
      mkPair (← mkAppM ``AddTree.leaf #[ToExpr.toExpr i]) accumExpr
    | none =>
      let newAccum ← pack (accum.push a).toList 
      mkPair (← mkAppM ``AddTree.leaf #[ToExpr.toExpr accum.size]) newAccum
  | AddTree.node l r =>
    let lexpr ← indexTreeM l accumExpr
    let (lIdx, lAccum) := (← split? lexpr).get!
    let rexpr ← indexTreeM r lAccum
    let (rIdx, rAccum) := (← split? rexpr).get!
    mkPair (← mkAppM ``AddTree.node #[lIdx, rIdx]) (rAccum)
  | AddTree.negLeaf a => 
    match ← accum.findIdxM? fun e => isDefEq e a with
    | some i => 
        mkPair (← mkAppM ``AddTree.negLeaf #[ToExpr.toExpr i]) accumExpr
    | none => 
      let newAccum ← pack (accum.push a).toList 
      mkPair (← mkAppM ``AddTree.leaf #[ToExpr.toExpr accum.size]) newAccum
  | AddTree.subNode l r => 
    let lexpr ← indexTreeM l accumExpr
    let (lIdx, lAccum) := (← split? lexpr).get!
    let rexpr ← indexTreeM r lAccum
    let (rIdx, rAccum) := (← split? rexpr).get!
    mkPair (← mkAppM ``AddTree.subNode #[lIdx, rIdx]) (rAccum)


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


@[irreducible] theorem pos_size {α : Type _}[Repr α][DecidableEq α] (t: AddTree α) : (arr : Array α) → (t.indexTree arr).2.size > 0 := by
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

partial def addTreeM (e : Expr) : MetaM <| AddTree Expr := do
  match ← hOp? ``HAdd.hAdd e with
  | some (a, b) => do
    let l ← addTreeM a
    let r ← addTreeM b
    return AddTree.node l r
  | none  =>
  match ← hOp? ``HMul.hMul e with
  | some (a, b) => do
    let l ← addTreeM a
    let r ← addTreeM b
    return AddTree.node l r
  | none  =>
    match ← hOp? ``HSub.hSub e with
  | some (a, b) => do
    let l ← addTreeM a
    let r ← addTreeM b
    return AddTree.subNode l r
  | none  =>
  match ← hOp? ``HDiv.hDiv e with
  | some (a, b) => do
    let l ← addTreeM a
    let r ← addTreeM b
    return AddTree.subNode l r
  | none  =>
  match ← invOp? ``Neg.neg e with
  | some a => return AddTree.negLeaf a
  | none  =>
  match ← invOp? ``Inv.inv e with
  | some a => return AddTree.negLeaf a
  | none  =>
      return AddTree.leaf e

@[simp] def IndexAddTree.foldMap {α : Type _}[AddCommGroup α][Repr α] 
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

@[simp] def IndexAddTree.foldMap! {α : Type _}[AddCommGroup α][Repr α][Inhabited α] 
  (t : IndexAddTree)(basisImages: Array α) : α :=
  match t with
  | AddTree.leaf i => basisImages.get! i
  | AddTree.node l r =>
      let lImage := foldMap! l basisImages 
      let rImage := foldMap! r basisImages   
      lImage + rImage
  | AddTree.negLeaf i => -basisImages.get! i 
  | AddTree.subNode l r => 
      let lImage := foldMap! l basisImages 
      let rImage := foldMap! r basisImages   
      lImage - rImage

def IndexAddTree.foldMapMAux 
  (t : IndexAddTree)(basisImages: Array Expr) : TermElabM Expr := do
  match t with
  | AddTree.leaf i => return basisImages.get! i
  | AddTree.node l r => 
      let lImage ←  foldMapMAux l basisImages 
      let rImage ←  foldMapMAux r basisImages   
      mkAppM ``HAdd.hAdd #[lImage, rImage]
  | AddTree.negLeaf i => mkAppM ``Neg.neg #[basisImages.get! i] 
  | AddTree.subNode l r => 
      let lImage ←  foldMapMAux l basisImages 
      let rImage ←  foldMapMAux r basisImages   
      mkAppM ``HSub.hSub #[lImage, rImage]


partial def exprNatLeaf : Expr → TermElabM (Option Nat) := fun expr => 
  do
    let mvar ←  mkFreshExprMVar (some (mkConst ``Nat))
    let sExp' ← mkAppM ``AddTree.leaf #[mvar]
    let expr ← reduce expr
    Term.synthesizeSyntheticMVarsNoPostponing
    if ← isDefEq sExp' expr then
      Term.synthesizeSyntheticMVarsNoPostponing
      let index ← exprNat (← whnf mvar)
      return some index
    else 
      return none

partial def exprNatNegLeaf : Expr → TermElabM (Option Nat) := fun expr => 
  do
    let mvar ←  mkFreshExprMVar (some (mkConst ``Nat))
    let sExp' ← mkAppM ``AddTree.negLeaf #[mvar]
    let expr ← reduce expr
    Term.synthesizeSyntheticMVarsNoPostponing
    if ← isDefEq sExp' expr then
      Term.synthesizeSyntheticMVarsNoPostponing
      let index ← exprNat (← whnf mvar)
      return some index
    else 
      return none
  
elab "leafIndex!" t: term : term => do
  let e ← elabTerm t none
  let e ← reduce e
  let n? ← exprNatLeaf e
  return (ToExpr.toExpr <| n?.get!)


#eval leafIndex! (AddTree.leaf 7)

partial def exprNode : Expr → TermElabM (Option (Expr × Expr)) := fun expr => 
  do
    let mvar ←  mkFreshExprMVar (some (mkConst ``IndexAddTree))
    let mvar' ←  mkFreshExprMVar (some (mkConst ``IndexAddTree))
    let sExp' ← mkAppM ``AddTree.node #[mvar, mvar']
    let expr ← reduce expr
    Term.synthesizeSyntheticMVarsNoPostponing
    if ← isDefEq sExp' expr then
      Term.synthesizeSyntheticMVarsNoPostponing
      return some (mvar, mvar')
    else 
      return none

partial def exprSubNode : Expr → TermElabM (Option (Expr × Expr)) := fun expr => 
  do
    let mvar ←  mkFreshExprMVar (some (mkConst ``IndexAddTree))
    let mvar' ←  mkFreshExprMVar (some (mkConst ``IndexAddTree))
    let sExp' ← mkAppM ``AddTree.subNode #[mvar, mvar']
    let expr ← reduce expr
    Term.synthesizeSyntheticMVarsNoPostponing
    if ← isDefEq sExp' expr then
      Term.synthesizeSyntheticMVarsNoPostponing
      return some (mvar, mvar')
    else 
      return none

partial def exprIndexTree : Expr → TermElabM IndexAddTree := fun expr => 
  do
    match ← exprNode expr with
    | some (l, r) => do
      let l ← exprIndexTree l
      let r ← exprIndexTree r
      return AddTree.node l r
    | none  =>
      match ← exprSubNode expr with
    | some (l, r) => do
      let l ← exprIndexTree l
      let r ← exprIndexTree r
      return AddTree.subNode l r
    | none =>
      match ← exprNatLeaf expr with
      | some i => return AddTree.leaf i
      | none => 
        match ← exprNatNegLeaf expr with
      | some i => return AddTree.negLeaf i
      | none => 
        throwError s!"expression {expr} is not a leaf or node"

def IndexAddTree.toString (t: IndexAddTree) : String := 
  match t with
  | AddTree.leaf i => s!"leaf {i}"
  | AddTree.node l r => 
    "node (" ++ toString l ++ ") (" ++ toString r ++ ")"
  | AddTree.negLeaf i => s!"negLeaf {i}"
  | AddTree.subNode l r => 
    "subNode (" ++ toString l ++ ") (" ++ toString r ++")"

instance : ToString IndexAddTree := ⟨IndexAddTree.toString⟩

elab "checktree" t:term : term => do
    let e ← elabTerm t none
    let e ← reduce e
    let tree ← exprIndexTree e
    logInfo s!"got tree {tree}"
    return e

#eval checktree (AddTree.node (AddTree.leaf 7) (AddTree.leaf 8))

def IndexAddTree.foldMapM
  (tExp: Expr)(basisImages: Array Expr) : TermElabM Expr := do
  let t ← exprIndexTree tExp
  foldMapMAux t basisImages

def IndexAddTree.foldMapAux {α : Type _}[AddCommGroup α][Repr α] 
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


@[simp] def foldPair{α : Type _}[AddCommGroup α][Repr α] 
  (tb : IndexAddTree × Array α)(h: tb.snd.size > 0) : α  := 
  let (t, basisImages) := tb
  t.foldMap basisImages h

@[simp] def IndexAddTree.foldMapMul {α : Type _}[CommGroup α][Repr α] 
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

@[simp, reducible] def AddTree.indexTree₀  {α : Type _}[Repr α][DecidableEq α](t: AddTree α) : 
    IndexAddTree × {a : Array α // a.size > 0} := 
    let indT := (t.indexTree #[]).fst
    let arr := (t.indexTree #[]).snd
    let p : arr.size > 0 := by apply pos_size 
    (indT, ⟨arr, p⟩)

elab "indexTree#" t:term : term => do
  let e ← elabTerm t none
  let t ← treeM e
  let res ← mkAppM ``AddTree.indexTree₀ #[t]
  reduce res

def listToExpr (lst: List Expr) : MetaM (Expr × Expr) := do
    let α ← inferType lst.head!
    let nilList ←  mkAppOptM ``List.nil #[some α]
    return (← lst.foldrM (fun l i => do
      mkAppOptM  ``List.cons #[some α, some l, some i]) nilList,
      α)


def AddTree.indexTreeM' (t : AddTree Expr) : TermElabM Expr :=
  do
    let res ← AddTree.indexTreeM t (mkConst ``Unit.unit)
    let res ← reduce res 
    let (tree, lstIn) := (← split? res).get!
    let lst ← unpack lstIn
    let lstExprPair ←  listToExpr lst
    let (lstExpr, _) := lstExprPair
    mkAppM ``Prod.mk #[tree, lstExpr]

def AddTree.indexTreeM'' (t : AddTree Expr) : 
  TermElabM <| Expr × (List Expr) :=
  do
    let res ← AddTree.indexTreeM t (mkConst ``Unit.unit)
    let res ← reduce res 
    let (tree, lstIn) := (← split? res).get!
    let lst ← unpack lstIn
    return (tree, lst)

elab "roundtrip#" t:term : term => do
  let e ← elabTerm t none
  let t ← addTreeM e
  let (indTree, lst) ← AddTree.indexTreeM'' t
  let arr := lst.toArray
  IndexAddTree.foldMapM indTree arr

elab "indTree#" t:term : term => do
  let e ← elabTerm t none
  let t ← addTreeM e
  AddTree.indexTreeM' t

@[simp] noncomputable def egInd {α : Type _}[AddCommGroup α][Repr α][DecidableEq α] (x y: α) := 
    indexTree# (x + y + x - y)

#print egInd

@[simp] def egInd' {α : Type _}[AddCommGroup α][Repr α][DecidableEq α][Inhabited α]  (x y: α) := 
    indTree# (x + y + x - y)

#check @egInd'
#print egInd'

@[simp] def egInd'' {α : Type _}[ag : AddCommGroup α][r : Repr α][de : DecidableEq α][w : Inhabited α]  (x y: α) : IndexAddTree × (List α)  := @egInd' α ag r de w x y

#print egInd''


@[simp] noncomputable def egIndMap {α : Type _}[AddCommGroup α][Repr α][DecidableEq α] 
  (x y: α) : α  :=
        (egInd x y).fst.foldMap (egInd x y).snd.val (egInd x y).snd.property

#print egIndMap

theorem egIndMapInv{α : Type _}[AddCommGroup α][Repr α][DecidableEq α] 
  (x y: α) : egIndMap x y = x + y + x - y := by 
      simp
      admit
    
@[simp] def egIndMap'' {α : Type _}[AddCommGroup α][Repr α][DecidableEq α][Inhabited α] 
  (x y: α) : α  :=
        let (tree, l) := egInd'' x y
        let arr := l.toArray 
        tree.foldMap! arr

theorem egIndMapInv''{α : Type _}[AddCommGroup α][Repr α][DecidableEq α][Inhabited α] 
  (x y: α) : egIndMap'' x y = x + y + x - y := by 
      simp 
      admit
      
theorem egRoundtrip{α : Type _}[AddCommGroup α][Repr α][DecidableEq α][Inhabited α] 
    (x y : α) : x + y + x - y =  roundtrip# (x + y + x - y)  := by rfl

def ℤnType : Nat →  MetaM Expr
| 0 => return mkConst ``Unit
| n + 1 => do mkAppM ``Prod #[mkConst ``Int, ← ℤnType n]

#eval (ℤnType 2)
