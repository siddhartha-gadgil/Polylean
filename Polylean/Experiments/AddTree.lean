import Lean.Meta 
import Lean.Elab
import Polylean.Experiments.FinGenFreeAbGroup
import Std
import Lean
open Lean Meta Elab Nat Term Std


def Lean.Expr.simplify(e: Expr) : MetaM Expr := do 
    let r ← simp e (← Simp.Context.mkDefault)
    return r.expr

def verify [Monad M] : Bool → M (Option Unit)
  | true => return some ()
  | false => return none

def hOp? (fname : Name) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← inferType e
  if e.isAppOfArity fname 6 then
    let x := e.appFn!.appArg!
    let y := e.appArg!
    if (← isDefEq (← inferType x) type) && (← isDefEq (← inferType y) type) then
      return some (x, y)
    else
      return none
  else
    return none

def hOp (fname : Name) (e : Expr) : MetaM (Expr × Expr) := do
  let e ← reduce e
  dbg_trace e
  guard (e.isAppOfArity fname 6)
  match e with
    | Expr.app (Expr.app _ a _) b _ =>
      guard (← isDefEq (← inferType a) (← inferType b))
      return (a, b)
    | _ => failure

def invOp? (fname : Name) (e : Expr) : MetaM (Option (Expr)) := do
  let type ← inferType e
  if (e.isAppOfArity fname 4) then
    let y := e.appArg!
    if (← isDefEq (← inferType y) type) then
      return some y
    else
      return none
  else
    return none

inductive AddTree (α : Type u) where
  | leaf : α → AddTree α 
  | negLeaf : α → AddTree α 
  | node : AddTree α  → AddTree α  → AddTree α 
  | subNode: AddTree α  → AddTree α  → AddTree α

@[reducible, simp] def AddTree.fold {α : Type u} [AddCommGroup α] (t : AddTree α) : α :=
  match t with
  | AddTree.leaf a => a
  | AddTree.node l r =>  (fold l) + (fold r)
  | AddTree.negLeaf a => -a
  | AddTree.subNode l r => (fold l) - (fold r)

@[reducible] def AddTree.elements {α : Type _} : AddTree α → List α
  | AddTree.leaf a => [a]
  | AddTree.negLeaf a => [a]
  | AddTree.node l r => (elements l) ++ (elements r)
  | AddTree.subNode l r => (elements l) ++ (elements r)

def AddTree.negate {α : Type _} : AddTree α → AddTree α
  | AddTree.leaf a => AddTree.negLeaf a
  | AddTree.negLeaf a => AddTree.leaf a
  | AddTree.node l r => AddTree.subNode l r
  | AddTree.subNode l r => AddTree.node l r

def AddTree.reduce {α : Type _} : AddTree (AddTree α) → AddTree α
  | AddTree.leaf adt => adt
  | AddTree.negLeaf adt => negate adt
  | AddTree.node lt rt => AddTree.node (reduce lt) (reduce rt)
  | AddTree.subNode lt rt => AddTree.subNode (reduce lt) (reduce rt)

@[reducible, simp] def AddTree.map {α β : Type _} (f : α → β) : AddTree α → AddTree β
  | AddTree.leaf a => AddTree.leaf (f a)
  | AddTree.negLeaf a => AddTree.negLeaf (f a)
  | AddTree.node l r => AddTree.node (map f l) (map f r)
  | AddTree.subNode l r => AddTree.subNode (map f l) (map f r)

def AddTree.foldMul {α : Type u}[CommGroup α][Repr α]  (t : AddTree α ) : α :=
  match t with
  | AddTree.leaf a => a
  | AddTree.node l r =>  (foldMul l) * (foldMul r)
  | AddTree.negLeaf a => a⁻¹ 
  | AddTree.subNode l r => (foldMul l) / (foldMul r)

/-
Reference:  Monads, partial evaluations, and rewriting by Tobias Fritz and Paulo Perrone
https://arxiv.org/pdf/1810.06037.pdf
-/

instance : Monad AddTree :=
  {
    pure := AddTree.leaf
    map := AddTree.map
    bind := λ adt f => (adt.map f).reduce
  }

instance : LawfulMonad AddTree := sorry

abbrev IndexAddTree := AddTree Nat 

@[simp] def AddTree.indexTree {α : Type u} [DecidableEq α] (t : AddTree α)
  (accum : Array α := #[]) : 
      IndexAddTree × (Array α) := 
  match t with
  | AddTree.leaf a => 
    match accum.getIdx? a with
    | some i => (AddTree.leaf i, accum)
    | none => (AddTree.leaf (accum.size), accum)
  | AddTree.node l r =>  
    let (lIdx, lAccum) := indexTree l accum
    let (rIdx, rAccum) := indexTree r lAccum
    (AddTree.node lIdx rIdx, rAccum)
  | AddTree.negLeaf a => 
    match accum.getIdx? a with
    | some i => (AddTree.negLeaf i, accum)
    | none => (AddTree.negLeaf (accum.size), accum)
  | AddTree.subNode l r => 
    let (lIdx, lAccum) := indexTree l accum
    let (rIdx, rAccum) := indexTree r lAccum
    (AddTree.subNode lIdx rIdx, rAccum)

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
  | some a => mkAppM ``AddTree.negLeaf #[e]
  | none  =>
  match ← invOp? ``Inv.inv e with
  | some a => mkAppM ``AddTree.negLeaf #[e]
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

syntax (name := addtreeElab) "addTree#" term : term

partial def addtreeM : TermElab :=
  fun stx typ? => do
  match stx with
  | `(HAdd.hAdd _ _ _ _ $a:term $b:term) =>
    dbg_trace "Addition"
    let l ← addtreeM a typ?
    let r ← addtreeM b typ?
    return mkApp2 (mkConst `AddTree.node) l r
  | `(HSub.hSub _ _ _ _ $a:term $b:term) =>
    dbg_trace "Subtraction"
    let l ← addtreeM a typ?
    let r ← addtreeM b typ?
    return mkApp2 (mkConst `AddTree.subNode) l r
  | `(Neg.neg _ _ $a:term) =>
    dbg_trace "Negation"
    let t ← addtreeM a typ?
    return mkApp (mkConst `AddTree.negLeaf) t
  | `($a:term) =>
    dbg_trace "Leaf"
    return mkApp (mkConst `AddTree.leaf) (← Term.elabTerm a typ?) -- this leads to an infinite recursion. Maybe creating a new syntax category will help

attribute [termElab addtreeElab] addtreeM -- adding the attribute in the usual way is not working, probably because the function is recursive and partial

#print Term.elabTerm

def IndexAddTree.map {α : Type _} [AddCommGroup α] [Repr α]
  (t : IndexAddTree) (basisImages : List α) : AddTree α :=

  if h:basisImages.length = 0 then
    AddTree.leaf (0 : α)
  else
    have hpos := Nat.pos_of_ne_zero h
    match t with
    | AddTree.leaf i => AddTree.leaf (basisImages.get (Fin.ofNat' i hpos))
    | AddTree.negLeaf i => AddTree.negLeaf (basisImages.get (Fin.ofNat' i hpos))
    | AddTree.node l r => AddTree.node (map l basisImages) (map r basisImages)
    | AddTree.subNode l r => AddTree.subNode (map l basisImages) (map r basisImages)

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

theorem AddTree.fold_tree_map_eq {A B : Type _} [AddCommGroup A] [AddCommGroup B]
  (φ : A → B) [Homφ : AddCommGroup.Homomorphism φ] : (t : AddTree A) → φ t.fold = (t.map φ).fold := by 
    intro t
    induction t with
      | leaf a => rw [map, fold, fold] 
      | negLeaf a => rw [map, fold, fold, Homφ.neg_push]
      | node l r ihl ihr => rw [map, fold, fold, Homφ.add_dist, ihl, ihr]
      | subNode l r ihl ihr => rw [map, fold, fold, Homφ.neg_dist, ihl, ihr]

-- taking an abstract tree to a given list of `n` elements of group `A` is equivalent to
-- first taking it to the basis of `ℤ^n` and then apply the `inducedFreeMap`
theorem IndexAddTree.fold_tree_freegroup_eq (t : IndexAddTree) {A : Type _} [AddCommGroup A] [Repr A]
  {n : ℕ} (l : List A) (h : l.length = n) (hpos : n > 0) :
  IndexAddTree.foldMap t l.toArray (by simp [h, hpos]) =
  (inducedFreeMap l h) (IndexAddTree.foldMap t (ℤbasis n).toArray (by simp [hpos])) := by
  induction t with
    | leaf _ =>
        simp [foldMap]
        rw [Array.getfromlist, Array.getfromlist, List.mapget (inducedFreeMap l h), List.get_index_eq (map_basis l h)]
        apply congrArg
        apply Fin.eq_of_val_eq; simp
        subst h
        apply Fin.eq_of_eq_of_Nat'; simp
        all_goals (apply Fin.eq_val_bound; simp)
    | negLeaf _ =>
        simp [foldMap]
        apply congrArg
        rw [Array.getfromlist, Array.getfromlist, List.mapget (inducedFreeMap l h), List.get_index_eq (map_basis l h)]
        apply congrArg
        apply Fin.eq_of_val_eq; simp
        subst h
        apply Fin.eq_of_eq_of_Nat'; simp
        all_goals (apply Fin.eq_val_bound; simp)
    | node _ _ ihl ihr => simp [ihl, ihr, foldMap]
    | subNode _ _ ihl ihr => simp [ihl, ihr, foldMap]


elab "tree#" s:term : term => do
  let e ← Term.elabTerm s none
  treeM e

def IndexAddTree.reduce {α : Type _} [AddCommGroup α] [Repr α] [DecidableEq α] (it : IndexAddTree) (arr : Array α) (harr : arr.size > 0) : α :=
  (inducedFreeMap arr.data rfl) (IndexAddTree.foldMap it (ℤbasis arr.size).toArray (by simp [harr]))

variable (x : ℤ)

abbrev egTree (n m : ℤ) := tree# ((n + m) + (m + (m + n)) - n)

abbrev egParse : AddTree ℤ := tree# (2 : ℤ) + ((5 : ℤ) - (x : ℤ))


#print Term.elabByTactic

/-
#check egTree

#print egTree

#eval AddTree.fold <| egTree 12 3

section test

variable {a b : ℤ}

def ℤexpr := a + b - a + a + b

def ℤexprtree (a b : ℤ) := tree# (a + b - a + a + b)

end test
-/

def reduceTerm {α : Type _} (a : α) (t : AddTree α) [AddCommGroup α] [DecidableEq α] : α :=
  -- let t : AddTree α := tree# a
  let ⟨it, ⟨l⟩⟩ := t.indexTree
  let n : ℕ := l.length
  let τ : AddTree (ℤ ^ n) := it.map (ℤbasis n)
  let ϕ : ℤ ^ n → α := inducedFreeMap l rfl
  have := AddTree.fold_tree_map_eq ϕ τ
  (τ.map ϕ).fold

-- set_option pp.all true

variable {x y z : ℤ}

#reduce (reduceTerm ((x + y - x) + (z - y)) (tree# ((x + y - x) + (z - y))))

#reduce tree# ((-12) + 3)

@[irreducible] def a : ℤ := 32432

#check Term.elabTerm
