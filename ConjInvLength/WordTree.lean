import ConjInvLength.ProvedBound

inductive ProofTree : Word → Type where
  | emptyWord : ProofTree []
  | normalized : (l : Letter) → ProofTree [l]
  | conjugate : (l : Letter) → (w: Word) → ProofTree w → ProofTree (w^l)
  | triangleIneq : (w₁ : Word) → (w₂ : Word) → 
                      ProofTree w₁ → ProofTree w₂ → ProofTree (w₁ ++ w₂)
  deriving Repr

def ProofTree.bound: (w: Word) → ProofTree w → Nat :=
  fun w t =>
    match t with
    | ProofTree.emptyWord => 0
    | ProofTree.normalized l => 1
    | ProofTree.conjugate l w t => bound w t 
    | ProofTree.triangleIneq w₁ w₂ t₁ t₂ => bound w₁ t₁ + bound w₂ t₂

def ProofTree.provedBound: (w: Word) → ProofTree w → ProvedBound w :=
  fun w t =>
    match t with
    | ProofTree.emptyWord => ProvedBound.emptyWord
    | ProofTree.normalized x => 
        ⟨1, by
              intros l emp norm conj triang
              rw [norm x]⟩
    | ProofTree.conjugate x w t => 
          let pb := provedBound w t
          ⟨pb.bound, by
            intros l emp norm conj triang
            rw [conj x w]
            apply pb.pf l emp norm conj triang⟩
    | ProofTree.triangleIneq w₁ w₂ t₁ t₂ => 
          let pb1 := provedBound w₁ t₁
          let pb2 := provedBound w₂ t₂
          ⟨pb1.bound + pb2.bound, by
            intros l emp norm conj triang
            apply Nat.le_trans (triang w₁ w₂)
            apply Nat.add_le_add
            exact pb1.pf l emp norm conj triang
            exact pb2.pf l emp norm conj triang 
            ⟩

def ProofTree.headMatches(x: Letter)(ys fst snd: Word)
  (eqn : ys = fst ++ [x⁻¹] ++ snd) :
  ProofTree fst → ProofTree snd → ProofTree (x :: ys) := by
      intros pt1 pt2 
      rw [conj_split x ys fst snd eqn]
      apply ProofTree.triangleIneq
      exact ProofTree.conjugate x fst pt1
      exact pt2

def ProofTree.prepend{w : Word} (x: Letter) 
        (pt: ProofTree w) : ProofTree (x :: w) := by
        have exp : x :: w = [x] ++ w := by rfl
        rw [exp]
        apply ProofTree.triangleIneq
        exact ProofTree.normalized x
        exact pt

def ProofTree.min {w: Word}: ProofTree w → List (ProofTree w) → 
    ProofTree w :=
        fun head tail =>
          tail.foldl (fun pt1 pt2 =>
            if pt1.bound ≤ pt2.bound then pt1 else pt2) head

def simpleTree(w: Word) : ProofTree w :=
  match w with
  | [] => ProofTree.emptyWord
  | x :: ys => by 
    have exp : x :: ys = [x] ++ ys := by rfl
    rw [exp]
    apply ProofTree.triangleIneq
    exact ProofTree.normalized x
    exact simpleTree ys


instance {w: Word} : Inhabited (ProofTree w) :=⟨simpleTree w⟩

def proofTree : (w: Word) → ProofTree w := fun w =>
  match h:w with
  | [] => ProofTree.emptyWord
  | x :: ys =>
    have : ys.length < (x :: ys).length := by
      simp
    let head := ProofTree.prepend x (proofTree ys)
    let splits := provedSplits x⁻¹  ys
    have wl:  w.length = ys.length + 1 := by
      rw[h] 
      rfl
    let tail := splits.map (fun ps => 
      have l1 : ps.fst.length + 1 ≤ ys.length + 1 := 
        by
        have lm := splitFirst ps
        apply Nat.le_trans lm
        apply Nat.le_succ        
      have l2 : ps.snd.length + 1 ≤ ys.length + 1 :=
        by
        have lm := splitSecond ps
        apply Nat.le_trans lm
        apply Nat.le_succ
      ProofTree.headMatches x ys ps.fst ps.snd ps.proof 
        (proofTree ps.fst) (proofTree ps.snd))
    ProofTree.min head tail
termination_by  _ w => w.length
decreasing_by assumption

open Letter

#eval (proofTree ([α, α, β, α!, β!]))

#eval (proofTree ([α, α, β, α!, β!]^2))

#eval ((proofTree ([α, α, β, α!, β!])).provedBound).bound

#eval ((proofTree ([α, α, β, α!, β!]^2)).provedBound).bound

#eval (proofTree ([α, α, β, α!, β!])).bound

#eval (proofTree ([α, α, β, α!, β!]^2)).bound
