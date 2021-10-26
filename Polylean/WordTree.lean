import Polylean.ProvedBound

inductive WordTree : Word → Type where
  | emptyWord : WordTree []
  | letter : (l : Letter) → WordTree [l]
  | conjugate : (l : Letter) → (w: Word) → WordTree w → WordTree (w^l)
  | append : (w₁ : Word) → (w₂ : Word) → WordTree w₁ → WordTree w₂ → WordTree (w₁ ++ w₂)
  deriving Repr

def WordTree.bound: (w: Word) → WordTree w → Nat :=
  fun w t =>
    match t with
    | WordTree.emptyWord => 0
    | WordTree.letter l => 1
    | WordTree.conjugate l w t => bound w t 
    | WordTree.append w₁ w₂ t₁ t₂ => bound w₁ t₁ + bound w₂ t₂

def WordTree.provedBound: (w: Word) → WordTree w → ProvedBound w :=
  fun w t =>
    match t with
    | WordTree.emptyWord => ProvedBound.emptyWord
    | WordTree.letter x => 
        ⟨1, by
              intros l emp norm conj triang
              rw [norm x]
              apply Nat.le_refl⟩
    | WordTree.conjugate x w t => 
          let pb := provedBound w t
          ⟨pb.bound, by
            intros l emp norm conj triang
            rw [conj x w]
            apply pb.pf l emp norm conj triang⟩
    | WordTree.append w₁ w₂ t₁ t₂ => 
          let pb1 := provedBound w₁ t₁
          let pb2 := provedBound w₂ t₂
          ⟨pb1.bound + pb2.bound, by
            intros l emp norm conj triang
            apply Nat.le_trans (triang w₁ w₂)
            apply Nat.add_le_add
            exact pb1.pf l emp norm conj triang
            exact pb2.pf l emp norm conj triang 
            ⟩

def WordTree.headMatches(x: Letter)(ys fst snd: Word)
  (eqn : ys = fst ++ [x⁻¹] ++ snd) :
  WordTree fst → WordTree snd → WordTree (x :: ys) := by
      intros wt1 wt2 
      rw [conj_split x ys fst snd eqn]
      apply WordTree.append
      exact WordTree.conjugate x fst wt1
      exact wt2

def WordTree.prepend{w : Word} (x: Letter) 
        (wt: WordTree w) : WordTree (x :: w) := by
        have exp : x :: w = [x] ++ w := by rfl
        rw [exp]
        apply WordTree.append
        exact WordTree.letter x
        exact wt

def WordTree.min {w: Word}: WordTree w → List (WordTree w) → 
    WordTree w :=
        fun head tail =>
          tail.foldl (fun wt1 wt2 =>
            if wt1.bound ≤ wt2.bound then wt1 else wt2) head

def simpleTree(w: Word) : WordTree w :=
  match w with
  | [] => WordTree.emptyWord
  | x :: ys => by 
    have exp : x :: ys = [x] ++ ys := by rfl
    rw [exp]
    apply WordTree.append
    exact WordTree.letter x
    exact simpleTree ys


instance {w: Word} : Inhabited (WordTree w) :=⟨simpleTree w⟩

partial def wordTree : (w: Word) → WordTree w := fun w =>
  match w with
  | [] => WordTree.emptyWord
  | x :: ys =>
    let head := WordTree.prepend x (wordTree ys)
    let splits := provedSplits x⁻¹  ys
    let tail := splits.map (fun ps => 
      WordTree.headMatches x ys ps.fst ps.snd ps.proof 
        (wordTree ps.fst) (wordTree ps.snd))
    WordTree.min head tail


open Letter
#eval (wordTree ([α, α, β, α!, β!])).bound

#eval (wordTree ([α, α, β, α!, β!]^2)).bound

#eval (wordTree ([α, α, β, α!, β!]))

#eval (wordTree ([α, α, β, α!, β!]^2))

#eval ((wordTree ([α, α, β, α!, β!])).provedBound).bound

#eval ((wordTree ([α, α, β, α!, β!]^2)).provedBound).bound