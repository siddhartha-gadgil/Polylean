import Polylean.LengthBound
open Letter

structure ProvedSplit (l: Letter)(w : Word) where
  fst : Word
  snd: Word
  proof : w = fst ++ [l] ++ snd 

-- Split with first piece empty when head matches the splitting letter.
def ProvedSplit.head (x: Letter) (ys: Word) : ProvedSplit x (x :: ys) :=
  ⟨[], ys, rfl⟩ 

-- Prepend to a proved split of the tail (`l` and `ys` implicit).
def ProvedSplit.prepend{l: Letter}{ys : Word} (x: Letter) 
        (ps: ProvedSplit l ys) : ProvedSplit l (x :: ys) :=
      let newFst := x :: ps.fst
      let newSnd := ps.snd
      have newProof : x :: ys = newFst ++ [l] ++ newSnd  := 
        by
          let prev : x :: ys = x :: (ps.fst ++ [l] ++ ps.snd) 
             := congrArg  (List.cons x) ps.proof
          rw [prev] 
          simp
      ⟨newFst, newSnd, newProof⟩   

-- all proved splits of a word
def provedSplits(z: Letter) : (w : Word) → List (ProvedSplit z w) 
  | [] => []
  | x :: ys =>
    let tailSplits := (provedSplits z ys).map (ProvedSplit.prepend x) 
    if c:x = z then
      let headSplit : ProvedSplit z (x :: ys) :=
        by
          rw [c] 
          exact ProvedSplit.head z ys 
      headSplit :: tailSplits
    else tailSplits

abbrev Length := Word → Nat

def conjInv(l: Length) : Prop := (x : Letter) → (g : Word) → l (g^x) = l (g)

def triangIneq(l: Length) : Prop := (g h : Word) → l (g ++ h) ≤ l g + l h

def normalized(l: Length) : Prop := (x : Letter) → l [x] = 1

def emptyWord(l: Length) : Prop := l [] = 0

structure ProvedBound(g: Word):  Type where
  bound: Nat 
  pf : (l: Length) → emptyWord l → 
           normalized l → conjInv l → triangIneq l → l g ≤ bound

theorem conj_split (x: Letter) (ys fst snd: Word) :
          ys = fst ++ [x⁻¹] ++ snd → x :: ys = fst^x ++ snd :=
            by
              intro hyp
              have expand : fst^x = [x] ++ fst ++ [x⁻¹] := rfl
              rw [expand] 
              rw [hyp]
              simp

-- deducing bound using `l (xh₁x⁻¹h₂) ≤ b₁ + b₂` given `l (hᵢ) ≤ bᵢ`, `i = 1, 2`
def ProvedBound.headMatches(x: Letter)(ys fst snd: Word)
  (eqn : ys = fst ++ [x⁻¹] ++ snd) :
  ProvedBound fst → ProvedBound snd → ProvedBound (x :: ys) := 
    fun pb1 pb2 =>
    let bound := pb1.bound + pb2.bound
    let pf : 
      (l: Length) → emptyWord l → normalized l → conjInv l → triangIneq l → 
          l (x :: ys) ≤ bound := by
            intros l emp norm conj triang
            rw [conj_split x ys fst snd eqn]
            have lem : l (fst ^ x ++ snd) ≤ l (fst^x) + l snd := 
                by
                  apply triang
            have clem : l (fst^x) = l fst := by apply conj
            rw [clem] at lem
            apply Nat.le_trans lem
            have l1 : l fst ≤ pb1.bound := pb1.pf l emp norm conj triang
            have l2 : l snd ≤ pb2.bound := pb2.pf l emp norm conj triang
            apply Nat.add_le_add l1 l2
    ⟨bound, pf⟩

-- deducing `l(xh) ≤ b + 1` given `l(h) ≤ b`
def ProvedBound.prepend{w : Word} (x: Letter) 
        (ps: ProvedBound w) : ProvedBound (x :: w) :=
      let newBound := ps.bound + 1
      ⟨newBound, fun l emp norm conj triang => by
        let prev := ps.pf l emp norm conj triang
        have lemTri : l (x :: w) ≤ l ([x]) + l w := by apply triang [x] 
        apply Nat.le_trans lemTri
        rw [norm x]
        rw [Nat.add_comm]
        apply Nat.add_le_add_right prev⟩

-- `l(e) ≤ 0`
def ProvedBound.emptyWord: ProvedBound [] :=
  ⟨0, fun l emp _ _ _ => by rw [emp]; apply Nat.le_refl⟩

-- the best proved bound for a word
def ProvedBound.min {w: Word}: ProvedBound w → List (ProvedBound w) → 
    ProvedBound w :=
        fun head tail =>
          tail.foldl (fun pb1 pb2 =>
            if pb1.bound ≤ pb2.bound then pb1 else pb2) head

-- bound using only the triangle inequality
def easyBound : (w : Word) → ProvedBound w 
  | [] => ProvedBound.emptyWord
  | x :: ys =>
    let base := easyBound ys
    let bound := base.bound + 1
    let pf: 
      (l: Length) → emptyWord l → normalized l → conjInv l → triangIneq l → 
          l (x :: ys) ≤ bound := 
        by
          intros l emp norm conj triang
          let lem : l (x :: ys) ≤ l [x] + l ys := triang [x] ys
          apply Nat.le_trans lem
          rw [norm x]
          rw [Nat.add_comm 1 (l ys)]
          apply Nat.add_le_add_right
          exact base.pf l emp norm conj triang 
    ⟨bound, pf⟩

instance {w: Word} : Inhabited (ProvedBound w) :=⟨easyBound w⟩

-- bound with proof for words  
partial def provedBound : (w: Word) → ProvedBound w := fun w =>
  match w with
  | [] => ProvedBound.emptyWord
  | x :: ys =>
    let head := ProvedBound.prepend x (provedBound ys)
    let splits := provedSplits x⁻¹  ys
    let tail := splits.map (fun ps => 
      ProvedBound.headMatches x ys ps.fst ps.snd ps.proof 
        (provedBound ps.fst) (provedBound ps.snd))
    ProvedBound.min head tail
    
#eval (provedBound ([α, α, β, α!, β!])).bound

#eval (provedBound ([α, α, β, α!, β!]^2)).bound
