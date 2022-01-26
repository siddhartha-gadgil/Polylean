inductive Letter where
  | α : Letter
  | β : Letter 
  | α! : Letter
  | β! : Letter
  deriving DecidableEq, Repr, Hashable

def Letter.inv : Letter → Letter
  | α => α!
  | β  => β!
  | α! => α 
  | β! => β 

postfix:max "⁻¹" => Letter.inv

open Letter

abbrev Word := List Letter

def Word.pow : Word → Nat → Word 
  | w, 0 => []
  | w, Nat.succ m => w ++ (pow w m)

instance : Pow Word Nat where
  pow w n := w.pow n

-- The code below (with better termination) is due to Mario Carneiro
-- split a word into parts before and after each occurrence of a letter `l`
def splits (l : Letter) : (w : Word) → List {p : Word × Word // p.1.length + p.2.length < w.length}
  | [] => []
  | x :: ys =>
    let tailSplits := (splits l ys).map fun ⟨(fst, snd), h⟩ =>
      ⟨(x :: fst, snd), by simp [Nat.succ_add, Nat.succ_lt_succ h]⟩
    if x = l then ⟨([], ys), by simp [Nat.lt_succ_self]⟩ :: tailSplits else tailSplits

def length : Word → Nat
  | [] => 0
  | x :: ys =>
    let base := 1 + (length ys)
    let derived := (splits x⁻¹ ys).map fun ⟨(fst, snd), h⟩ =>
      have h : fst.length + snd.length < ys.length + 1 := Nat.lt_trans h (Nat.lt_succ_self _)
      have h1 : snd.length < ys.length + 1  := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h
      have h2 : fst.length < ys.length + 1 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h
      length fst + length snd
    derived.foldl min base -- minimum of base and elements of derived
termination_by _ l => l.length

#eval length ([α, α, β, α!, β!])

#eval length ([α, α, β, α!, β!]^2)

-- For proofs 

def Word.conj: Word → Letter → Word := fun w l => [l] ++ w ++ [l⁻¹]

instance: Pow Word Letter where
  pow w l := w.conj l

