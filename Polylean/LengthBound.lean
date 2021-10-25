inductive Letter where
  | α : Letter
  | β : Letter 
  | α! : Letter
  | β! : Letter
  deriving DecidableEq, Repr

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

def splits(l : Letter) : Word → List (Word × Word) 
  | [] => []
  | x :: ys =>
    let tailSplits := (splits l ys).map (fun (fst, snd) => (x :: fst, snd)) 
    if x = l then ([], ys) :: tailSplits else tailSplits

partial def l : Word → Nat  
  | [] => 0
  | x :: ys =>
    let base := 1 + (l ys)
    let derived := (splits (x⁻¹) ys).map (fun (fst, snd) => l fst + l snd) 
    derived.foldl min base -- minimum of base and elements of derived

#eval l ([α, α, β, α!, β!])

#eval l ([α, α, β, α!, β!]^2)

-- For proofs 

def Word.conj: Word → Letter → Word := fun w l => [l] ++ w ++ [l⁻¹]

instance: Pow Word Letter where
  pow w l := w.conj l

