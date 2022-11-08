structure Graph(V: Type) (E: Type) where
  null : E
  init : E → V
  bar : E → E
  barInv : bar ∘ bar = id
  barNoFP : ∀ e: E, bar e ≠ e
  
variable {V: Type}{E: Type}[DecidableEq V][DecidableEq E]

@[inline] def term (graph: Graph V E): E → V :=
  fun e => graph.init (graph.bar e)

inductive EdgePath (graph: Graph V E): V → V → Type where
  | single : (x: V) → EdgePath graph v v
  | cons : {x y z : V} → (e : E) → graph.init e = x → term graph e = y →  
        EdgePath graph y z → EdgePath graph x z

def EdgePath.length {graph: Graph V E}{x y: V}: EdgePath graph x y → Nat
  | EdgePath.single x => 0
  | EdgePath.cons  _ _ _ path => length path + 1 

open EdgePath

-- concatenates two edgepaths 
def multiply {G : Graph V E} {x y z : V}: (EdgePath G x y) → (EdgePath G y z) → (EdgePath G x z) := by 
intro p q
match p with
| single x => exact q
| cons ex h1 h2 exy => exact (cons ex h1 h2 (multiply exy q))



--proves that the endpoint of the reverse of an edge is the start point of the edge
theorem lemma1 {G : Graph V E} {x : V}{e : E}: G.init e = x → (term G (G.bar e) = x) :=
by
intro h
have h1 : G.bar (G.bar e) = e := congr G.barInv (Eq.refl e) 
have h2 : G.init (G.bar (G.bar e)) = G.init e := congrArg G.init h1 
apply Eq.trans h2 h

-- proves associativity of path multiplication
theorem mult_assoc {G : Graph V E} (p : EdgePath G w x) (q : EdgePath G x y) (r : EdgePath G y z):
      (multiply (multiply p q) r) = (multiply p (multiply q r)) := by
      induction p with
      | single w => simp[multiply]
      | cons ex h1 h2 exy ih => simp[multiply, ih]

theorem mult_const {G : Graph V E} {p : EdgePath G x y} : 
      (multiply p (single y)) = p := by
      induction p with
      | single x => simp [multiply] ; sorry
      | cons ex h1 h2 exy ih => simp[multiply, ih] 

-- reverses an edgepath
def inverse {G : Graph V E} {x y : V}: (EdgePath G x y) → (EdgePath G y x)
| single x => single x 
| cons ex h1 h2 exy => multiply (inverse exy) (cons (G.bar (ex)) h2 (lemma1 h1) (single x)) 

open Nat

-- reduces given path such that no two consecutive edges are inverses of each other
def reducePath {G : Graph V E} {x y : V} : (p : EdgePath G x y )→ 
  {rp : EdgePath G x y // rp.length ≤ p.length}
| single x => ⟨single x, by apply Nat.le_refl⟩
| cons ex h1 h2 (single y) => ⟨cons ex h1 h2 (single y), by apply Nat.le_refl⟩
| cons ex h1 h2 (cons ey h3 h4 (eyz)) => 
    have h5: length eyz < length (cons ex h1 h2 (cons ey h3 h4 eyz)) := by 
      simp[EdgePath.length , Nat.lt_trans (Nat.lt_succ_self (length eyz) ) (Nat.lt_succ_self (length eyz +1))]
    let ⟨eyz', ih⟩ := reducePath eyz 
    if c : (x = term G ey) ∧ (ey = G.bar (ex)) then
      ⟨Eq.symm (Eq.trans (And.left c) h4) ▸ eyz', by
      have h6 : length (Eq.symm (Eq.trans (And.left c) h4) ▸ eyz') = length (eyz') := by sorry--simp[EdgePath.length]
      rw[h6]
      exact Nat.le_trans ih (Nat.le_of_lt h5)
      ⟩
    else
      have : length (cons ey h3 h4 eyz') < length (cons ex h1 h2 (cons ey h3 h4 eyz)) := by 
       simp[EdgePath.length, Nat.lt_succ_of_le (Nat.succ_le_succ ih)] 
      let ⟨prev, ih'⟩ := reducePath (cons ey h3 h4 (eyz'))
      if d : prev.length < (cons ey h3 h4 (eyz')).length then
      have h8 : 
        length (cons ex h1 h2 prev) <
          length (cons ex h1 h2 (cons ey h3 h4 eyz)) := by 
           simp[EdgePath.length]
           have h9 : (cons ey h3 h4 (eyz')).length ≤ length eyz + 1 := by 
            simp[EdgePath.length, Nat.succ_le_succ ih] 
           exact Nat.succ_lt_succ (Nat.lt_of_lt_of_le d h9 ) 
      let ⟨rp, pf⟩ := reducePath (cons ex h1 h2 (prev))
      ⟨rp, Nat.le_of_lt (Nat.lt_of_le_of_lt pf h8)⟩
      else 
      ⟨cons ex h1 h2 (cons ey h3 h4 (eyz)), by apply Nat.le_refl⟩
termination_by _ _ _ _ p => p.length

--defines homotopy of edgepaths
inductive homotopy {G : Graph V E} : EdgePath G x y → EdgePath G x y → Sort where
| consht : (x : V) → (homotopy (single x) (single x)) -- constant homotopy
| cancel : (ex : E) → {w x y : V} → (p : EdgePath G x y) → -- cancelling consecutive opposite edges from a path
           (h : G.init ex = x) → { h1 : term G ex = w} → 
           homotopy p (cons ex h h1 (cons (G.bar (ex)) h1 (lemma1 h) p))
| mult : {x y z : V} → {p q : EdgePath G y z} →   -- adding an edge to homotopic paths
         homotopy p q → (ex : E) →(h1 : G.init ex = x) → ( h : term G ex = y)→ 
         homotopy (cons ex h1 h p) (cons ex h1 h q)

--proves that homotopy is left multiplicative
theorem homotopy_left_mult {G : Graph V E} {x y z : V} (p1 p2 : EdgePath G y z) (q : EdgePath G x y) (h :homotopy p1 p2):
         (homotopy (multiply q p1) (multiply q p2)) := by
         induction q with
        | single w  => 
          simp [multiply, h]
        | cons ex h1 h2 exy ih => 
         simp[homotopy.mult (ih p1 p2 h) ex h1 h2, multiply]

/-theorem homotopy_reverse {G : Graph V E} {x y : V} (p1 p2 : EdgePath G x y) : homotopy p1 p2 → homotopy (inverse p1) (inverse p2) := by
        intro h
        induction p1 with
        | single x => 
              induction h with
              | consht z => simp[inverse]
              | cancel ex p h h1 =>
              | mult h' h1 h2 => 
        |  cons ex h1 h2 exy =>-/

/-theorem homotopy_right_mult {V : Type} {E : Type} {G : Graph V E} {x y z : V} (p1 p2 : EdgePath G x y) (q : EdgePath G y z) (h :homotopy p1 p2):
        (homotopy (multiply p1 q) (multiply p2 q)) := by
         induction q with
        | single _ => have h1 : multiply p1 (single _) = p1 := by sorry --apply mult_const p1
        | cons ex h1 h2 exy ih => 
         simp[homotopy.mult (ih p1 p2 h) ex h1 h2, multiply]-/

/-theorem homotopy_reducepath {G : Graph V E} {x y : V} (p1 p2 : EdgePath G x y) (ih : p2.length ≤ p1.length)
        (h : reducePath p1 = p2) : homotopy p1 p2 := by
        let c := p1.length
        induction c with
        | zero => have: p2.length = 0 := by 
          match p1 with
          | single x => -/
