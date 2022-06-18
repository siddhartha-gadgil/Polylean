structure Graph(V: Type) (E: Type) where
  null : E
  init : E → V
  bar : E → E
  barInv : bar ∘ bar = id
  barNoFP : ∀ e: E, bar e ≠ e
  
variable {V: Type}{E: Type}[DecidableEq V][DecidableEq E]

@[inline] def term{V: Type}{E: Type}(graph: Graph V E): E → V :=
  fun e => graph.init (graph.bar e)

inductive EdgePath{V: Type}{E: Type}(graph: Graph V E): V → V → Type where
  | single : (x: V) → EdgePath graph v v
  | cons : {x y z : V} → (e : E) → graph.init e = x → term graph e = y →  
        EdgePath graph y z → EdgePath graph x z

def EdgePath.length{V: Type}{E: Type}{graph: Graph V E}{x y: V}: EdgePath graph x y → Nat
  | EdgePath.single x => 0
  | EdgePath.cons  _ _ _ path => length path + 1 

open EdgePath

-- concatenates two edgepaths 
def multiply {V : Type} {E : Type} {G : Graph V E} {x y z : V}: (EdgePath G x y) → (EdgePath G y z) → (EdgePath G x z) := by 
intro p q
match p with
| single x =>exact q
| cons ex h1 h2 exy => exact (cons ex h1 h2 (multiply exy q))



--proves that the endpoint of the reverse of an edge is the start point of the edge
theorem lemma1 {V : Type} {E : Type} {G : Graph V E} {x : V}{e : E}: G.init e = x → (term G (G.bar e) = x) :=
by
intro h
have h1 : G.bar (G.bar e) = e := congr G.barInv (Eq.refl e) 
have h2 : G.init (G.bar (G.bar e)) = G.init e := congrArg G.init h1 
apply Eq.trans h2 h


-- proves associativity of path multiplication
theorem mulassoc {G : Graph V E} (p : EdgePath G w x) (q : EdgePath G x y) (r : EdgePath G y z):
      (multiply (multiply p q) r) = (multiply p (multiply q r)) := by
      induction p with
      | single w => 
        calc 
        multiply (multiply (single w) q) r = multiply q r := by rfl
        _ = multiply (single w) (multiply q r) := by rfl
      | cons ex h1 h2 exy ih => 
        calc 
        multiply (multiply (cons ex h1 h2 exy) q) r = multiply (cons ex h1 h2 (multiply exy q)) r := by rfl
        _ = cons ex h1 h2 (multiply (multiply exy q) r) := by rfl
        _ = cons ex h1 h2 (multiply exy (multiply q r)) := by rw[ih]
        _ = multiply (cons ex h1 h2 exy) (multiply q r) := by rfl


-- reverses an edgepath
def inverse {V : Type} {E : Type} {G : Graph V E} {x y : V}: (EdgePath G x y) → (EdgePath G y x)
| single x => single x 
| cons ex h1 h2 exy => multiply (inverse exy) (cons (G.bar (ex)) h2 (lemma1 h1) (single x)) 

--reduces given path such that its first two edges are not inverses of each other
def reducePath0 {G : Graph V E} {x y : V} : EdgePath G x y→ EdgePath G x y
| single x => single x
| cons ex h1 h2 (single y) => cons ex h1 h2 (single y)
| cons ex h1 h2 (cons ey h3 h4 (eyz)) => 
        if c : (x = term G ey) ∧ (ey = G.bar (ex)) then
              Eq.symm (Eq.trans (And.left c) h4) ▸ eyz
            else
            cons ex h1 h2 (cons ey h3 h4 (eyz))

-- reduces given path such that no two consecutive edges are inverses of each other
def reducePath {G : Graph V E} {x y : V} : (p : EdgePath G x y )→ 
  {rp :EdgePath G x y // rp.length ≤ p.length}
| single x => ⟨single x, by apply Nat.le_refl⟩
| cons ex h1 h2 (single y) => ⟨cons ex h1 h2 (single y), by apply Nat.le_refl⟩
| cons ex h1 h2 (cons ey h3 h4 (eyz)) => 
    have : length eyz < length (cons ex h1 h2 (cons ey h3 h4 eyz)) := by admit
    let ⟨eyz', ih⟩ := reducePath eyz 
    if c : (x = term G ey) ∧ (ey = G.bar (ex)) then
      ⟨Eq.symm (Eq.trans (And.left c) h4) ▸ eyz', by 
      
      admit⟩
    else
      have : length (cons ey h3 h4 eyz') < length (cons ex h1 h2 (cons ey h3 h4 eyz)) := by admit
      let ⟨prev, ih'⟩ := reducePath (cons ey h3 h4 (eyz'))
      have : 
        length (cons ex h1 h2 prev) < 
          length (cons ex h1 h2 (cons ey h3 h4 eyz)) := by admit
      let ⟨rp, pf⟩ := reducePath (cons ex h1 h2 (prev))
      ⟨rp, sorry⟩
termination_by _ _ _ _ p => p.length

#check @EdgePath


inductive homotopy {G : Graph V E} : EdgePath G x y → EdgePath G x y → Sort where
| consht : (x : V) → homotopy (single x) (single x)
| cancel : (ex : E) → {w x y : V} → (p : EdgePath G x y) → 
           (h : x = G.init ex) → { h1 : term G ex = w} → 
           homotopy p (cons ex (Eq.symm h) h1 (cons (G.bar (ex)) h1 (lemma1 (Eq.symm h)) p))
| mult : {x y z : V} → {p q : EdgePath G y z} →
         homotopy p q → (ex : E) →(h1 : y = term G ex) → { h : x = G.init ex} → 
         homotopy (cons ex (Eq.symm h) (Eq.symm h1) p) (cons ex (Eq.symm h) (Eq.symm h1) q)


theorem homotopymult {V : Type} {E : Type} {G : Graph V E} {x y z : V} (p1 p2 : EdgePath G y z) (q : EdgePath G x y) (h :homotopy p1 p2):
         (homotopy (multiply q p1) (multiply q p2)) := by
         induction q with
        | single w  => have h7 : (multiply (single w) p1) = p1 := by rfl
                       have h8 : (multiply (single w) p2) = p2 := by rfl
                       exact h7 ▸ h8 ▸ h
        | cons ex h1 h2 exy ih => 
        have h7 : (cons ex h1 h2 (multiply exy p1)) = (multiply (cons ex h1 h2 exy) p1) := by rfl
        have h8 : cons ex h1 h2 (multiply exy p2) = multiply (cons ex h1 h2 exy) p2 := by rfl
        have h9 : homotopy (cons ex h1 h2 (multiply exy p1)) (cons ex h1 h2 (multiply exy p2)) := by admit -- exact homotopy.mult (ih p1 p2 h) ex (Eq.symm h2) h1
        sorry

   
