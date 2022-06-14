structure Graph(V: Type) (E: Type)[DecidableEq V][DecidableEq E] where
  null : E
  init : E → V
  bar : E → E
  barInv : bar ∘ bar = id
  barNoFP : ∀ e: E, bar e ≠ e

variable {V: Type}{E: Type}[DecidableEq V][DecidableEq E]

@[inline] def term(graph: Graph V E): E → V :=
  fun e => graph.init (graph.bar e)

inductive EdgePath(graph: Graph V E): V → V → Type where
  | single : (x: V) → EdgePath graph v v
  | cons : {x y z : V} → (e : E) → graph.init e = x → term graph e = y →  
        EdgePath graph y z → EdgePath graph x z

def length{graph: Graph V E}{x y: V}: EdgePath graph x y → Nat
  | EdgePath.single x => 0
  | EdgePath.cons  _ _ _ path => length path + 1 

open EdgePath


/-theorem lemma2   (G : Graph V E) {x y z : V} (p : EdgePath G x z) (h : x = y) : EdgePath G y z :=
match h with
| rfl => p

def follow  (G : Graph V E) (x y : V) (p : EdgePath G x y) : V :=
match p with
| single x => x
| cons ex h1 h2 exy => term G ex


def forward  {G : Graph V E} {x y : V} (p : EdgePath G x y) :  EdgePath G _ y :=
match p with
| cons ex h1 h2 exy => --have h : (follow G x _ p) = term G ex := sorry 
                         exy 
| single x => sorry


def next  {G : Graph V E} {x y : V}: EdgePath G x y → E
| single x => G.null
| cons ex h1 h2 exy => ex-/

def multiply  {G : Graph V E} {x y z : V}: (EdgePath G x y) → (EdgePath G y z) → (EdgePath G x z) 
| single x , single y => single x 
|  single x , cons ey h1 h2 eyz => cons ey h1 h2 eyz
| cons ex h1 h2 exy , single y => cons ex h1 h2 exy
| cons ex h1 h2 exy , cons ey h3 h4 eyz => cons ex h1 h2 (multiply exy (cons ey h3 h4 eyz))

theorem lemma1  {G : Graph V E} {x : V}{e : E}: G.init e = x → (term G (G.bar e) = x) :=
by
intro h
have h1 : G.bar (G.bar e) = e := congr G.barInv (Eq.refl e) 
have h2 : G.init (G.bar (G.bar e)) = G.init e := congrArg G.init h1 
apply Eq.trans h2 h


def inverse  {G : Graph V E} {x y : V}: (EdgePath G x y) → (EdgePath G y x)
| single x => single x 
| cons ex h1 h2 exy => multiply (inverse exy) (cons (G.bar (ex)) h2 (lemma1 h1) (single x)) 

def reducePath {G : Graph V E} {x y : V} : EdgePath G x y→ EdgePath G x y 
| single x => single x
| cons ex h1 h2 (single y) => cons ex h1 h2 (single y)
| cons ex h1 h2 (cons ey h3 h4 (eyz)) => 
    if c:x = term G ey then 
      if ex = G.bar ey  then 
        let eqn := Eq.symm <| Eq.trans c h4
        eqn ▸ eyz
        -- by
        --   rw [c, h4]
        --   exact eyz
      else 
        cons ex h1 h2 (cons ey h3 h4 (reducePath eyz)) 
    else    
      cons ex h1 h2 (cons ey h3 h4 (reducePath eyz))

/-
inductive homotopy  {G : Graph V E} {x y z : V}: EdgePath G x y → EdgePath G x y → Type where
| consht : (x : V) → homotopy (single x) (single x)
-/