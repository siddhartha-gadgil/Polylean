structure Graph' where
  V : Type
  E : Type
  init : E → V
  bar : E → E
  barInv : bar ∘ bar = id
  barNoFP : ∀ e: E, bar e ≠ e

structure Graph(V: Type) (E: Type) where
  init : E → V
  bar : E → E
  barInv : bar ∘ bar = id
  barNoFP : ∀ e: E, bar e ≠ e

@[inline] def term{V: Type}{E: Type}(graph: Graph V E): E → V :=
  fun e => graph.init (graph.bar e)

example : Graph Unit Bool:= 
  let init : Bool → Unit := fun e => ()
  let bar : Bool → Bool := fun e => ¬ e
  let barInv : bar ∘ bar = id := by 
    apply funext ; intro x ; cases x <;> rfl  
  let barNoFP : ∀ e: Bool, bar e ≠ e := by
    intro e; cases e <;> simp
  ⟨init, bar, barInv, barNoFP⟩

example : Graph Unit Bool:= by
  apply Graph.mk
  case init => 
    intro x; exact ()
  case bar =>
    intro x
    exact not x
  case barInv =>
    apply funext ; intro x ; cases x <;> rfl  
  case barNoFP =>
    intro e; cases e <;> simp

inductive EdgePath{V: Type}{E: Type}(graph: Graph V E): V → V → Type where
  | single : (x: V) → EdgePath graph v v
  | cons : {x y z : V} → (e : E) → graph.init e = x → term graph e = y →  
        EdgePath graph y z → EdgePath graph x z

def length{V: Type}{E: Type}{graph: Graph V E}{x y: V}: EdgePath graph x y → Nat
  | EdgePath.single x => 0
  | EdgePath.cons  _ _ _ path => length path + 1 
