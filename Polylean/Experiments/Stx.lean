import Lean.Meta 
import Lean.Elab
import Mathlib.Algebra.Group.Defs
open Lean Meta Elab Term

def expr (stx: Syntax) : TermElabM Expr := do
  let e ← elabTerm stx none
  return e

def eg : TermElabM Expr :=  do 
    expr (← `(1 + 2))

#eval eg

def eg₁ : TermElabM Expr := do 
    expr (← `(∀ y : ℤ, ∀ n : ℕ,  y < ↑n + 1 + y))

#eval eg₁