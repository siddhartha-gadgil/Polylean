import Lean

open Lean Meta MVarId Elab Tactic Term in
/-- A tactic to reduce the main goal, up to definitional equality. -/
elab "reduceGoal" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  withContext goal do
    let goalDecl ← getDecl goal
    let goalType := goalDecl.type
    let reducedGoalType ← Meta.withTransparency TransparencyMode.reducible <|
       reduce (skipTypes := false) (skipProofs := false) goalType
    let goal' ← MVarId.replaceTargetDefEq goal reducedGoalType
    replaceMainGoal [goal']