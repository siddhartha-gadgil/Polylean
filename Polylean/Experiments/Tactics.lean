import Lean

open Lean Meta Elab Tactic Term in
elab "reduceGoal" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  withMVarContext goal do
    let goalDecl ← Lean.Meta.getMVarDecl goal
    let goalType := goalDecl.type
    let reducedGoalType ← withTransparency TransparencyMode.reducible $ reduce (skipTypes := false) (skipProofs := false) goalType
    let goal' ← replaceTargetDefEq goal reducedGoalType
    replaceMainGoal [goal']
