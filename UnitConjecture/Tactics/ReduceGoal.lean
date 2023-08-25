import Lean

open Lean Meta Elab Tactic Term

/-- A tactic to reduce the main goal, up to definitional equality. -/
def reduceGoal (transparency : TransparencyMode) : TacticM Unit := do
  let goal ← getMainGoal
  let reducedGoalType ← withTransparency transparency <| 
    reduce (skipTypes := false) (skipProofs := false) (← getMainTarget)
  let newGoal ← mkFreshExprMVar reducedGoalType
  goal.assign newGoal
  replaceMainGoal [newGoal.mvarId!]

elab "reduce_goal" tpc:ident : tactic => do
  let transparency : TransparencyMode :=
    match tpc.getId with
      |    `all    => .all
      |  `default  => .default
      | `reducible => .reducible
      | `instances => .instances
      |     _      => panic! "Unknown transparency mode"
  reduceGoal transparency

abbrev reduceGoalAll := reduceGoal .all
abbrev reduceGoalDefault := reduceGoal .default
abbrev reduceGoalReducible := reduceGoal .reducible
abbrev reduceGoalInstances := reduceGoal .instances