import Lean

open Lean Meta Elab Tactic

/--
The `induct_rename` tactic performs induction on a hypothesis and automatically
renames all resulting ghost (inaccessible) variables with fresh names.

Usage: `induct_rename h` where h is a hypothesis in the local context.
-/
elab "induct_rename " h:ident : tactic => do
  -- First, perform induction
  evalTactic (← `(tactic| induction $h:ident))

  -- Get all goals after induction
  let allGoals ← getGoals
  let mut processedGoals : List MVarId := []

  -- Process each goal
  for goal in allGoals do
    -- Set just this goal as current
    setGoals [goal]

    -- Keep renaming until no ghost variables remain
    let mut keepGoing := true
    while keepGoing do
      let currentGoal ← getMainGoal
      let foundGhost ← currentGoal.withContext do
        let lctx ← getLCtx
        -- Find first ghost variable
        let mut ghostFound := false
        for decl in lctx do
          if decl.userName.hasMacroScopes then
            ghostFound := true
            break
        pure ghostFound

      if foundGhost then
        -- Rename the first ghost variable
        let currentGoal ← getMainGoal
        currentGoal.withContext do
          let lctx ← getLCtx
          for decl in lctx do
            if decl.userName.hasMacroScopes then
              let freshName := lctx.getUnusedName `h
              let ident := mkIdent freshName
              evalTactic (← `(tactic| rename_i $ident:ident))
              break
          pure ()
      else
        keepGoing := false

    -- Collect the goal(s) after processing
    let goalsAfterRename ← getGoals
    processedGoals := processedGoals ++ goalsAfterRename

  -- Set all processed goals
  setGoals processedGoals

-- Example usage
example (h : p ∧ q) : q ∧ p := by
  induct_rename h
  apply And.intro
  exact h
  exact h_1

example (n : Nat) (h : n = n) : True := by
  induct_rename n
  trivial
  trivial

example (xs : List Nat) : xs.length ≥ 0 := by
  induct_rename xs
  · simp
  · simp
