import Lean

open Lean Meta Elab Tactic

/--
The `so` tactic checks if the goal type is inductive.
If it is, it prints "apply c" for each constructor c that can be applied.
If the goal starts with a Pi type (∀/→), it suggests "intro" with an unused name.
For each hypothesis in the context, it suggests "induction h" if applicable.
If there are inaccessible (ghost) variables, suggests renaming them.
For each hypothesis, suggests "apply h" if applicable.
-/
elab "so" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Reduce/instantiate the goal type to get rid of lambda wrappers
  let goalType ← goal.withContext do
    instantiateMVars goalType

  -- Collect all suggestions
  let mut allSuggestions : Array String := #[]

  -- Get the head symbol of the goal type and check for constructors first
  let typeHead := goalType.getAppFn

  let constructorSuggestions ← do
    match typeHead with
    | Expr.const name _ =>
      -- Check if this constant has constructors
      let env ← getEnv
      match env.find? name with
      | some (ConstantInfo.inductInfo indVal) =>
        -- It's an inductive type, get its constructors
        let ctors := indVal.ctors
        pure (ctors.map (fun ctor => s!"apply {ctor}")).toArray
      | some _ =>
        -- Not an inductive type, but still try to apply the constant itself
        pure #[s!"apply {name}"]
      | none =>
        pure #[]
    | _ =>
      pure #[]

  allSuggestions := allSuggestions ++ constructorSuggestions

  -- Check for inaccessible variables and suggest rename_i
  let renameSuggestions ← goal.withContext do
    let lctx ← getLCtx
    let mut foundGhost := false
    let mut suggestions := #[]
    for decl in lctx do
      if !foundGhost && decl.userName.hasMacroScopes then
        let freshName := lctx.getUnusedName `h
        suggestions := suggestions.push s!"rename_i {freshName}"
        foundGhost := true
    pure suggestions

  allSuggestions := allSuggestions ++ renameSuggestions

  -- Check if the goal type starts with a Pi type (forall/implication)
  let introSuggestions ← if goalType.isForall then
    goal.withContext do
      let lctx ← getLCtx
      let unusedName := lctx.getUnusedName `h
      pure #[s!"intro {unusedName}"]
  else
    pure #[]

  allSuggestions := allSuggestions ++ introSuggestions

  -- Check each hypothesis for possible induction
  let inductionSuggestions ← goal.withContext do
    let lctx ← getLCtx
    let mut suggestions := #[]
    for decl in lctx do
      if decl.isImplementationDetail then
        continue
      if decl.userName.hasMacroScopes then
        continue
      if decl.userName.isAnonymous then
        continue
      try
        let canInduct ← withoutModifyingState do
          try
            let ident := mkIdent decl.userName
            evalTactic (← `(tactic| induction $ident:ident))
            pure true
          catch _ =>
            pure false

        if canInduct then
          suggestions := suggestions.push s!"induction {decl.userName}"
      catch _ =>
        pure ()
    pure suggestions

  allSuggestions := allSuggestions ++ inductionSuggestions

  -- Check each hypothesis for possible apply
  let applySuggestions ← goal.withContext do
    let lctx ← getLCtx
    let mut suggestions := #[]
    for decl in lctx do
      if decl.isImplementationDetail then
        continue
      if decl.userName.hasMacroScopes then
        continue
      if decl.userName.isAnonymous then
        continue
      try
        let canApply ← withoutModifyingState do
          try
            let ident := mkIdent decl.userName
            evalTactic (← `(tactic| apply $ident:ident))
            pure true
          catch _ =>
            pure false

        if canApply then
          suggestions := suggestions.push s!"apply {decl.userName}"
      catch _ =>
        pure ()
    pure suggestions

  allSuggestions := allSuggestions ++ applySuggestions

  -- Deduplicate and print all suggestions
  let uniqueSuggestions := allSuggestions.toList.eraseDups
  for suggestion in uniqueSuggestions do
    logInfo m!"{suggestion}"

-- Example usage
example (n : Nat): n + 2 = 2 + n:= by
  grind
