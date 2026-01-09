import Lean
import RL.InductRename
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

/-
Goal: Find a way to debug this.
I would like to see, for a given state, the tactics that have been
executed so far.
-/
structure GoalKey where
  target : Expr
  lctx   : List (Name × Expr)
  deriving BEq, Hashable

def lctxKey (lctx : LocalContext) : List (Name × Expr) :=
  lctx.foldl (init := []) fun acc ldecl =>
    if ldecl.isImplementationDetail then acc
    else (ldecl.userName, ldecl.type) :: acc

elab "so" : tactic => do
  let env ← getEnv
  let state ← saveState
  let mut stateList : List Tactic.SavedState := []
  stateList := [state]
  let mut seen : List GoalKey := []
  while !stateList.isEmpty do
    match stateList.reverse with
    | currState :: _ =>
      restoreState currState
      stateList := stateList.dropLast
      let goals ← getGoals
      if goals.isEmpty then
        break
      let goal ← getMainGoal
      let goalTy ← instantiateMVars (← goal.getType)
      let decl ← goal.getDecl
      let lctx := decl.lctx

      let key : GoalKey := {
        target := goalTy,
        lctx   := lctxKey decl.lctx
      }

      -- if seen.contains key then
      --   continue
      seen := seen.insert key

      logInfo (← ppGoal goal)
      let msg ← ppGoal goal
      let str := msg.pretty'
      IO.FS.withFile "output.txt" IO.FS.Mode.append fun h => do
        h.putStr (str)
        h.putStr ("\n")

      if !goalTy.isConstOf ``False then
        try
            evalTactic (← `(tactic| apply False.elim))
            let newState ← saveState
            stateList := stateList ++ [newState]
            restoreState currState
        catch e =>
          pure ()

      try
        let fresh : Name := lctx.getUnusedName `h
        let ident : Ident := mkIdent fresh
        evalTactic (← `(tactic| intro $ident:ident))
        let newState ← saveState
        stateList := stateList ++ [newState]
        restoreState currState
      catch e =>
        pure ()




      for ldecl in lctx do
        if ldecl.isImplementationDetail then
          continue
        let type ← instantiateMVars ldecl.type
        let ident := mkIdent ldecl.userName
        -- induct_rename
        try
          evalTactic (← `(tactic| induct_rename $ident:ident))
          let newState ← saveState
          stateList := stateList ++ [newState]
          restoreState currState
        catch e =>
          pure ()

        -- apply
        try
            evalTactic (← `(tactic| apply $ident:ident))
            let newState ← saveState
            stateList := stateList ++ [newState]
            restoreState currState
        catch e =>
          pure ()



        -- apply ctors
      if goalTy.isConstOf ``False then
        logInfo "goal is False"
      -- not False
      let .const indName _ := goalTy.getAppFn
        | pure ()
      let env ← getEnv
      let some indInfo := env.find? indName
        | throwError "Inductive not found"
      match indInfo with
      | .inductInfo info =>
          for ctor in info.ctors do
            let ident := mkIdent ctor
            try
              evalTactic (← `(tactic| apply $ident))
              let newState ← saveState
              stateList := stateList ++ [newState]
              restoreState currState
            catch e =>
              pure ()
      | _ =>
        pure ()
    | [] => break


variable (p q r: Prop)

example : q ∨ r → q ∨ r := by so


example : q ∨ r → q ∧ r := by
  sorry

example : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by so

example : (p ∧ q) ∨ (p ∧ r)  →  p ∧ (q ∨ r):= by so

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by so



/-
let msg ← ppGoal goal
      let str := msg.pretty'
      IO.FS.withFile "output.txt" IO.FS.Mode.append fun h => do
        h.putStr (str)
        h.putStr ("\n")
-/
