import Lean
import RL.InductRename
import RL.Tags
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

structure SearchNode where
  state : Tactic.SavedState
  trace : List String

def tryTactic
(state : Tactic.SavedState)
(tactic : TacticM Unit)
(trace : List String)
(label : String)
(searchStack : List SearchNode)
: TacticM (List SearchNode) := do
  restoreState state
  try
    tactic
    let newState ← saveState
    let newNode: SearchNode := ⟨ newState, trace ++ [label] ⟩
    restoreState state
    return searchStack ++ [newNode]
  catch e =>
    return searchStack


def printSearchStack (searchStack : List SearchNode) (path : String): TacticM Unit := do
  IO.FS.withFile path IO.FS.Mode.append fun h => do h.putStrLn ("-------")
  for node in searchStack do
    let ⟨ state, trace ⟩ := node
    let goals ← getGoals
    IO.FS.withFile path IO.FS.Mode.append fun h => do h.putStrLn ("Tactics:")
    for label in trace do
      IO.FS.withFile path IO.FS.Mode.append fun h => do
        h.putStrLn (label)
    IO.FS.withFile path IO.FS.Mode.append fun h => do h.putStr ("\n")
    if goals.isEmpty then
      IO.FS.withFile path IO.FS.Mode.append fun h => do h.putStrLn ("No goals")
    for goal in goals do
      let msg ← ppGoal goal
      let goalStr := msg.pretty'
      IO.FS.withFile path IO.FS.Mode.append fun h => do
        h.putStrLn ("Resulting State:")
        h.putStr (goalStr)
        h.putStr ("\n\n")
  IO.FS.withFile path IO.FS.Mode.append fun h => do h.putStrLn ("-------")


elab "so" : tactic => do
  let state ← saveState
  let env ← getEnv
  let goal ← getMainGoal
  let decl ← goal.getDecl
  let theoremName := decl.userName

  let start : SearchNode := ⟨ state, [] ⟩
  let mut searchStack : List SearchNode := []
  searchStack := searchStack ++ [start]

  while !searchStack.isEmpty do
    match searchStack.reverse with
    | currNode :: _ => do
      --printSearchStack searchStack "output.txt"
      let ⟨ currState, currTrace ⟩ := currNode
      restoreState currState
      searchStack := searchStack.dropLast
      if (currState.tactic.goals).isEmpty then
        dbg_trace "theorem:"
        for label in currTrace do
          dbg_trace label
        break
      if currTrace.length > 7 then
        continue
      let goal ← getMainGoal
      let goalTy ← instantiateMVars (← goal.getType)
      let decl ← goal.getDecl
      let lctx := decl.lctx

      let fresh : Name := lctx.getUnusedName `h
      let freshIdent : Ident := mkIdent fresh

      /-intro-/
      let introTactic := evalTactic (← `(tactic| intro $freshIdent:ident))
      let introLabel := s!"intro {fresh}"
      searchStack ← tryTactic currState introTactic currTrace introLabel searchStack





      for ldecl in lctx do
        if ldecl.isImplementationDetail then
          continue

        let type ← instantiateMVars ldecl.type
        let ident := mkIdent ldecl.userName




        /-induct_rename-/
        let induct_renameTactic := evalTactic (← `(tactic| induct_rename $ident:ident))
        let induct_renameLabel := s!"induct_rename {ldecl.userName}"
        searchStack ← tryTactic currState induct_renameTactic currTrace induct_renameLabel searchStack
        /-apply-/
        let applyTactic := evalTactic (← `(tactic| apply $ident:ident))
        let applyLabel := s!"apply {ldecl.userName}"
        searchStack ← tryTactic currState applyTactic currTrace applyLabel searchStack




      /-goal ctor-/
      match goalTy.getAppFn with
      | .const indName _  =>
        let env ← getEnv
        let some indInfo := env.find? indName
          | throwError "Inductive not found"
        match indInfo with
        | .inductInfo info =>
            for ctor in info.ctors do
              let ctorIdent := mkIdent ctor

              let ctorTactic := evalTactic (← `(tactic| apply $ctorIdent))
              let ctorLabel := s!"apply {ctor}"
              searchStack ← tryTactic currState ctorTactic currTrace ctorLabel searchStack
        | _ => pure ()
      | _ => pure ()

      let taggedDecls := myTagAttr.ext.getState env
      --dbg_trace "Found {taggedDecls.size} tagged theorems"

      for declName in taggedDecls do
        if let some constInfo := env.find? declName then
          match constInfo with
          | .thmInfo tInfo =>
            let ident := mkIdent declName
            let rwTactic := evalTactic (← `(tactic| rw[$ident:ident]))
            let rwLabel := s!"rw[{declName}]"
            --dbg_trace "Tagged theorem available: {declName} : {tInfo.type}"
            searchStack ← tryTactic currState rwTactic currTrace rwLabel searchStack
          | _ => pure ()

       /-apply congrArg Nat.succ-/
      let congrTactic := evalTactic (← `(tactic| apply congrArg Nat.succ))
      let congrLabel := s!"intro {fresh}"
      searchStack ← tryTactic currState congrTactic currTrace congrLabel searchStack


    | _ => break



variable (p q r : Prop)

theorem t1 : p ∧ q ↔ q ∧ p := by
  sorry
attribute [my_search_tag] t1

example (h : p ∧ q ∧ r): r := by
  so
