import Lean
import RL.InductRename
import RL.Tags
open Lean Meta Elab Tactic
set_option linter.unusedVariables false
set_option maxHeartbeats 20000000



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

def printTrace (trace : List String) (path : String): TacticM Unit := do
  IO.FS.withFile path IO.FS.Mode.append fun h => do
        h.putStrLn ("---------")
  for label in trace do
    IO.FS.withFile path IO.FS.Mode.append fun h => do
        h.putStrLn (label)

elab "so" : tactic => do

  let counter ← IO.mkRef 0
  let startTime ← IO.monoMsNow


  let state ← saveState
  let env ← getEnv
  let goal ← getMainGoal
  let decl ← goal.getDecl

  let start : SearchNode := ⟨ state, [] ⟩
  let mut searchStack : List SearchNode := []
  searchStack := searchStack ++ [start]
  let mut ldeclList : List LocalDecl := []

  let goal ← getMainGoal
  let goalTy ← instantiateMVars (← goal.getType)
  let decl ← goal.getDecl
  let lctx := decl.lctx

  for ldecl in lctx do -- don't need to redo this computation
    if ldecl.isImplementationDetail then
      continue
    ldeclList := ldeclList ++ [ldecl]

  while !searchStack.isEmpty do
    match searchStack.reverse with
    | currNode :: _ => do
      let ⟨ currState, currTrace ⟩ := currNode
      restoreState currState
      searchStack := searchStack.dropLast
      if (currState.tactic.goals).isEmpty then
        break
      --printTrace currTrace "output.txt"
      if currTrace.length > 8 then
        continue

      --rw[mul_assoc]
      let rwTactic := evalTactic (← `(tactic| rw[Nat.mul_assoc]))
      let rwLabel := s!"rw[mul_assoc]"
      searchStack ← tryTactic currState rwTactic currTrace rwLabel searchStack

      --rw[←Nat.mul_assoc]
      let rwLeftTactic := evalTactic (← `(tactic| rw[← Nat.mul_assoc]))
      let rwLeftLabel := s!"rw[←mul_assoc]"
      searchStack ← tryTactic currState rwLeftTactic currTrace rwLeftLabel searchStack

      --rw[Nat.mul_one]
      let mulOneTactic := evalTactic (← `(tactic| rw[Nat.mul_one]))
      let mulOneLabel := s!"rw[mul_one]"
      searchStack ← tryTactic currState mulOneTactic currTrace mulOneLabel searchStack

      --rw[Nat.one_mul]
      let oneMulTactic := evalTactic (← `(tactic| rw[Nat.one_mul]))
      let oneMulLabel := s!"rw[one_mul]"
      searchStack ← tryTactic currState oneMulTactic currTrace oneMulLabel searchStack

      for xi in ldeclList do
        for xj in ldeclList do
          let identi := mkIdent xi.userName
          let identj := mkIdent xj.userName
          let commTactic := evalTactic (← `(tactic| rw[Nat.mul_comm $identi:ident $identj:ident]))
          let commLabel := s!"rw[mul_comm {identi} {identj}]"
          searchStack ← tryTactic currState commTactic currTrace commLabel searchStack



    | _ => break






theorem mul_idempotent_context
  (a b c : Nat) :
  a * (b * c * a) * b = a * a * b * b * c := by
  sorry






















































/-
example (a b c : Nat) :
  (a * b) * c = a * (b * c) := by so

example (a b c d : Nat) :
  ((a * b) * c) * d = a * (b * (c * d)) := by so

example (a b c d : Nat) :
  a * ((b * c) * d) = (a * b) * (c * d) := by so

example (a b : Nat) :
  (a * 1) * b = a * b := by so

example (a b c : Nat) :
  (1 * a) * (b * 1) * c = a * b * c := by so

example (a b c : Nat) :
  a * (1 * (b * c)) = (a * b) * c := by so

example (a b c : Nat) :
  (a * (b * 1)) * (1 * c) = a * b * c := by so

example (a b c d : Nat) :
  ((a * 1) * b) * (c * (1 * d)) = a * b * c * d := by so

example (a b c d : Nat) :
  (a * b) * (c * d) = a * (b * c) * d := by so

example (a b c d e : Nat) :
  (a * (b * c)) * (d * e) = a * b * (c * d) * e := by so

example (a b c : Nat) :
  a * b * c = (a * 1) * (b * (1 * c)) := by so

example (a b c d : Nat) :
  a * (b * (c * d)) = ((a * b) * c) * d := by so

example (a b c : Nat) :
  (a * b) * c = a * b * c := by so

example (a b c d : Nat) :
  a * ((b * c) * d) = a * b * c * d := by so

example (a b c d : Nat) :
  (a * b) * (c * d) = ((a * b) * c) * d := by so

theorem last (a b c d e : Nat) :
  (a * (b * c)) * (d * e) = a * ((b * c) * d) * e := by so


theorem commute_shuffle (a b c : Nat) : a * b * c = c * b * a := by
   so
-/
