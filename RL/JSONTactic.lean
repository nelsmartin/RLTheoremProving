import Lean
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

def localDeclToJson (ldecl : LocalDecl) : MetaM Json := do
  let type ← instantiateMVars ldecl.type
  let typeFmt ← ppExpr type
  return Json.mkObj [
    ("userName", Json.str ldecl.userName.toString),
    ("binderName", Json.str ldecl.fvarId.name.toString),
    ("type", Json.str typeFmt.pretty),
    ("isLet", Json.bool ldecl.isLet),
    ("implicit", Json.bool ldecl.binderInfo.isImplicit)
  ]

def goalToJson (goals : List MVarId) : MetaM Json := do
  let jsonGoals ← goals.mapM fun mvarId => do
    let g ← Meta.ppGoal mvarId
    return ("goal", Json.str s!"{g}")
  return Json.mkObj jsonGoals

elab "printJSON" : tactic => do
  let goals ← getGoals
  let goalJson ← goalToJson goals
  logInfo m!"@@GOAL_JSON@@ {goalJson}"

  try
    let goal ← getMainGoal
    let decl ← goal.getDecl
    let lctx := decl.lctx

    let mut jsonDecls : Array Json := #[]

    for ldecl in lctx do
      if ldecl.isImplementationDetail then
        continue
      let j ← localDeclToJson ldecl
      jsonDecls := jsonDecls.push j

    logInfo m!"@@LDECL_JSON@@ {Json.arr jsonDecls}"
  catch e =>
    -- Optional: tag errors too
    logInfo m!"@@TACTIC_ERROR@@ {e.toMessageData}"



elab "my_rw" "[" rules:Lean.Parser.Tactic.rwRule,* "]" : tactic => do
  try
    evalTactic (← `(tactic| rw [$rules,*]))
  catch _ =>
    pure ()



theorem rotate₃ (a b c : Nat) : a * b * c = a * b * c:= by


  sorry

  printJSON


/-
example (a * b) * c = a * (b * c) := by so

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
