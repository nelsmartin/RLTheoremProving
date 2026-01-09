import Lean
import RL.InductRename
open Lean Meta Elab Tactic
set_option linter.unusedVariables false

structure SearchNode where
  state : Tactic.SavedState
  trace : List String
