import RL.MyTactic2
import RL.InductRename

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  so

example (h : p ∧ q ∧ r): r := by
  so





example : p ∨ q ↔ q ∨ p := sorry

-- associativity of ∧ and ∨
theorem t1 : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by so

#print t1

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by so
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by so
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by so
example : ¬p ∨ ¬q → ¬(p ∧ q) := by so
example : ¬(p ∧ ¬p) := by so
example : p ∧ ¬q → ¬(p → q) := by so
example : ¬p → (p → q) := by so


example : (¬p ∨ q) → (p → q) := by so
example : p ∨ False ↔ p := by so
example : p ∧ False ↔ False := by so
example : (p → q) → (¬q → ¬p) := by so
