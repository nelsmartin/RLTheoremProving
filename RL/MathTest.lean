import RL.MyTactic3
import RL.Tags
set_option maxHeartbeats 2000000


theorem add_zero (n : Nat) :  n + 0 = n := by
  so
attribute [my_search_tag] add_zero

theorem add_assoc (m n k : Nat) : n + m + k = n + (m + k) := by
  so
attribute [my_search_tag] add_assoc

theorem zero_add (n : Nat): 0 + n = n := by
  so
attribute [my_search_tag] zero_add

theorem succ_add (n m : Nat) : n + 1 + m = (n + m) + 1 := by
  so
attribute [my_search_tag] succ_add

theorem add_succ (n m : Nat) : n + m + 1 = (n + m) + 1 := by
  so
attribute [my_search_tag] succ_add

theorem add_comm (n m : Nat) : m + n = n + m := by
  so
attribute [my_search_tag] add_comm

theorem add_left_comm (n m k : Nat) : n + (m + k) = m + (n + k) := by
  so
attribute [my_search_tag] add_left_comm

theorem add_right_comm (n m k : Nat) : (n + m) + k = (n + k) + m := by
  so
attribute [my_search_tag] add_right_comm


/-! # Nat.mul theorems -/

theorem mul_zero (n : Nat) : n * 0 = 0 := by
  so
attribute [my_search_tag] mul_zero

theorem mul_succ (n m : Nat) : n * m.succ = n * m + n := by
  so
attribute [my_search_tag] mul_succ

theorem mul_add_one (n m : Nat) : n * (m + 1) = n * m + n := by
  so
attribute [my_search_tag] mul_add_one

theorem zero_mul (n : Nat) : 0 * n = 0 := by
  so
attribute [my_search_tag] zero_mul


theorem succ_mul (n m : Nat) : (n.succ) * m = (n * m) + m := by
  sorry

theorem add_one_mul (n m : Nat) : (n + 1) * m = (n * m) + m := by
  sorry

theorem mul_comm : ∀ (n m : Nat), n * m = m * n := by
  sorry

theorem mul_one : ∀ (n : Nat), n * 1 = n := by
  so

theorem one_mul (n : Nat) : 1 * n = n := by
  so

theorem left_distrib (n m k : Nat) : n * (m + k) = n * m + n * k := by
  sorry

theorem right_distrib (n m k : Nat) : (n + m) * k = n * k + m * k := by
  sorry

theorem mul_add (n m k : Nat) : n * (m + k) = n * m + n * k := by
  sorry

theorem add_mul (n m k : Nat) : (n + m) * k = n * k + m * k := by
  sorry

theorem mul_assoc : ∀ (n m k : Nat), (n * m) * k = n * (m * k) := by
  sorry

theorem mul_left_comm (n m k : Nat) : n * (m * k) = m * (n * k) := by
  sorry

theorem mul_two (n) : n * 2 = n + n := by
  sorry
theorem two_mul (n) : 2 * n = n + n := by
  sorry
/-! # Inequalities -/

theorem succ_lt_succ {n m : Nat} : n < m → n.succ < m.succ := by
  sorry

theorem le_of_lt_add_one {n m : Nat} : n < m + 1 → n ≤ m := by
  sorry
theorem lt_add_one_of_le {n m : Nat} : n ≤ m → n < m + 1 := by
  sorry

theorem sub_zero (n : Nat) : n - 0 = n := by
  so
attribute [my_search_tag] result

theorem not_add_one_le_zero (n : Nat) : ¬ n + 1 ≤ 0 := by
  sorry

theorem not_add_one_le_self : (n : Nat) → ¬ n + 1 ≤ n := by
  sorry

theorem add_one_pos (n : Nat) : 0 < n + 1 := by
  sorry

theorem pred_lt : ∀ {n : Nat}, n ≠ 0 → n.pred < n := by
  sorry

theorem sub_one_lt : ∀ {n : Nat}, n ≠ 0 → n - 1 < n := by
  sorry

theorem sub_lt_of_lt {a b c : Nat} (h : a < c) : a - b < c := by
  sorry

theorem sub_succ (n m : Nat) : n - m.succ = (n - m).pred := by
  sorry

theorem succ_sub_succ (n m : Nat) : n.succ - m.succ = n - m := by
  sorry

theorem sub_self : ∀ (n : Nat), n - n = 0 := by
  sorry

theorem sub_add_eq (a b c : Nat) : a - (b + c) = a - b - c := by
  sorry
