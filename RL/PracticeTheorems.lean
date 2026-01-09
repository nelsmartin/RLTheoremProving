import RL.MyTactic2






theorem add_zero (n : Nat) :  n + 0 = n := by
  apply rfl


theorem add_assoc (m n k : Nat) : n + m + k = n + (m + k) := by
  induction k with
  | zero => apply Eq.refl
  | succ k ih =>
    apply congrArg Nat.succ
    apply ih

theorem zero_add (n : Nat): 0 + n = n := by
  induction n with
  | zero =>
    apply Eq.refl
  | succ i ih =>
    apply congrArg Nat.succ
    apply ih


theorem succ_add (n m : Nat) : n + 1 + m = (n + m) + 1 := by
  induction m with
  | zero =>
    rw[add_zero, add_zero]
  | succ m ih =>
    apply congrArg Nat.succ
    exact ih

theorem succ_add' (n m : Nat) : n + 1 + m = (n + m) + 1 := by
  induction m with
  | zero =>
    apply add_zero
  | succ m ih =>
    apply congrArg Nat.succ
    exact ih

theorem succ_add'' (n m : Nat) : n + 1 + m = (n + m) + 1 := by
  sorry


theorem add_succ (n m : Nat) : n + m + 1 = (n + m) + 1 := by
  induction n with
  | zero => sorry
  | succ i ih => rfl


theorem result (n m : Nat) : m + n = n + m := by
  induction m with
  | zero =>
    apply zero_add
  | succ i ih =>
    rw[succ_add, add_succ]
    apply congrArg Nat.succ
    apply ih

#print Nat.add_comm
#print Nat.rec





theorem add_one_ne_zero (n : Nat) : n + 1 ≠ 0 := nofun

theorem zero_ne_add_one (n : Nat) : 0 ≠ n + 1 := by simp


theorem add_assoc' (n m k : Nat) : (n + m) + k = n + (m + k) :=
  sorry

theorem add_left_comm (n m k : Nat) : n + (m + k) = m + (n + k) := by
  sorry

theorem add_right_comm (n m k : Nat) : (n + m) + k = (n + k) + m := by
  sorry

theorem add_left_cancel (n m k : Nat) : n + m = n + k → m = k := by
  sorry

theorem add_right_cancel (n m k : Nat) (h : n + m = k + m) : n = k := by
  sorry

theorem eq_zero_of_add_eq_zero (n m : Nat) : n + m = 0 → n = 0 ∧ m = 0 := by
  sorry


theorem eq_zero_of_add_eq_zero_left (n m : Nat) (h : n + m = 0) : m = 0 :=
  sorry

/-! # Nat.mul theorems -/

theorem mul_zero (n : Nat) : n * 0 = 0 :=
  rfl

theorem mul_succ (n m : Nat) : n * m.succ = n * m + n :=
  rfl

theorem mul_add_one (n m : Nat) : n * (m + 1) = n * m + n :=
  rfl

theorem zero_mul (n : Nat) : 0 * n = 0 := by
  sorry


theorem succ_mul (n m : Nat) : (n.succ) * m = (n * m) + m := by
  sorry
theorem add_one_mul (n m : Nat) : (n + 1) * m = (n * m) + m := by
  sorry

theorem mul_comm : ∀ (n m : Nat), n * m = m * n := by
  sorry

theorem mul_one : ∀ (n : Nat), n * 1 = n := by
  sorry

theorem one_mul (n : Nat) : 1 * n = n := by
  sorry

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
  sorry

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
