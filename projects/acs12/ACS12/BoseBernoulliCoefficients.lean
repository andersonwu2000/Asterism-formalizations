import Mathlib.NumberTheory.Bernoulli

/-! The finite Bernoulli coefficient recurrence needed by the complete Bose eight-moment account. -/
namespace ACS12.NativeCells
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem cubicBernoulli_0 : bernoulli' 0 = (1:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ]

theorem cubicBernoulli_1 : bernoulli' 1 = (1/2:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,cubicBernoulli_0]

theorem cubicBernoulli_2 : bernoulli' 2 = (1/6:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,cubicBernoulli_0,cubicBernoulli_1]

theorem cubicBernoulli_3 : bernoulli' 3 = (0:ℚ) := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem cubicBernoulli_4 : bernoulli' 4 = (-1/30:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,cubicBernoulli_0,cubicBernoulli_1,cubicBernoulli_2,cubicBernoulli_3]

theorem cubicBernoulli_5 : bernoulli' 5 = (0:ℚ) := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem cubicBernoulli_6 : bernoulli' 6 = (1/42:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,cubicBernoulli_0,cubicBernoulli_1,cubicBernoulli_2,cubicBernoulli_3,cubicBernoulli_4,cubicBernoulli_5]

theorem cubicBernoulli_7 : bernoulli' 7 = (0:ℚ) := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem cubicBernoulli_8 : bernoulli' 8 = (-1/30:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,cubicBernoulli_0,cubicBernoulli_1,cubicBernoulli_2,cubicBernoulli_3,cubicBernoulli_4,cubicBernoulli_5,cubicBernoulli_6,cubicBernoulli_7]

theorem cubicBernoulli_9 : bernoulli' 9 = (0:ℚ) := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem cubicBernoulli_10 : bernoulli' 10 = (5/66:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,cubicBernoulli_0,cubicBernoulli_1,cubicBernoulli_2,cubicBernoulli_3,cubicBernoulli_4,cubicBernoulli_5,cubicBernoulli_6,cubicBernoulli_7,cubicBernoulli_8,cubicBernoulli_9]

theorem cubicBernoulli_11 : bernoulli' 11 = (0:ℚ) := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem cubicBernoulli_12 : bernoulli' 12 = (-691/2730:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,cubicBernoulli_0,cubicBernoulli_1,cubicBernoulli_2,cubicBernoulli_3,cubicBernoulli_4,cubicBernoulli_5,cubicBernoulli_6,cubicBernoulli_7,cubicBernoulli_8,cubicBernoulli_9,cubicBernoulli_10,cubicBernoulli_11]

theorem cubicBernoulli_13 : bernoulli' 13 = (0:ℚ) := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem cubicBernoulli_14 : bernoulli' 14 = (7/6:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,cubicBernoulli_0,cubicBernoulli_1,cubicBernoulli_2,cubicBernoulli_3,cubicBernoulli_4,cubicBernoulli_5,cubicBernoulli_6,cubicBernoulli_7,cubicBernoulli_8,cubicBernoulli_9,cubicBernoulli_10,cubicBernoulli_11,cubicBernoulli_12,cubicBernoulli_13]

theorem cubicBernoulli_15 : bernoulli' 15 = (0:ℚ) := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem cubicBernoulli_16 : bernoulli' 16 = (-3617/510:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,cubicBernoulli_0,cubicBernoulli_1,cubicBernoulli_2,cubicBernoulli_3,cubicBernoulli_4,cubicBernoulli_5,cubicBernoulli_6,cubicBernoulli_7,cubicBernoulli_8,cubicBernoulli_9,cubicBernoulli_10,cubicBernoulli_11,cubicBernoulli_12,cubicBernoulli_13,cubicBernoulli_14,cubicBernoulli_15]

theorem cubicBernoulli_17 : bernoulli' 17 = (0:ℚ) := by
  exact bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem cubicBernoulli_18 : bernoulli' 18 = (43867/798:ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose,Finset.sum_range_succ,cubicBernoulli_0,cubicBernoulli_1,cubicBernoulli_2,cubicBernoulli_3,cubicBernoulli_4,cubicBernoulli_5,cubicBernoulli_6,cubicBernoulli_7,cubicBernoulli_8,cubicBernoulli_9,cubicBernoulli_10,cubicBernoulli_11,cubicBernoulli_12,cubicBernoulli_13,cubicBernoulli_14,cubicBernoulli_15,cubicBernoulli_16,cubicBernoulli_17]

end ACS12.NativeCells
