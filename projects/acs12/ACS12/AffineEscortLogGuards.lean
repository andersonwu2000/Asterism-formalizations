import ACS12.NativeEntropyCore
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Complete positive-logarithm prefixes and controlled tails pay every escort endpoint guard. -/
namespace ACS12.NativeCells

theorem affine_log_seven_bounds :
    (97 / 50 : ℝ) < Real.log 7 ∧ Real.log 7 < (973 / 500 : ℝ) := by
  have hLower := Real.sum_range_le_log_div (x := 3 / 4) (by norm_num) (by norm_num) 8
  have hUpper := Real.log_div_le_sum_range_add (x := 3 / 4) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at hLower hUpper
  constructor <;> linarith only [hLower,hUpper]

theorem affine_log_five_bounds :
    (8 / 5 : ℝ) < Real.log 5 ∧ Real.log 5 < (161 / 100 : ℝ) := by
  have hLower := Real.sum_range_le_log_div (x := 2 / 3) (by norm_num) (by norm_num) 4
  have hUpper := Real.log_div_le_sum_range_add (x := 2 / 3) (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at hLower hUpper
  constructor <;> linarith only [hLower,hUpper]

end ACS12.NativeCells
