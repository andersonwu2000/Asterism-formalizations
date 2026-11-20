import ACS12.JointLogEndpoint

/-! Directed rational logarithm guards for the far envelope. -/
namespace ACS12.GammaMeasure

theorem farLog_eight_sevenths :
    (1335 / 10000 : ℝ) < Real.log (8 / 7) ∧ Real.log (8 / 7) < 1336 / 10000 := by
  have hL := Real.sum_range_le_log_div (x := 1 / 15) (by norm_num) (by norm_num) 6
  have hU := Real.log_div_le_sum_range_add (x := 1 / 15) (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hL hU
  constructor <;> linarith only [hL,hU]

theorem farLog_fifteen_eighths :
    (628 / 1000 : ℝ) < Real.log (15 / 8) ∧ Real.log (15 / 8) < 629 / 1000 := by
  have hL := Real.sum_range_le_log_div (x := 7 / 23) (by norm_num) (by norm_num) 10
  have hU := Real.log_div_le_sum_range_add (x := 7 / 23) (by norm_num) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at hL hU
  constructor <;> linarith only [hL,hU]

theorem farLog_thirteen_eighths :
    (485 / 1000 : ℝ) < Real.log (13 / 8) ∧ Real.log (13 / 8) < 486 / 1000 := by
  have hL := Real.sum_range_le_log_div (x := 5 / 21) (by norm_num) (by norm_num) 8
  have hU := Real.log_div_le_sum_range_add (x := 5 / 21) (by norm_num) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at hL hU
  constructor <;> linarith only [hL,hU]

theorem farLog_twentyone_eighths :
    (965 / 1000 : ℝ) < Real.log (21 / 8) ∧ Real.log (21 / 8) < 966 / 1000 := by
  have hL := Real.sum_range_le_log_div (x := 13 / 29) (by norm_num) (by norm_num) 12
  have hU := Real.log_div_le_sum_range_add (x := 13 / 29) (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at hL hU
  constructor <;> linarith only [hL,hU]

theorem farLog_four_thirds :
    (287 / 1000 : ℝ) < Real.log (4 / 3) ∧ Real.log (4 / 3) < 288 / 1000 := by
  have hL := Real.sum_range_le_log_div (x := 1 / 7) (by norm_num) (by norm_num) 7
  have hU := Real.log_div_le_sum_range_add (x := 1 / 7) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hL hU
  constructor <;> linarith only [hL,hU]

theorem farLog_sixteen_thirteenths :
    (207 / 1000 : ℝ) < Real.log (16 / 13) ∧ Real.log (16 / 13) < 208 / 1000 := by
  have hL := Real.sum_range_le_log_div (x := 3 / 29) (by norm_num) (by norm_num) 7
  have hU := Real.log_div_le_sum_range_add (x := 3 / 29) (by norm_num) (by norm_num) 7
  norm_num [Finset.sum_range_succ] at hL hU
  constructor <;> linarith only [hL,hU]

theorem farLog_sixteen_fifteenths :
    (64 / 1000 : ℝ) < Real.log (16 / 15) ∧ Real.log (16 / 15) < 65 / 1000 := by
  have hL := Real.sum_range_le_log_div (x := 1 / 31) (by norm_num) (by norm_num) 6
  have hU := Real.log_div_le_sum_range_add (x := 1 / 31) (by norm_num) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hL hU
  constructor <;> linarith only [hL,hU]

end ACS12.GammaMeasure
