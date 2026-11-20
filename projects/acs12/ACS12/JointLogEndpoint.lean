import ACS12.PowerLogTailBounds
import ACS12.PureAdjacentValueData
import ACS12.PureNativeOneValue

/-! Exact endpoint log moments with complete directed tails for W22 and W24. -/
namespace ACS12.GammaMeasure

private theorem log_site_guards :
    ((693147 / 1000000 : ℝ) < Real.log 2 ∧ Real.log 2 < 693148 / 1000000) ∧
    ((1098612 / 1000000 : ℝ) < Real.log 3 ∧ Real.log 3 < 1098613 / 1000000) ∧
    ((1386294 / 1000000 : ℝ) < Real.log 4 ∧ Real.log 4 < 1386295 / 1000000) ∧
    ((1609437 / 1000000 : ℝ) < Real.log 5 ∧ Real.log 5 < 1609438 / 1000000) ∧
    ((1791759 / 1000000 : ℝ) < Real.log 6 ∧ Real.log 6 < 1791760 / 1000000) ∧
    ((1945910 / 1000000 : ℝ) < Real.log 7 ∧ Real.log 7 < 1945911 / 1000000) ∧
    ((2079441 / 1000000 : ℝ) < Real.log 8 ∧ Real.log 8 < 2079442 / 1000000) ∧
    ((2197224 / 1000000 : ℝ) < Real.log 9 ∧ Real.log 9 < 2197225 / 1000000) ∧
    ((2302585 / 1000000 : ℝ) < Real.log 10 ∧ Real.log 10 < 2302586 / 1000000) := by
  have hM3 : (405465108 / 1000000000 : ℝ) < Real.log (3 / 2) ∧ Real.log (3 / 2) < 405465109 / 1000000000 := by
    have hL := Real.sum_range_le_log_div (x := 1 / 5) (by norm_num) (by norm_num) 8
    have hU := Real.log_div_le_sum_range_add (x := 1 / 5) (by norm_num) (by norm_num) 8
    norm_num [Finset.sum_range_succ] at hL hU
    constructor <;> linarith only [hL,hU]
  have hM5 : (223143551 / 1000000000 : ℝ) < Real.log (5 / 4) ∧ Real.log (5 / 4) < 223143552 / 1000000000 := by
    have hL := Real.sum_range_le_log_div (x := 1 / 9) (by norm_num) (by norm_num) 8
    have hU := Real.log_div_le_sum_range_add (x := 1 / 9) (by norm_num) (by norm_num) 8
    norm_num [Finset.sum_range_succ] at hL hU
    constructor <;> linarith only [hL,hU]
  have hM7 : (559615787 / 1000000000 : ℝ) < Real.log (7 / 4) ∧ Real.log (7 / 4) < 559615788 / 1000000000 := by
    have hL := Real.sum_range_le_log_div (x := 3 / 11) (by norm_num) (by norm_num) 10
    have hU := Real.log_div_le_sum_range_add (x := 3 / 11) (by norm_num) (by norm_num) 10
    norm_num [Finset.sum_range_succ] at hL hU
    constructor <;> linarith only [hL,hU]
  have hM9 : (117783035 / 1000000000 : ℝ) < Real.log (9 / 8) ∧ Real.log (9 / 8) < 117783036 / 1000000000 := by
    have hL := Real.sum_range_le_log_div (x := 1 / 17) (by norm_num) (by norm_num) 8
    have hU := Real.log_div_le_sum_range_add (x := 1 / 17) (by norm_num) (by norm_num) 8
    norm_num [Finset.sum_range_succ] at hL hU
    constructor <;> linarith only [hL,hU]
  have h2 : (693147 / 1000000 : ℝ) < Real.log 2 ∧ Real.log 2 < 693148 / 1000000 := by
    constructor <;> linarith only [Real.log_two_gt_d9,Real.log_two_lt_d9]
  have h3 : (1098612 / 1000000 : ℝ) < Real.log 3 ∧ Real.log 3 < 1098613 / 1000000 := by
    rw [show (3 : ℝ) = (2 : ℝ) ^ 1 * (3 / 2) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
    constructor <;> linarith only [Real.log_two_gt_d9,Real.log_two_lt_d9,hM3.1,hM3.2]
  have h4 : (1386294 / 1000000 : ℝ) < Real.log 4 ∧ Real.log 4 < 1386295 / 1000000 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2  by norm_num,
      Real.log_pow]
    norm_num
    constructor <;> linarith only [Real.log_two_gt_d9,Real.log_two_lt_d9]
  have h5 : (1609437 / 1000000 : ℝ) < Real.log 5 ∧ Real.log 5 < 1609438 / 1000000 := by
    rw [show (5 : ℝ) = (2 : ℝ) ^ 2 * (5 / 4) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
    constructor <;> linarith only [Real.log_two_gt_d9,Real.log_two_lt_d9,hM5.1,hM5.2]
  have h6 : (1791759 / 1000000 : ℝ) < Real.log 6 ∧ Real.log 6 < 1791760 / 1000000 := by
    rw [show (6 : ℝ) = (2 : ℝ) ^ 2 * (3 / 2) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
    constructor <;> linarith only [Real.log_two_gt_d9,Real.log_two_lt_d9,hM3.1,hM3.2]
  have h7 : (1945910 / 1000000 : ℝ) < Real.log 7 ∧ Real.log 7 < 1945911 / 1000000 := by
    rw [show (7 : ℝ) = (2 : ℝ) ^ 2 * (7 / 4) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
    constructor <;> linarith only [Real.log_two_gt_d9,Real.log_two_lt_d9,hM7.1,hM7.2]
  have h8 : (2079441 / 1000000 : ℝ) < Real.log 8 ∧ Real.log 8 < 2079442 / 1000000 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ 3  by norm_num,
      Real.log_pow]
    norm_num
    constructor <;> linarith only [Real.log_two_gt_d9,Real.log_two_lt_d9]
  have h9 : (2197224 / 1000000 : ℝ) < Real.log 9 ∧ Real.log 9 < 2197225 / 1000000 := by
    rw [show (9 : ℝ) = (2 : ℝ) ^ 3 * (9 / 8) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
    constructor <;> linarith only [Real.log_two_gt_d9,Real.log_two_lt_d9,hM9.1,hM9.2]
  have h10 : (2302585 / 1000000 : ℝ) < Real.log 10 ∧ Real.log 10 < 2302586 / 1000000 := by
    rw [show (10 : ℝ) = (2 : ℝ) ^ 3 * (5 / 4) by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
    constructor <;> linarith only [Real.log_two_gt_d9,Real.log_two_lt_d9,hM5.1,hM5.2]
  exact ⟨h2,h3,h4,h5,h6,h7,h8,h9,h10⟩

theorem log_three_tight : (1098612 / 1000000 : ℝ) < Real.log 3 ∧ Real.log 3 < 1098613 / 1000000 :=
  log_site_guards.2.1

theorem powerLogTail_prefix_split {q : ℝ} (hq : 1 < q) (k n : ℕ) :
    powerLogTail q k 1 =
      (∑ j : Fin n, (1 + (j.val : ℝ)) ^ (-q) * Real.log (1 + (j.val : ℝ)) ^ k) +
        powerLogTail q k (1 + n) := by
  have h := (powerLogTail_summable hq k 1 le_rfl).sum_add_tsum_nat_add n
  simp only [Nat.cast_one] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  have hTail : (∑' j : ℕ, (1 + ((j + n : ℕ) : ℝ)) ^ (-q) * Real.log (1 + ((j + n : ℕ) : ℝ)) ^ k) =
      powerLogTail q k (1 + n) := by
    unfold powerLogTail
    apply tsum_congr
    intro j
    push_cast
    rw [show 1 + ((j : ℝ) + n) = 1 + n + j by ring]
  rw [hTail] at h
  simpa only [powerLogTail,Nat.cast_one] using h.symm

theorem logMoment_two_bounds :
    (937 / 1000 : ℝ) < powerLogTail 2 1 1 ∧ powerLogTail 2 1 1 < 938 / 1000 := by
  obtain ⟨h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := log_site_guards
  have hT := powerLogTail_trapezoid (q := 2) (m := 10) (by norm_num) (by decide)
  have hS := powerLogTail_prefix_split (q := 2) (by norm_num) 1 9
  norm_num [Fin.sum_univ_succ,Real.rpow_neg,Real.rpow_ofNat,Real.rpow_two] at hS hT
  constructor <;> linarith only [hS,hT.1,hT.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2,h9.1,h9.2,h10.1,h10.2]

theorem logMoment_three_bounds :
    (198 / 1000 : ℝ) < powerLogTail 3 1 1 ∧ powerLogTail 3 1 1 < 199 / 1000 := by
  obtain ⟨h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := log_site_guards
  have hT := powerLogTail_trapezoid (q := 3) (m := 10) (by norm_num) (by decide)
  have hS := powerLogTail_prefix_split (q := 3) (by norm_num) 1 9
  norm_num [Fin.sum_univ_succ,Real.rpow_neg,Real.rpow_ofNat] at hS hT
  constructor <;> linarith only [hS,hT.1,hT.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2,h9.1,h9.2,h10.1,h10.2]

theorem powerTail_three_bounds : (1202 / 1000 : ℝ) < powerTail 3 1 ∧ powerTail 3 1 < 12021 / 10000 := by
  have hL := powerTail_trapezoid_lower (q := 3) (m := 10) (by norm_num) (by decide)
  have hU := powerTail_B2 (q := 3) (m := 10) (by norm_num) (by decide)
  have hS := powerTail_prefix_split (q := 3) (by norm_num) 9
  norm_num [Fin.sum_univ_succ,Real.rpow_neg,Real.rpow_ofNat,Real.rpow_two] at hS hL hU
  constructor <;> linarith only [hS,hL,hU]

end ACS12.GammaMeasure
