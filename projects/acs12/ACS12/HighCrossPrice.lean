import ACS12.HighCrossLogMotion

/-! The original complete crossing coefficient, including the full row-mass price. -/
namespace ACS12.HighCurrent

open Set

noncomputable def crossingCoefficient (p : ℝ) : ℝ :=
  (2 : ℝ) ^ (-p - 3) * (2 / (p - 1)) *
    (2 * (p - 1) / (p + 1)) ^ ((p + 1) / 2)

noncomputable def completeCrossPrice (p : ℝ) : ℝ :=
  crossingCoefficient p * ((35 * p + 19) / 54) ^ (2 : ℕ)

theorem crossingCoefficient_pos {p : ℝ} (hp : 1 < p) : 0 < crossingCoefficient p := by
  have hM : 0 < p - 1 := sub_pos.mpr hp
  have hP : 0 < p + 1 := by linarith only [hp]
  unfold crossingCoefficient
  positivity

theorem completeCrossPrice_pos {p : ℝ} (hp : 1 < p) : 0 < completeCrossPrice p := by
  have hM : 0 < (35 * p + 19) / 54 := by
    apply div_pos _ (by norm_num)
    linarith only [hp]
  exact mul_pos (crossingCoefficient_pos hp) (sq_pos_of_pos hM)

theorem completeCrossPrice_log {p : ℝ} (hp : 3 ≤ p) :
    Real.log (completeCrossPrice p) = completeCrossLogPrice p := by
  have hM : 0 < p - 1 := by linarith only [hp]
  have hP : 0 < p + 1 := by linarith only [hp]
  have hBase : 0 < 2 * (p - 1) / (p + 1) := div_pos (mul_pos (by norm_num) hM) hP
  have hE : 0 < (35 * p + 19) / 54 := by
    apply div_pos _ (by norm_num)
    linarith only [hp]
  unfold completeCrossPrice
  rw [Real.log_mul (crossingCoefficient_pos (by linarith only [hp])).ne' (sq_pos_of_pos hE).ne']
  unfold crossingCoefficient
  rw [Real.log_mul (mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) (div_pos (by norm_num) hM)).ne'
    (Real.rpow_pos_of_pos hBase _).ne']
  rw [Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne' (div_pos (by norm_num) hM).ne']
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),Real.log_rpow hBase,
    Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hM.ne',
    Real.log_div (mul_pos (by norm_num : (0 : ℝ) < 2) hM).ne' hP.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hM.ne',Real.log_pow]
  unfold completeCrossLogPrice
  push_cast
  ring

theorem completeCrossPrice_antitone :
    AntitoneOn completeCrossPrice (Ici 3) := by
  intro p hp q hq hpq
  change 3 ≤ p at hp
  change 3 ≤ q at hq
  have hLog := completeCrossLogPrice_strictAnti.antitoneOn hp hq hpq
  rw [← completeCrossPrice_log hp,← completeCrossPrice_log hq] at hLog
  exact (Real.log_le_log_iff
    (completeCrossPrice_pos (by linarith only [hq]))
    (completeCrossPrice_pos (by linarith only [hp]))).mp hLog

theorem completeCrossPrice_three : completeCrossPrice 3 = (961 / 11664 : ℝ) := by
  norm_num [completeCrossPrice,crossingCoefficient,Real.rpow_neg,Real.rpow_ofNat]

theorem completeCrossPrice_lt_twelfth {p : ℝ} (hp : 3 ≤ p) :
    completeCrossPrice p < 1 / 12 := by
  have h := completeCrossPrice_antitone (by norm_num : (3 : ℝ) ∈ Ici 3) hp hp
  rw [completeCrossPrice_three] at h
  linarith only [h]

end ACS12.HighCurrent
