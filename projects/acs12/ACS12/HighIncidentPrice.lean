import ACS12.HighMinimumIncident

/-! Original minimum-incident price calibration and complete seed constants. -/
namespace ACS12.HighCurrent

theorem minimumIncidentPrice_pos {p q : ℝ} (hq : 0 < q) :
    0 < minimumIncidentPrice p q :=
  mul_pos (div_pos hq (by norm_num)) (Real.rpow_pos_of_pos (mul_pos (by norm_num) hq) _)

theorem minimumIncidentPrice_eq {p q : ℝ} (hq : 0 < q) :
    minimumIncidentPrice p q = (2 : ℝ) ^ (-1 - 1 / p) * q ^ (1 - 1 / p) := by
  have hTwo : (2 : ℝ) ^ (-1 - 1 / p) = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / p)) := by
    rw [show -1 - 1 / p = -1 + -(1 / p) by ring,Real.rpow_add (by norm_num : (0 : ℝ) < 2),Real.rpow_neg_one]
    norm_num
  have hQ : q ^ (1 - 1 / p) = q * q ^ (-(1 / p)) := by
    rw [show 1 - 1 / p = 1 + -(1 / p) by ring,Real.rpow_add hq,Real.rpow_one]
  unfold minimumIncidentPrice
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hq.le,hTwo,hQ]
  ring

theorem minimumIncidentPrice_mass_mono {p q Q : ℝ} (hp : 1 ≤ p) (hq : 0 < q) (hqQ : q ≤ Q) :
    minimumIncidentPrice p q ≤ minimumIncidentPrice p Q := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have hExponent : 0 ≤ 1 - 1 / p := by
    have h := (div_le_one hp₀).mpr hp
    linarith only [h]
  rw [minimumIncidentPrice_eq hq,minimumIncidentPrice_eq (hq.trans_le hqQ)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq.le hqQ hExponent)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le

theorem minimumIncidentPrice_exponent_le_four {p q : ℝ} (hp : 4 ≤ p)
    (hq : 0 < q) (hqHalf : q ≤ 1 / 2) :
    minimumIncidentPrice p q ≤ minimumIncidentPrice 4 q := by
  have hp₀ : 0 < p := by linarith only [hp]
  have hExp : -(1 / 4 : ℝ) ≤ -(1 / p) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hp
    linarith only [h]
  have hPow := Real.rpow_le_rpow_of_exponent_ge
    (mul_pos (by norm_num : (0 : ℝ) < 2) hq) (by linarith only [hqHalf] : 2 * q ≤ 1) hExp
  exact mul_le_mul_of_nonneg_left hPow (div_nonneg hq.le (by norm_num))

theorem minimumIncidentPrice_four_power {q : ℝ} (hq : 0 < q) :
    minimumIncidentPrice 4 q ^ (4 : ℕ) = q ^ (3 : ℕ) / 32 := by
  have hBase : 0 < 2 * q := mul_pos (by norm_num) hq
  have hPower : ((2 * q) ^ (-(1 / 4 : ℝ))) ^ (4 : ℕ) = (2 * q)⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hBase.le]
    norm_num only [Nat.cast_ofNat,show (-(1 / 4 : ℝ)) * 4 = -1 by norm_num,Real.rpow_neg_one]
  unfold minimumIncidentPrice
  rw [mul_pow,hPower]
  field_simp [hq.ne']
  <;> ring

theorem minimumIncidentPrice_seed {p q : ℝ} (hp : 4 ≤ p) (hq : 0 < q) (hqSeed : q ≤ 1 / 20) :
    minimumIncidentPrice p q < 1 / 20 := by
  have hFirst := minimumIncidentPrice_exponent_le_four hp hq (by linarith only [hqSeed])
  have hSecond := minimumIncidentPrice_mass_mono (by norm_num : (1 : ℝ) ≤ 4) hq hqSeed
  have hValue : minimumIncidentPrice 4 (1 / 20) < (1 / 20 : ℝ) := by
    have hPow := minimumIncidentPrice_four_power (by norm_num : (0 : ℝ) < 1 / 20)
    have hPos := minimumIncidentPrice_pos (p := 4) (by norm_num : (0 : ℝ) < 1 / 20)
    have hPowBound : minimumIncidentPrice 4 (1 / 20) ^ (4 : ℕ) < (1 / 20 : ℝ) ^ (4 : ℕ) := by
      rw [hPow]
      norm_num
    exact (pow_lt_pow_iff_left₀ hPos.le (by norm_num : (0 : ℝ) ≤ 1 / 20) (by decide : (4 : ℕ) ≠ 0)).mp hPowBound
  exact (hFirst.trans hSecond).trans_lt hValue

theorem minimumIncidentPrice_relative_seed {p e : ℝ} (hp : 4 ≤ p) (he : 0 < e) (heSeed : e ≤ 1 / 40) :
    minimumIncidentPrice p e < 1 / 36 := by
  have hFirst := minimumIncidentPrice_exponent_le_four hp he (by linarith only [heSeed])
  have hSecond := minimumIncidentPrice_mass_mono (by norm_num : (1 : ℝ) ≤ 4) he heSeed
  have hValue : minimumIncidentPrice 4 (1 / 40) < (1 / 36 : ℝ) := by
    have hPow := minimumIncidentPrice_four_power (by norm_num : (0 : ℝ) < 1 / 40)
    have hPos := minimumIncidentPrice_pos (p := 4) (by norm_num : (0 : ℝ) < 1 / 40)
    have hPowBound : minimumIncidentPrice 4 (1 / 40) ^ (4 : ℕ) < (1 / 36 : ℝ) ^ (4 : ℕ) := by
      rw [hPow]
      norm_num
    exact (pow_lt_pow_iff_left₀ hPos.le (by norm_num : (0 : ℝ) ≤ 1 / 36) (by decide : (4 : ℕ) ≠ 0)).mp hPowBound
  exact (hFirst.trans hSecond).trans_lt hValue

end ACS12.HighCurrent
