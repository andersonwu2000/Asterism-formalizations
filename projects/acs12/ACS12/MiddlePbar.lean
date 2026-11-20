import ACS12.PureZetaBound
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The exact Pbar guard carried from the selected middle donor. -/

namespace ACS12.GammaMeasure

open Set

noncomputable def middlePowerUpper (p : ℝ) : ℝ :=
  p * (p - 1) +
    (p - 1) * (1 / 2 - (10641 / 40000) * (p - 1)) * (1 + p / 4 + p * (p + 1) / 48)

private theorem two_rpow_top_lt : (2 : ℝ) ^ (-(9 / 5 : ℝ)) < 14359 / 50000 := by
  apply lt_of_pow_lt_pow_left₀ 5 (by norm_num)
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    show -(9 / 5 : ℝ) * ↑(5 : ℕ) = -(9 : ℝ) by norm_num,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    show (9 : ℝ) = (9 : ℕ) by norm_num, Real.rpow_natCast]
  norm_num

private theorem two_rpow_middle_le {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (2 : ℝ) ^ (-p) ≤ 1 / 2 - (10641 / 40000) * (p - 1) := by
  let b := (p - 1) / (4 / 5)
  let a := 1 - b
  have hB : 0 ≤ b := div_nonneg (sub_nonneg.mpr hp) (by norm_num)
  have hA : 0 ≤ a := by dsimp only [a, b]; linarith
  have hSum : a + b = 1 := by dsimp only [a]; ring
  have hX : a * (-1 : ℝ) + b * (-(9 / 5 : ℝ)) = -p := by dsimp only [a, b]; ring
  have hc := (convexOn_rpow_left (by norm_num : (0 : ℝ) < 2)).2
    (mem_univ (-1 : ℝ)) (mem_univ (-(9 / 5 : ℝ))) hA hB hSum
  simp only [smul_eq_mul] at hc
  have hHalf : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by rw [Real.rpow_neg_one, inv_eq_one_div]
  rw [hX, hHalf] at hc
  calc
    _ ≤ a * (1 / 2) + b * ((2 : ℝ) ^ (-(9 / 5 : ℝ))) := hc
    _ ≤ a * (1 / 2) + b * (14359 / 50000) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left two_rpow_top_lt.le hB)
    _ = _ := by dsimp only [a, b]; ring

theorem middle_powerMoment_le {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    p * (p - 1) * powerTail (p + 1) 1 ≤ middlePowerUpper p := by
  have hp₀ := zero_lt_one.trans_le hp
  have hq : 1 < p + 1 := by linarith
  have hT := powerTail_B2 hq (show (0 : ℕ) < 2 by decide)
  have hE := powerTail_shift (q := p + 1) hq 1
  simp only [Nat.cast_one, Real.one_rpow] at hE
  have hE' : powerTail (p + 1) 1 = 1 + powerTail (p + 1) 2 := by
    change powerTail (p + 1) 2 = _ at hE
    linarith
  have hA : (2 : ℝ) ^ (-(p + 1)) = (2 : ℝ) ^ (-p) / 2 := by
    rw [show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
  have hB : (2 : ℝ) ^ (-(p + 1 + 1)) = (2 : ℝ) ^ (-p) / 4 := by
    rw [show -(p + 1 + 1) = -(p + 1) - 1 by ring, Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0), hA]
    ring
  simp only [Nat.cast_ofNat, add_sub_cancel_right,
    show 1 - (p + 1) = -p by ring, hA, hB] at hT
  have hpp : 0 ≤ p * (p - 1) := mul_nonneg hp₀.le (sub_nonneg.mpr hp)
  have hCoef : 0 ≤ (p - 1) * (1 + p / 4 + p * (p + 1) / 48) :=
    mul_nonneg (sub_nonneg.mpr hp) (by positivity)
  rw [hE']
  calc
    _ ≤ p * (p - 1) * (1 + ((2 : ℝ) ^ (-p) / p + ((2 : ℝ) ^ (-p) / 2) / 2 +
        (p + 1) / 12 * ((2 : ℝ) ^ (-p) / 4))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hT.le) hpp
    _ = p * (p - 1) + (p - 1) * (1 + p / 4 + p * (p + 1) / 48) * ((2 : ℝ) ^ (-p)) := by
      field_simp [hp₀.ne']
      ring
    _ ≤ p * (p - 1) + (p - 1) * (1 + p / 4 + p * (p + 1) / 48) *
        (1 / 2 - (10641 / 40000) * (p - 1)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (two_rpow_middle_le hp hP) hCoef)
    _ = _ := by unfold middlePowerUpper; ring

theorem middlePowerUpper_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    middlePowerUpper p < p := by
  let t := p - 1
  let T : ℝ := 4 / 5
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have hT : t ≤ T := by dsimp only [t, T]; linarith
  let a : ℝ := 31 / 48
  let b : ℝ := 260043 / 320000
  let c : ℝ := 27923 / 384000
  let d : ℝ := 3547 / 640000
  let U := a + b * (T + t) - c * (T ^ 2 + T * t + t ^ 2) -
    d * (T ^ 3 + T ^ 2 * t + T * t ^ 2 + t ^ 3)
  have hD : p - middlePowerUpper p = 34351 / 12500000 + (T - t) * U := by
    unfold middlePowerUpper
    dsimp only [t, T, U, a, b, c, d]
    ring
  have ht₂ : t ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ ht hT 2
  have ht₃ : t ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ ht hT 3
  have hT₀ : 0 ≤ T := by norm_num [T]
  have hS₂ : T ^ 2 + T * t + t ^ 2 ≤ 3 * T ^ 2 := by
    nlinarith only [ht₂, mul_le_mul_of_nonneg_left hT hT₀]
  have hS₃ : T ^ 3 + T ^ 2 * t + T * t ^ 2 + t ^ 3 ≤ 4 * T ^ 3 := by
    nlinarith only [ht₃, mul_le_mul_of_nonneg_left hT (sq_nonneg T),
      mul_le_mul_of_nonneg_left ht₂ hT₀]
  have hU : 0 ≤ U := by
    have hc := mul_le_mul_of_nonneg_left hS₂ (by norm_num [c] : 0 ≤ c)
    have hd := mul_le_mul_of_nonneg_left hS₃ (by norm_num [d] : 0 ≤ d)
    have hb := mul_nonneg (by norm_num [b] : 0 ≤ b) (add_nonneg hT₀ ht)
    dsimp only [U, a, b, c, d, T] at *
    norm_num at hc hd hb ⊢
    linarith only [hc, hd, hb]
  apply sub_pos.mp
  rw [hD]
  exact add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg (sub_nonneg.mpr hT) hU)

theorem middle_powerMoment_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    p * (p - 1) * powerTail (p + 1) 1 < p :=
  (middle_powerMoment_le hp hP).trans_lt (middlePowerUpper_lt hp hP)

end ACS12.GammaMeasure

