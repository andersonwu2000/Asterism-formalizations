import ACS12.JointLowerRightSum
import ACS12.JointRightMomentBand
import ACS12.JointLogZBand

/-! The whole-band polynomial price for the full original right response. -/
namespace ACS12.GammaMeasure

open Set

private noncomputable def rightResponseCertificate (t : ℝ) : ℝ :=
  1290207 / 312500 + (598097 / 156250) * t + (9516743 / 10000000) * t ^ 2 +
    (1921697 / 2000000) * t ^ 3 + (113 / 25000) * t ^ 4 -
    (1691 / 10000) * t ^ 5 + (63 / 1000) * t ^ 6

private theorem rightResponseCertificate_le {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    rightResponseCertificate (p - 1) ≤ lowerRightResponseTotal p 1 := by
  let t := p - 1
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have ht' : p = t + 1 := by unfold t; ring
  have hZ : (355 / 1000 : ℝ) + t / 4 ≤ p + 1 - pureZ p := by
    have h := (pureZ_band_bounds hp hP).2
    change pureZ p < 1645 / 1000 + (3 / 4) * t at h
    linarith only [h,ht']
  have hZ' := mul_le_mul_of_nonneg_left hZ (show 0 ≤ 8 * t by positivity)
  have h₂ := mul_le_mul_of_nonneg_left (rightMoment2Lower_le hp hP)
    (show 0 ≤ 6 * (2 * p + 1) * (p + 1) by have := zero_lt_one.trans_le hp; positivity)
  have h₃ := mul_le_mul_of_nonneg_left (rightMoment3_le hp hP)
    (show 0 ≤ (6 * p + 8) * (p + 2) by have := zero_lt_one.trans_le hp; positivity)
  have h₄ := mul_le_mul_of_nonneg_left (rightMoment4_ge hp)
    (show 0 ≤ (p + 2) * (p + 3) by have := zero_lt_one.trans_le hp; positivity)
  have h₀ := sub_le_sub (add_le_add hZ' h₂) h₃
  have h := add_le_add h₀ h₄
  rw [lowerRightResponseTotal_one hp (hP.trans (by norm_num))]
  convert h using 1
  · unfold rightResponseCertificate rightMoment2Lower
    change _ = 8 * t * (355 / 1000 + t / 4) +
      6 * (2 * p + 1) * (p + 1) * (9751 / 100000 + (835 / 10000) * (9 / 5 - p) +
        (405 / 10000) * (9 / 5 - p) ^ 2 + (94 / 6000) * (9 / 5 - p) ^ 3 + (126 / 24000) * (9 / 5 - p) ^ 4) -
      (6 * p + 8) * (p + 2) * (824 / 10000 - (49 / 1000) * t) +
      (p + 2) * (p + 3) * (1 / 32 - (216875 / 10000000) * t)
    change (1290207 / 312500 : ℝ) + (598097 / 156250) * t + (9516743 / 10000000) * t ^ 2 +
      (1921697 / 2000000) * t ^ 3 + (113 / 25000) * t ^ 4 - (1691 / 10000) * t ^ 5 +
      (63 / 1000) * t ^ 6 = _
    rw [ht']
    ring

private theorem rightResponseCertificate_gt {t : ℝ} (ht : 0 ≤ t) (hT : t ≤ 4 / 5) :
    19 / 5 + 5 * t < rightResponseCertificate t := by
  let v := t - 2 / 5
  have hv : -(2 / 5 : ℝ) ≤ v := by unfold v; linarith only [ht]
  have hV : v ≤ 2 / 5 := by unfold v; linarith only [hT]
  have h₂ : v ^ 2 ≤ (2 / 5) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr hV)]
  have h₃ : -(2 / 5 : ℝ) * v ^ 2 ≤ v ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_right hv (sq_nonneg v)]
  have h₄ : v ^ 4 ≤ (2 / 5) ^ 2 * v ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right h₂ (sq_nonneg v)]
  have h₅ : v ^ 5 ≤ (2 / 5) ^ 3 * v ^ 2 := by
    have hA := mul_le_mul_of_nonneg_right hV ((by nlinarith only [sq_nonneg (v ^ 2)] : 0 ≤ v ^ 4))
    have hB := mul_le_mul_of_nonneg_left h₄ (by norm_num : (0 : ℝ) ≤ 2 / 5)
    nlinarith only [hA,hB]
  have h₆ : 0 ≤ v ^ 6 := by positivity
  have hEq : rightResponseCertificate t - (19 / 5 + 5 * t) =
      (63 / 1000) * v ^ 6 - (179 / 10000) * v ^ 5 - (2281 / 12500) * v ^ 4 +
        (1556321 / 2000000) * v ^ 3 + (20249997 / 10000000) * v ^ 2 +
        (210941 / 6250000) * v + 4512193 / 62500000 := by
    unfold rightResponseCertificate v
    ring
  apply sub_pos.mp
  rw [hEq]
  nlinarith only [h₃,h₄,h₅,h₆,hv,sq_nonneg v]

private theorem rightResponseCertificate_left_gt {t : ℝ} (ht : 0 ≤ t) (hT : t ≤ 4 / 5) :
    (516 / 100) * t + 6 * t ^ 2 < rightResponseCertificate t := by
  let d := -(63 / 1000) * t ^ 5 + (1187 / 10000) * t ^ 4 + (2261 / 25000) * t ^ 3 -
    (1776993 / 2000000) * t ^ 2 + (8675057 / 2000000) * t + 2401101 / 500000
  have h₂ := pow_le_one₀ ht (hT.trans (by norm_num : (4 / 5 : ℝ) ≤ 1)) (n := 2)
  have h₅ := pow_le_one₀ ht (hT.trans (by norm_num : (4 / 5 : ℝ) ≤ 1)) (n := 5)
  have hd : 0 ≤ d := by
    unfold d
    nlinarith only [h₂,h₅,ht,pow_nonneg ht 3,pow_nonneg ht 4]
  have hEq : rightResponseCertificate t - ((516 / 100) * t + 6 * t ^ 2) =
      2869008 / 10000000 + (4 / 5 - t) * d := by
    unfold rightResponseCertificate d
    ring
  apply sub_pos.mp
  rw [hEq]
  exact add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg (sub_nonneg.mpr hT) hd)

theorem lowerRightResponseTotal_gt {p U : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hU : U ∈ Icc 1 (7 / 6)) :
    19 / 5 + 5 * (p - 1) < lowerRightResponseTotal p U := by
  have hT : p - 1 ≤ 4 / 5 := by linarith only [hP]
  exact (rightResponseCertificate_gt (sub_nonneg.mpr hp) hT).trans_le
    ((rightResponseCertificate_le hp hP).trans
      (lowerRightResponseTotal_mono hp (hP.trans (by norm_num))
        (show (1 : ℝ) ∈ Icc 1 (7 / 6) by constructor <;> norm_num) hU hU.1))

theorem lowerRightResponseTotal_left_gt {p U : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hU : U ∈ Icc 1 (7 / 6)) :
    8 * (p - 1) * (pureZ p - 1) < lowerRightResponseTotal p U := by
  have hT : p - 1 ≤ 4 / 5 := by linarith only [hP]
  have ht := sub_nonneg.mpr hp
  have hL := mul_le_mul_of_nonneg_left (sub_le_sub_right (pureZ_band_bounds hp hP).2.le 1)
    (show 0 ≤ 8 * (p - 1) by positivity)
  have hL' : 8 * (p - 1) * (pureZ p - 1) ≤ (516 / 100) * (p - 1) + 6 * (p - 1) ^ 2 := by
    convert hL using 1
    ring
  exact hL'.trans_lt ((rightResponseCertificate_left_gt ht hT).trans_le
    ((rightResponseCertificate_le hp hP).trans
      (lowerRightResponseTotal_mono hp (hP.trans (by norm_num))
        (show (1 : ℝ) ∈ Icc 1 (7 / 6) by constructor <;> norm_num) hU hU.1)))

end ACS12.GammaMeasure
