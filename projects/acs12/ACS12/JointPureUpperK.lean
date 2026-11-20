import ACS12.OuterPureMoments
import ACS12.JointMomentsPrice

/-! The complete favorable K contribution on the upper pure edge of the joint certificate. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory
open GammaDeficit (lineDensity)

private theorem jointUnit_Z_lower {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (3199 / 5000) + (19279 / 20000) * p - (49 / 1000) * p ^ 2 < pureZ p := by
  let x := 9 / 5 - p
  have hx : 0 ≤ x := sub_nonneg.mpr hP
  have hA : (287 / 1000 : ℝ) < (2 : ℝ) ^ (-(9 / 5 : ℝ)) := by
    apply (Real.rpow_lt_rpow_iff (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      (z := (5 : ℝ)) (by norm_num)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Real.rpow_neg]
  have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hE : 1 + (69 / 100) * x ≤ (2 : ℝ) ^ x := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith only [mul_le_mul_of_nonneg_right hL hx, Real.add_one_le_exp (Real.log 2 * x)]
  have hB : (3199 / 5000) - (49 / 250) * p < (2 : ℝ) ^ (-p) := by
    rw [show -p = -(9 / 5) + x by dsimp only [x]; ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have h₁ := mul_lt_mul_of_pos_right hA (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x)
    have h₂ := mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 287 / 1000)
    dsimp only [x] at h₂
    nlinarith only [h₁,h₂,hP]
  have hZ := pureZ_trapezoid_lower hp
  have h := mul_lt_mul_of_pos_right hB (show 0 < 1 + p / 4 by positivity)
  nlinarith only [hZ,h]

private theorem jointUnit_K_reference_lt {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    (p - 15 / 8) * pureZ p - (12 / 25) * pureQ p + (12 / 25) * p + 15 / 8 < -(583 / 10000) := by
  let t := p - 1
  let T : ℝ := 4 / 5
  let f (x : ℝ) := -(49 / 1000) * x ^ 3 + (1910101 / 5000000) * x ^ 2 -
    (6067413 / 20000000) * x - 1180317 / 20000000
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have htU : t ≤ T := by dsimp only [t,T]; linarith only [hP]
  have hZ := mul_lt_mul_of_neg_left (jointUnit_Z_lower hp hP)
    (show p - 15 / 8 < 0 by linarith only [hP])
  have hQ := mul_lt_mul_of_neg_left (jointQ_lower hp hP) (by norm_num : (-(12 / 25) : ℝ) < 0)
  have hE :
      (p - 15 / 8) * (3199 / 5000 + (19279 / 20000) * p - (49 / 1000) * p ^ 2) -
        (12 / 25) * ((109751 / 100000) * (p * (p + 1))) + (12 / 25) * p + 15 / 8 = f t := by
    dsimp only [f,t]
    ring
  have hC : f t ≤ (1 - t / T) * f 0 + (t / T) * f T := by
    have hC' : 0 ≤ (1910101 / 5000000) - (49 / 1000) * (t + T) := by
      dsimp only [T] at htU ⊢
      linarith only [htU]
    have h := mul_nonneg (mul_nonneg ht (sub_nonneg.mpr htU)) hC'
    dsimp only [f,T]
    dsimp only [T] at h
    linear_combination h
  have h := mul_le_mul_of_nonneg_left (show f 0 ≤ -(1180317 / 20000000) by norm_num [f])
    (sub_nonneg.mpr ((div_le_one (by norm_num [T] : 0 < T)).mpr htU))
  have h' := mul_le_mul_of_nonneg_left (show f T ≤ -(1180317 / 20000000) by norm_num [f,T])
    (div_nonneg ht (by norm_num [T] : 0 ≤ T))
  nlinarith only [hZ,hQ,hE,hC,h,h']

theorem jointOuterK_integral_le {p u t : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hu : 7 / 8 ≤ u) (hut : u ≤ t) (ht₁ : t ≤ 1) :
    (∫ s : ℝ in Ioi 0, lineDensity p s * outerK u s * BoseShape.C (s * t)) ≤ -(583 / 10000) := by
  have ht := (by norm_num : (0 : ℝ) < 7 / 8).trans_le (hu.trans hut)
  have hZ : 1 ≤ pureZ p := by
    have h := jointUnit_Z_lower hp hP
    have h' := mul_le_mul_of_nonneg_right hP (zero_le_one.trans hp)
    linarith only [h,h',hp]
  have h := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hZ)
  have hR : (p - 1 - u) * pureZ p - (12 / 25) * pureQ p + (12 / 25) * p + 1 + u ≤ -(583 / 10000) := by
    nlinarith only [h,jointUnit_K_reference_lt hp hP]
  have hPow : 1 ≤ t ^ (-p) := by
    have h := Real.rpow_le_rpow_of_exponent_ge ht ht₁ (show -p ≤ 0 by linarith only [hp])
    simpa only [Real.rpow_zero] using h
  refine (outerK_scaled_reference_le hp hP hu hut ht₁).trans ?_
  exact (mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg ht.le _)).trans
    ((mul_le_mul_of_nonpos_right hPow (by norm_num : (-(583 / 10000) : ℝ) ≤ 0)).trans_eq (one_mul _))

end ACS12.GammaMeasure
