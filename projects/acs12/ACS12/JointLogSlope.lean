import ACS12.PureZCurvatureVariation
import ACS12.PureZCurvatureReference

/-! Sharp spatial slope bounds for the complete logarithmic-moment tails. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory intervalIntegral

private theorem scaledSlopePolynomial_le {p v : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hv : 4 ≤ v) :
    p * (p + 1) / (p + 2) ^ 2 * v ^ 2 - (4 * p + 2) / (p + 2) * v + 2 ≤
      (126 / 361) * v ^ 2 - (46 / 19) * v + 2 := by
  let B := ((47 / 5) * p + 56 / 5) * v - (114 / 5) * (p + 2)
  have hB : 0 ≤ B := by
    have h := mul_le_mul_of_nonneg_left hv (show 0 ≤ (47 / 5) * p + 56 / 5 by linarith only [hp])
    dsimp only [B]
    linarith only [h,hp]
  have h : (126 / 361) * v ^ 2 - (46 / 19) * v + 2 -
      (p * (p + 1) / (p + 2) ^ 2 * v ^ 2 - (4 * p + 2) / (p + 2) * v + 2) =
      (9 / 5 - p) * v * B / ((p + 2) ^ 2 * (19 / 5) ^ 2) := by
    have hp' : p + 2 ≠ 0 := by linarith only [hp]
    dsimp only [B]
    field_simp [hp']
    ring
  have hv₀ : 0 ≤ v := by linarith only [hv]
  apply sub_nonneg.mp
  rw [h]
  exact div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hP) hv₀) hB) (by positivity)

private theorem scaledSlopePolynomial_price {v : ℝ} (hv : 4 ≤ v) :
    Real.exp (-v) * ((126 / 361) * v ^ 2 - (46 / 19) * v + 2) < 3 / 1000 := by
  let P (z : ℝ) := (126 / 361) * z ^ 2 - (46 / 19) * z + 2
  change Real.exp (-v) * P v < _
  by_cases hV : v ≤ 59 / 10
  · have hD : P v = ((59 / 10 - v) * P 4 + (v - 4) * P (59 / 10)) / (19 / 10) -
        (126 / 361) * (v - 4) * (59 / 10 - v) := by dsimp only [P]; ring
    have hA : P 4 ≤ 0 := by norm_num [P]
    have hB : P (59 / 10) ≤ 0 := by norm_num [P]
    have hP : P v ≤ 0 := by
      rw [hD]
      exact sub_nonpos.mpr ((div_nonpos_of_nonpos_of_nonneg (add_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hV) hA)
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hv) hB)) (by norm_num)).trans
        (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hv)) (sub_nonneg.mpr hV)))
    exact (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hP).trans_lt (by norm_num)
  · let z := v - 59 / 10
    have hz : 0 ≤ z := sub_nonneg.mpr (le_of_not_ge hV)
    have hB : P v ≤ (17 / 10) * z + (7 / 20) * z ^ 2 := by
      have hEq : P v = P (59 / 10) + ((252 / 361) * (59 / 10) - 46 / 19) * z + (126 / 361) * z ^ 2 := by
        dsimp only [P,z]
        ring
      rw [hEq]
      have hA : P (59 / 10) ≤ 0 := by norm_num [P]
      nlinarith only [hA,hz,sq_nonneg z]
    have hE1 : Real.exp (-1 : ℝ) < 2 / 5 := by linarith only [Real.exp_neg_one_lt_d9]
    have hE2 : Real.exp (-2 : ℝ) < 1 / 6 := by
      have h := pow_lt_pow_left₀ (show Real.exp (-1 : ℝ) < 2 / 5 from hE1) (Real.exp_pos _).le (by decide : 2 ≠ 0)
      rw [← Real.exp_nat_mul] at h
      norm_num at h
      linarith only [h]
    have hSmall : Real.exp (-(59 / 10) : ℝ) < 1 / 350 := by
      have h := Real.sum_le_exp_of_nonneg (x := 59 / 10) (by norm_num) 13
      have h' : (350 : ℝ) < Real.exp (59 / 10) := by norm_num [Finset.sum_range_succ] at h; linarith only [h]
      rw [Real.exp_neg, ← one_div]
      exact one_div_lt_one_div_of_lt (by norm_num) h'
    have hLinear (t : ℝ) : t * Real.exp (-t) ≤ Real.exp (-1) := by
      have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (t - 1)) (Real.exp_pos (-t)).le
      rw [← Real.exp_add,show t - 1 + -t = -1 by ring] at h
      nlinarith only [h]
    have hSquare : z ^ 2 * Real.exp (-z) ≤ 4 * Real.exp (-2) := by
      have hA : 0 ≤ (z / 2) * Real.exp (-(z / 2)) := by positivity
      have h := pow_le_pow_left₀ hA (hLinear (z / 2)) 2
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul] at h
      norm_num at h
      rw [show -(2 * (z / 2)) = -z by ring] at h
      nlinarith only [h]
    have hE : Real.exp (-v) = Real.exp (-(59 / 10)) * Real.exp (-z) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [z]
      ring
    have hC : Real.exp (-z) * ((17 / 10) * z + (7 / 20) * z ^ 2) ≤ 1 := by
      nlinarith only [hLinear z,hSquare,hE1,hE2]
    rw [hE,mul_assoc]
    have hX := mul_le_mul_of_nonneg_left hB (Real.exp_pos (-z)).le
    have hY := mul_le_mul_of_nonneg_left (hX.trans hC) (Real.exp_pos (-(59 / 10))).le
    nlinarith only [hY,hSmall]

theorem zetaCurvatureSlope_gt_neg_three {p x : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hx : 4 ≤ x) :
    -(3 / 1000) < zetaCurvatureSlope p x := by
  let v := (p + 2) * Real.log x
  have hx₀ : 0 < x := (by norm_num : (0 : ℝ) < 4).trans_le hx
  have hLog : 4 / 3 < Real.log x := by
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
      ring
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hx
    linarith only [h,h4,Real.log_two_gt_d9]
  have hv : 4 ≤ v := by
    have h := mul_le_mul (show (3 : ℝ) ≤ p + 2 by linarith only [hp]) hLog.le
      (by norm_num) (by linarith only [hp])
    dsimp only [v]
    linarith only [h]
  have hEq : -zetaCurvatureSlope p x = Real.exp (-v) *
      (p * (p + 1) / (p + 2) ^ 2 * v ^ 2 - (4 * p + 2) / (p + 2) * v + 2) := by
    rw [zetaCurvatureSlope,Real.rpow_def_of_pos hx₀, show Real.log x * (-(p + 2)) = -v by dsimp only [v]; ring]
    have h : p + 2 ≠ 0 := by linarith only [hp]
    unfold peanoExponentQuadratic
    dsimp only [v]
    field_simp [h]
    ring
  have h := mul_le_mul_of_nonneg_left (scaledSlopePolynomial_le hp hP hv) (Real.exp_pos (-v)).le
  linarith only [hEq,h,scaledSlopePolynomial_price hv]

theorem zetaCurvatureSlope_four_lt {p : ℝ} (hp : 1 ≤ p) :
    zetaCurvatureSlope p 4 < 39 / 1000 := by
  let y := Real.log 4
  have hEq : y = 2 * Real.log 2 := by
    dsimp only [y]
    rw [show (4 : ℝ) = 2 * 2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hy : 1386 / 1000 < y := by linarith only [hEq,Real.log_two_gt_d9]
  have hy' : y < 1387 / 1000 := by linarith only [hEq,Real.log_two_lt_d9]
  have hFactor : peanoExponentQuadratic p y ≤ peanoExponentQuadratic 1 y := by
    have h := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sub_nonneg.mpr hp)
      (show 0 ≤ y by linarith only [hy])) (show 4 - (p + 2) * y ≤ 0 by
        have h := mul_le_mul (show (3 : ℝ) ≤ p + 2 by linarith only [hp]) hy.le (by norm_num) (by linarith only [hp])
        nlinarith only [h])
    unfold peanoExponentQuadratic
    nlinarith only [h]
  have hOne : peanoExponentQuadratic 1 y ≤ 249 / 100 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1386 / 1000) hy.le 2
    unfold peanoExponentQuadratic
    nlinarith only [h,hy']
  have hE : (4 : ℝ) ^ (-(p + 2)) ≤ 1 / 64 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (show -(p + 2) ≤ -3 by linarith only [hp])
    norm_num [Real.rpow_neg,Real.rpow_ofNat] at h
    convert h using 2 <;> ring
  rw [zetaCurvatureSlope]
  have h := mul_le_mul_of_nonneg_left (hFactor.trans hOne) (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (-(p + 2)))
  have h' := mul_le_mul_of_nonneg_right hE (by norm_num : (0 : ℝ) ≤ 249 / 100)
  linarith only [h,h']


theorem zetaCurvature_negativeVariation_le {p N : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hN : 4 ≤ N) :
    (∫ x in (4 : ℝ)..N, max 0 (-zetaCurvatureSpatial p x)) ≤ 21 / 500 := by
  obtain ⟨X,hX,hLeft,hRight⟩ := spatial_cut hp hP
  let f (x : ℝ) := zetaCurvatureSpatial p x
  let g (x : ℝ) := max 0 (-f x)
  have hC {a b : ℝ} (ha : 4 ≤ a) (hab : a ≤ b) : ContinuousOn f (Icc a b) :=
    (zetaCurvatureSpatial_continuousOn p).mono
      (fun x hx => (by norm_num : (0 : ℝ) < 4).trans_le (ha.trans hx.1))
  have hI {a b : ℝ} (ha : 4 ≤ a) (hab : a ≤ b) : IntervalIntegrable g volume a b :=
    (continuous_max.comp_continuousOn (continuousOn_const.prodMk (hC ha hab).neg)).intervalIntegrable_of_Icc hab
  have hBound (b : ℝ) (hb : 4 ≤ b) (hbX : b ≤ X) : (∫ x in (4 : ℝ)..b, g x) ≤ 21 / 500 := by
    have hEq : (∫ x in (4 : ℝ)..b, g x) = ∫ x in (4 : ℝ)..b, -f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb] at hx
      exact max_eq_right (neg_nonneg.mpr (hLeft x ⟨hx.1,hx.2.trans hbX⟩))
    rw [hEq,intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => zetaCurvatureSlope_hasDerivAt p (by
        rw [uIcc_of_le hb] at hx
        exact (by norm_num : (0 : ℝ) < 4).trans_le hx.1))
      ((hC le_rfl hb).intervalIntegrable_of_Icc hb)]
    linarith only [zetaCurvatureSlope_four_lt hp, zetaCurvatureSlope_gt_neg_three hp hP hb]
  rcases le_or_gt N X with h | h
  · exact hBound N hN h
  · have hZ : (∫ x in X..N, g x) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => 0) (fun x hx => ?_),intervalIntegral.integral_zero]
      rw [uIcc_of_le h.le] at hx
      exact max_eq_left (neg_nonpos.mpr (hRight x hx.1).1)
    have hS := intervalIntegral.integral_add_adjacent_intervals (hI le_rfl hX) (hI hX h.le)
    rw [hZ,add_zero] at hS
    rw [← hS]
    exact hBound X hX le_rfl

end ACS12.GammaMeasure
