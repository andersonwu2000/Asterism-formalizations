import ACS12.PureRightExponentShape
import ACS12.PureNativeBasics
import ACS12.TrapezoidPositive

/-! Exponent derivatives of the exact pure right kernel and their active-site lower bound. -/

namespace ACS12.GammaMeasure

open Set MeasureTheory

noncomputable def pureRightExponentD (p u x : ℝ) : ℝ :=
  x ^ (-p) * Real.log x - (x + 1) ^ (-p) * Real.log (x + 1) -
    middleZ u * logTailPower p x - middleA u * logTailPower p (x + 1)

theorem pureRight_exponent_deriv {p u x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun q => pureRight q u x) (pureRightExponentD p u x) p := by
  have hy := add_pos hx zero_lt_one
  have hP (x : ℝ) (hx : 0 < x) :=
    ((hasDerivAt_id p).neg.const_rpow hx)
  have h₁ := zetaTerm_exponent_hasDerivAt hx p
  have h₂ := zetaTerm_exponent_hasDerivAt hy p
  convert (((h₁.const_mul (middleZ u)).add (h₂.const_mul (middleA u))).sub (hP x hx)).add (hP (x + 1) hy) using 1
  · funext q
    simp only [pureRight, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq]
    ring
  · simp only [pureRightExponentD, logTailPower, Pi.neg_apply, id_eq]
    ring

theorem pureRightExponentD_pos_of_log_le {p u x : ℝ} (hp : 0 < p) (hx : 0 < x)
    (hLog : Real.log x ≤ 1 / p) (hG : 0 < pureRight p u x) :
    0 < pureRightExponentD p u x := by
  let y := x + 1
  let t := Real.log y - Real.log x
  let a := middleA u
  have hy : 0 < y := add_pos hx zero_lt_one
  have ht : 0 < t := sub_pos.mpr (Real.log_lt_log hx (by dsimp only [y]; linarith))
  have hT : 1 / y ≤ t := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
    rw [Real.log_div hy.ne' hx.ne', inv_div] at h
    change 1 - x / y ≤ t at h
    have hE : 1 - x / y = 1 / y := by
      dsimp only [y]
      field_simp [show x + 1 ≠ 0 from hy.ne']
      ring
    exact hE ▸ h
  have hA : a ≤ 6 / 25 := middleA_le u
  have hP : 0 < t / 2 - a / y := by
    have hQ := (div_lt_div_iff_of_pos_right hy).mpr (show a < 1 / 2 by linarith only [hA])
    have hT' : (1 / 2) / y ≤ t / 2 := by
      calc
        _ = (1 / y) / 2 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hT (by norm_num)
    exact sub_pos.mpr (hQ.trans_le hT')
  have hExp : y ^ (-p) * Real.exp (p * t) = x ^ (-p) := by
    rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hx, ← Real.exp_add]
    congr 1
    dsimp only [t]
    ring
  have hB : 0 < (Real.exp (p * t) - 1) / p - t * (1 + p * a / y) := by
    have h := Real.quadratic_le_exp_of_nonneg (mul_pos hp ht).le
    have hN := mul_pos (mul_pos hp ht) hP
    have hI := (div_le_div_iff_of_pos_right hp).mpr (show p * t + (p * t) ^ 2 / 2 ≤ Real.exp (p * t) - 1 by linarith only [h])
    have hJ : (p * t + (p * t) ^ 2 / 2) / p = t + p * t ^ 2 / 2 := by
      field_simp [hp.ne'] <;> ring
    rw [hJ] at hI
    have hE : t + p * t ^ 2 / 2 - t * (1 + p * a / y) = p * t * (t / 2 - a / y) := by ring
    exact (hE.symm ▸ hN).trans_le (sub_le_sub_right hI _)
  have hEq : pureRightExponentD p u x = (1 / p - Real.log x) * pureRight p u x +
      y ^ (-p) * ((Real.exp (p * t) - 1) / p - t * (1 + p * a / y)) := by
    rw [pureRight_two_powers hx]
    unfold pureRightExponentD logTailPower
    rw [show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hx.ne', Real.rpow_sub_one hy.ne']
    have hE : y ^ (-p) * ((Real.exp (p * t) - 1) / p - t * (1 + p * a / y)) =
        (x ^ (-p) - y ^ (-p)) / p - y ^ (-p) * t * (1 + p * a / y) := by
      rw [mul_sub, ← mul_div_assoc, mul_sub, hExp, mul_one]
      ring
    rw [hE]
    dsimp only [t, a]
    change _ = (1 / p - Real.log x) * ((p * middleZ u / x - 1) * x ^ (-p) +
      (1 + p * middleA u / y) * y ^ (-p)) + _
    field_simp [hx.ne', hy.ne', hp.ne']
    ring
  rw [hEq]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hLog) hG.le)
    (mul_pos (Real.rpow_pos_of_pos hy _) hB)

private theorem logTailPrimitive_hasDerivAt (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => -(t ^ (-p) * Real.log t)) (logTailPower p x) x := by
  have h := (Real.hasDerivAt_rpow_const (p := -p) (Or.inl hx.ne')).mul (Real.hasDerivAt_log hx.ne')
  convert h.neg using 1
  rw [logTailPower, show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hx.ne']
  field_simp [hx.ne']
  ring

private theorem logTail_integral_ge {p x : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) (hx : 1 ≤ x) :
    (logTailPower p x + logTailPower p (x + 1)) / 2 - 1 / 600 ≤
      x ^ (-p) * Real.log x - (x + 1) ^ (-p) * Real.log (x + 1) := by
  have hx₀ := zero_lt_one.trans_le hx
  have hI : x ≤ x + 1 := by linarith
  have hP₀ (t : ℝ) (ht : t ∈ Icc x (x + 1)) : 0 < t := hx₀.trans_le ht.1
  have hE := ACS12.trapezoidalError_unit_le_of_second_le (M := 1 / 50)
    (fun t ht => logTailPower_deriv p (hP₀ t ht)) (fun t ht => logTailSlope_deriv p (hP₀ t ht))
    ((logTailSecond_continuousOn p).mono hP₀) (fun t ht => logTailSecond_le hp hP (hx.trans ht.1))
  have hC : ContinuousOn (logTailPower p) (Icc x (x + 1)) :=
    fun t ht => (logTailPower_deriv p (hP₀ t ht)).continuousAt.continuousWithinAt
  have hQ := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => logTailPrimitive_hasDerivAt p (hP₀ t (by rwa [uIcc_of_le hI] at ht)))
    (hC.intervalIntegrable_of_Icc (μ := volume) hI)
  rw [trapezoidal_error, trapezoidal_integral_one, hQ] at hE
  nlinarith only [hE]

theorem pureRightExponentD_gt_neg {p u x : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hu : 0 < u) (hu' : u ≤ 7 / 8) (hx : 0 < x) (hG : 0 < pureRight p u x) :
    -(1 / 600) < pureRightExponentD p u x := by
  have hp₀ := zero_lt_one.trans_le hp
  rcases le_or_gt (Real.log x) (1 / p) with h | h
  · exact (by norm_num : -(1 / 600 : ℝ) < 0).trans (pureRightExponentD_pos_of_log_le hp₀ hx h hG)
  have hx₁ : 1 ≤ x := by
    by_contra! h'
    exact (not_lt_of_ge (le_of_lt h)) ((Real.log_neg hx h').trans (one_div_pos.mpr hp₀))
  have hI := logTail_integral_ge hp hP hx₁
  have hxP := logTailPower_pos hp₀ hx h
  have hy := add_pos hx zero_lt_one
  have hyP := logTailPower_pos hp₀ hy (h.trans_le (Real.log_le_log hx (le_add_of_nonneg_right zero_le_one)))
  have hR := logTailPower_next_ratio hp hP hx h
  have ha : middleA u ≤ 189 / 800 := by
    unfold middleA
    have hU := mul_nonneg (sub_nonneg.mpr hu') (show 0 ≤ 2 - 7 / 8 - u by linarith only [hu'])
    nlinarith only [hU]
  have hz : middleZ u ≤ 511 / 800 := by
    unfold middleZ middleA
    have hU := pow_le_pow_left₀ hu.le hu' 2
    nlinarith only [hU, hu']
  have ha' := mul_le_mul_of_nonneg_right ha hyP.le
  have hz' := mul_le_mul_of_nonneg_right hz hxP.le
  unfold pureRightExponentD
  nlinarith only [hI, hR, ha', hz', hyP]

end ACS12.GammaMeasure
