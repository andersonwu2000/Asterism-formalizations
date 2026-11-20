import ACS12.JointFarMotion
import ACS12.JointFarLogGuards

/-! A directed bound for the complete integral term in the far curvature. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory Filter

theorem far_fifth_rpow_lower {b x : ℝ} {k : ℕ} (hb : 0 < b) (_hx : 0 ≤ x)
    (h : x ^ 5 < (b ^ k)⁻¹) : x < b ^ (-(k : ℝ) / 5) := by
  apply lt_of_pow_lt_pow_left₀ 5 (Real.rpow_nonneg hb.le _)
  rw [← Real.rpow_mul_natCast hb.le,show -(k : ℝ) / 5 * ↑(5 : ℕ) = -(k : ℝ) by push_cast; ring,
    Real.rpow_neg hb.le,Real.rpow_natCast]
  exact h

private theorem farIntegralJet_two_one :
    farIntegralJet 2 1 =
      (Real.log (21 / 8) ^ 3 - Real.log (13 / 8) ^ 3) / 3 := by
  let x : ℝ := 13 / 8
  let y : ℝ := 21 / 8
  have hx : 0 < x := by norm_num [x]
  have hxy : x ≤ y := by norm_num [x,y]
  let f (t : ℝ) := Real.log t ^ 3 / 3
  have hD (t : ℝ) (ht : t ∈ uIcc x y) : HasDerivAt f (farPowerJet 2 t 1) t := by
    rw [uIcc_of_le hxy] at ht
    have ht₀ := hx.trans_le ht.1
    convert ((Real.hasDerivAt_log ht₀.ne').pow 3).div_const 3 using 1
    unfold farPowerJet
    rw [Real.rpow_neg_one,neg_sq]
    norm_num
    ring
  have hC : ContinuousOn (fun t => farPowerJet 2 t 1) (Icc x y) := by
    intro t ht
    have ht₀ := hx.trans_le ht.1
    unfold farPowerJet
    exact ((((Real.hasDerivAt_log ht₀.ne').continuousAt.neg).pow 2).mul
      (Real.hasDerivAt_rpow_const (p := -(1 : ℝ)) (Or.inl ht₀.ne')).continuousAt).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hD (hC.intervalIntegrable_of_Icc hxy)
  rw [intervalIntegral.integral_of_le hxy] at h
  change farIntegralJet 2 1 = _
  change farIntegralJet 2 1 = f y - f x at h
  unfold f x y at h
  linarith only [h]

theorem farIntegralTerm_second_gt {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    -(115 / 1000 : ℝ) <
      (511 / 800) * farPowerJet 2 (13 / 8) p + (189 / 800) * farPowerJet 2 (21 / 8) p - farIntegralJet 2 p := by
  let x : ℝ := 13 / 8
  let y : ℝ := 21 / 8
  let a := x ^ (1 - p)
  let r := (y / x) ^ (1 - p)
  let J := farIntegralJet 2 1
  have hx : 0 < x := by norm_num [x]
  have hy : 0 < y := by norm_num [y]
  have hx₁ : 1 < x := by norm_num [x]
  have ha : 0 < a := Real.rpow_pos_of_pos hx _
  have ha₁ : a ≤ 1 := by
    unfold a
    simpa only [Real.rpow_zero] using (Real.rpow_le_rpow_left_iff hx₁).mpr (show 1 - p ≤ 0 by linarith only [hp])
  have hr : 68 / 100 < r := by
    have h := far_fifth_rpow_lower (b := 21 / 13) (x := 68 / 100) (k := 4)
      (by norm_num) (by norm_num) (by norm_num)
    apply h.trans_le
    unfold r
    rw [show y / x = (21 / 13 : ℝ) by norm_num [x,y],Nat.cast_ofNat]
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).mpr (by linarith only [hpP])
  have hX (z : ℝ) (hz : 0 < z) : z ^ (-p) = z ^ (1 - p) / z := by
    rw [← Real.rpow_sub_one hz.ne',show 1 - p - 1 = -p by ring]
  have hI : farIntegralJet 2 p ≤ a * J := by
    let μ := volume.restrict (Ioc x y)
    have hC (q : ℝ) : ContinuousOn (fun z => farPowerJet 2 z q) (Icc x y) := by
      intro z hz
      have hz₀ := hx.trans_le hz.1
      unfold farPowerJet
      exact ((((Real.hasDerivAt_log hz₀.ne').continuousAt.neg).pow 2).mul
        (Real.hasDerivAt_rpow_const (p := -q) (Or.inl hz₀.ne')).continuousAt).continuousWithinAt
    have hXY : x ≤ y := by norm_num [x,y]
    have hIntegrable (q : ℝ) : Integrable (fun z => farPowerJet 2 z q) μ :=
      ((hC q).intervalIntegrable_of_Icc hXY).1
    change (∫ z, farPowerJet 2 z p ∂μ) ≤ a * ∫ z, farPowerJet 2 z 1 ∂μ
    rw [← integral_const_mul]
    apply integral_mono_ae (hIntegrable p) ((hIntegrable 1).const_mul a)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    have hz₀ := hx.trans hz.1
    have hZ : z ^ (1 - p) ≤ a :=
      Real.rpow_le_rpow_of_nonpos hx hz.1.le (by linarith only [hp])
    have h₁ := div_le_div_of_nonneg_right hZ hz₀.le
    have h₂ := mul_le_mul_of_nonneg_left h₁ (sq_nonneg (Real.log z))
    unfold farPowerJet
    rw [hX z hz₀,Real.rpow_neg_one,neg_sq]
    exact h₂.trans_eq (by ring)
  have hY : y ^ (1 - p) = a * r := by
    unfold a r
    rw [Real.div_rpow hy.le hx.le]
    field_simp [(Real.rpow_pos_of_pos hx (1 - p)).ne']
  have hEq :
      (511 / 800) * farPowerJet 2 x p + (189 / 800) * farPowerJet 2 y p =
        a * ((511 / 800) * Real.log x ^ 2 / x + (189 / 800) * r * Real.log y ^ 2 / y) := by
    unfold farPowerJet
    rw [hX x hx,hX y hy,hY,neg_sq,neg_sq]
    ring
  have hXLog := farLog_thirteen_eighths
  have hYLog := farLog_twentyone_eighths
  have hLX : (485 / 1000 : ℝ) ^ 2 ≤ Real.log x ^ 2 := pow_le_pow_left₀ (by norm_num) hXLog.1.le _
  have hLY : (965 / 1000 : ℝ) ^ 2 ≤ Real.log y ^ 2 := pow_le_pow_left₀ (by norm_num) hYLog.1.le _
  have hUX : (485 / 1000 : ℝ) ^ 3 ≤ Real.log x ^ 3 := pow_le_pow_left₀ (by norm_num) hXLog.1.le _
  have hUY : Real.log y ^ 3 ≤ (966 / 1000 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (Real.log_nonneg (by norm_num [y])) hYLog.2.le _
  have hR := mul_le_mul hr.le hLY (by norm_num : (0 : ℝ) ≤ (965 / 1000) ^ 2)
    (by linarith only [hr] : 0 ≤ r)
  have hJ : J ≤ ((966 / 1000 : ℝ) ^ 3 - (485 / 1000 : ℝ) ^ 3) / 3 := by
    unfold J
    rw [farIntegralJet_two_one]
    linarith only [hUY,hUX]
  have hB : -(115 / 1000 : ℝ) <
      (511 / 800) * Real.log x ^ 2 / x + (189 / 800) * r * Real.log y ^ 2 / y - J := by
    unfold x y
    linarith only [hLX,hR,hJ]
  have h := mul_lt_mul_of_pos_left hB ha
  have hNeg := mul_le_mul_of_nonpos_right ha₁ (by norm_num : -(115 / 1000 : ℝ) ≤ 0)
  change _ < (511 / 800) * farPowerJet 2 x p + (189 / 800) * farPowerJet 2 y p - farIntegralJet 2 p
  rw [hEq]
  nlinarith only [h,hNeg,hI]

end ACS12.GammaMeasure
