import ACS12.QuarticCountIncident
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace ACS12.HighCurrent
open Set

private theorem count_power_difference {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y)
    (hy₁ : y ≤ 1) (hxy : x < y) :
    y^(5/4:ℝ)-x^(5/4:ℝ) ≤ (5/4)*(y-x) := by
  have h := (convexOn_rpow (by norm_num : (1:ℝ) ≤ 5/4)).slope_le_of_hasDerivAt
    hx hy.le hxy (Real.hasDerivAt_rpow_const (Or.inl hy.ne'))
  rw [slope_def_field,div_le_iff₀ (sub_pos.mpr hxy)] at h
  have hpow : y^((5/4:ℝ)-1) ≤ 1 := Real.rpow_le_one hy.le hy₁ (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr hxy.le)
  nlinarith

theorem quarticCount_lower_loss {r z k q : ℝ}
    (hr : r ∈ Icc 0 1) (hz : z ∈ Icc 0 (691/2000))
    (hk : k ∈ Icc 0 (64/169)) (hq : 0<q) (hqU : q≤3/4)
    (hCorr : (q/(3/4))^r*k ≤ (2:ℝ)^r*z^2) :
    quarticCountConstant*(1-(2:ℝ)^r*z^2)^(5/4:ℝ) -
      quarticCountConstant*(1-k)^(5/4:ℝ) ≤
      (8471/10000)*(5/4)*((64/169)/(3/4))*(3/4-q) := by
  let K := (2:ℝ)^r*z^2
  have h2 : (2:ℝ)^r ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hr.2
  have hzsq : z^2 ≤ (691/2000:ℝ)^2 := sq_le_sq₀ hz.1 (by norm_num) |>.mpr hz.2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hK₁ : K < 1 := by
    have h := mul_le_mul_of_nonneg_right h2 (sq_nonneg z)
    dsimp [K]; nlinarith
  have ht : q/(3/4:ℝ) ≤ 1 := (div_le_one (by norm_num)).mpr hqU
  have ht₀ : 0 ≤ q/(3/4:ℝ) := by positivity
  have hl := (mul_le_mul_of_nonneg_right
    (Real.self_le_rpow_of_le_one ht₀ ht hr.2) hk.1).trans hCorr
  have hmul := mul_nonneg (sub_nonneg.mpr hk.2) (sub_nonneg.mpr ht)
  have hgap : k-K ≤ ((64/169)/(3/4))*(3/4-q) := by dsimp [K]; nlinarith
  have hd : 0 ≤ 3/4-q := sub_nonneg.mpr hqU
  have hR : 0 ≤ ((64/169)/(3/4:ℝ))*(3/4-q) := by positivity
  have hc : 0 < quarticCountConstant := lt_trans (by norm_num) quarticCountConstant_lower
  by_cases h : K < k
  · have hp := count_power_difference (by linarith [hk.2] : 0 ≤ 1-k)
      (sub_pos.mpr hK₁) (by linarith : 1-K ≤ 1) (by linarith : 1-k < 1-K)
    have hb : (1-K)^(5/4:ℝ)-(1-k)^(5/4:ℝ) ≤ (5/4)*(((64/169)/(3/4))*(3/4-q)) := by linarith
    have hm := mul_le_mul_of_nonneg_left hb hc.le
    have hu := mul_le_mul_of_nonneg_right quarticCountConstant_upper.le
      (show 0 ≤ (5/4:ℝ)*(((64/169)/(3/4))*(3/4-q)) by positivity)
    dsimp [K] at hm
    nlinarith
  · have hp := Real.rpow_le_rpow (sub_nonneg.mpr hK₁.le)
      (show 1-K ≤ 1-k by linarith) (by norm_num : (0:ℝ) ≤ 5/4)
    have hm := mul_le_mul_of_nonneg_left hp hc.le
    dsimp [K] at hm
    have hu : 0 ≤ (8471/10000:ℝ)*(5/4)*((64/169)/(3/4))*(3/4-q) := by positivity
    linarith


theorem quarticCount_transfer {r z k q J : ℝ}
    (hr : r ∈ Icc 0 1) (hz : z ∈ Icc 0 (691/2000))
    (hk : k ∈ Icc 0 (64/169)) (hq : 0<q) (hqU : q≤3/4)
    (hCorr : (q/(3/4))^r*k ≤ (2:ℝ)^r*z^2)
    (hLo : quarticCountConstant*(1-k)^(5/4:ℝ) ≤ J)
    (hHi : J ≤ q*(2*q)^(-(r/4))*Real.sqrt (1-z)+(1/16-5*z^2/64)) : False := by
  have hLoss := quarticCount_lower_loss hr hz hk hq hqU hCorr
  have hGain := quarticCount_incident_gain hr hq hqU hz
  have hV := quarticCount_scalar_pos hr hz
  have hd : 0 ≤ 3/4-q := sub_nonneg.mpr hqU
  nlinarith only [hLoss,hGain,hV,hLo,hHi,hd]

end ACS12.HighCurrent
