import ACS12.OuterNative

/-! Closed pure-law formulas for the finite-value certificates. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set
open GammaDeficit (lineDensity)

noncomputable def pureRight (p u x : ℝ) : ℝ :=
  middleZ u * p * x ^ (-(p + 1)) + middleA u * p * (x + 1) ^ (-(p + 1)) -
    x ^ (-p) + (x + 1) ^ (-p)

theorem lawRightTest_zero {p L u t : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L)
    (ht : 0 < t) : lawRightTest p L 0 u t = pureRight p u t := by
  have hp₀ := zero_lt_one.trans_le hp
  have ht' := add_pos ht zero_lt_one
  rw [lawRightTest_eq_moments hp hp₂ hL ⟨le_rfl, zero_le_one⟩ ht,
    lawMoment_zero_slope hp₀ ht, lawMoment_zero_slope hp₀ ht',
    lawMoment_zero_radial hp₀ ht, lawMoment_zero_radial hp₀ ht', pureRight]
  ring

theorem lawUnitSlope_zero {p L : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) :
    lawUnitSlope p L 0 = p * powerTail (p + 1) 1 := by
  have hp₀ := zero_lt_one.trans_le hp
  have hG := (Real.Gamma_pos_of_pos hp₀).ne'
  rw [(lawUnitSlope_integral hp hp₂ hL ⟨le_rfl, zero_le_one⟩).2]
  simp only [lawDensity, sub_zero, one_mul, zero_mul, add_zero]
  have hP (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      lineDensity p s * s * scaledExpTail s 1 =
        (Real.Gamma p)⁻¹ * (s ^ p * (Real.exp (-s * (1 : ℕ)) / (1 - Real.exp (-s)))) := by
    have hs₀ : 0 < s := hs
    have hβ := scaledExpTail_bridge hs₀ zero_lt_one
    have hB : scaledExpTail s 1 = Real.exp (-s) / (1 - Real.exp (-s)) := by
      apply (eq_div_iff (expHead_den_pos hs₀).ne').mpr
      simp only [mul_one] at hβ
      linear_combination -hβ
    have hPow : s ^ (p - 1) * s = s ^ p := by
      rw [Real.rpow_sub_one hs₀.ne', div_mul_cancel₀ _ hs₀.ne']
    unfold lineDensity
    rw [hB, Nat.cast_one, mul_one, show s ^ (p - 1) / Real.Gamma p * s =
      (s ^ (p - 1) * s) / Real.Gamma p by ring, hPow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hP, integral_const_mul,
    boseMoment_integral hp₀ (show (0 : ℕ) < 1 by decide), Real.Gamma_add_one hp₀.ne']
  field_simp [hG]

theorem middleLawBase_zero {p L u : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) (hL : 0 < L) :
    middleLawBase p L 0 u = u * (1 + middleA u * p - p * powerTail (p + 1) 1) := by
  have hp₀ := zero_lt_one.trans_le hp
  rw [middleLawBase, lawUnitSlope_zero hp hp₂ hL, lawMoment_zero_radial hp₀ zero_lt_one,
    lawMoment_zero_slope hp₀ zero_lt_one]
  simp only [Real.one_rpow, mul_one, lawSelf, zero_mul, mul_zero, sub_zero]

theorem pureRight_scaled {p u t : ℝ} (ht : 0 < t) :
    pureRight p u t * t ^ p =
      p * middleZ u / t - 1 +
        (t / (t + 1)) ^ p * (1 + p * middleA u / (t + 1)) := by
  have ht' := add_pos ht zero_lt_one
  have h1 : t ^ (-p) * t ^ p = 1 := by
    rw [Real.rpow_neg ht.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos ht _).ne']
  have h2 : (t + 1) ^ (-p) * t ^ p = (t / (t + 1)) ^ p := by
    rw [Real.div_rpow ht.le ht'.le, Real.rpow_neg ht'.le, div_eq_mul_inv]
    ring
  have h3 (x : ℝ) (hx : 0 < x) : x ^ (-(p + 1)) = x ^ (-p) / x := by
    rw [show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hx.ne']
  unfold pureRight
  rw [h3 _ ht, h3 _ ht']
  calc
    _ = (t ^ (-p) * t ^ p) * (p * middleZ u / t - 1) +
        ((t + 1) ^ (-p) * t ^ p) * (1 + p * middleA u / (t + 1)) := by ring
    _ = _ := by rw [h1, h2, one_mul]

theorem pureRight_one_at_u {u : ℝ} (hu : 0 < u) :
    pureRight 1 u u = (37 * u ^ 2 + 7 * u - 12) / (25 * u * (1 + u) ^ 2) := by
  have h := pureRight_scaled (p := 1) (u := u) hu
  simp only [Real.rpow_one, one_mul, middleZ, middleA] at h
  have hD := (add_pos hu zero_lt_one).ne'
  apply (eq_div_iff (by positivity : 25 * u * (1 + u) ^ 2 ≠ 0)).mpr
  field_simp [hu.ne', hD] at h
  linear_combination h

theorem pureRight_two_powers {p u x : ℝ} (hx : 0 < x) :
    pureRight p u x = (p * middleZ u / x - 1) * x ^ (-p) +
      (1 + p * middleA u / (x + 1)) * (x + 1) ^ (-p) := by
  have hy := add_pos hx zero_lt_one
  unfold pureRight
  simp_rw [show -(p + 1) = -p - 1 by ring]
  rw [Real.rpow_sub_one hx.ne', Real.rpow_sub_one hy.ne']
  ring

end ACS12.GammaMeasure
