import ACS12.PureNativeUpperPrice

/-! The directed native curvature lower throughout the upper gap interval. -/

namespace ACS12.GammaMeasure

open Set

private theorem lowerPower {b v : ℝ} (hb : 0 < b) (hv : 0 ≤ v)
    (h : v ^ 5 < (b ^ 9)⁻¹) : v < b ^ (-(9 / 5 : ℝ)) := by
  apply (Real.rpow_lt_rpow_iff hv (Real.rpow_nonneg hb.le _) (z := (5 : ℝ)) (by norm_num)).mp
  rw [← Real.rpow_mul hb.le, show -(9 / 5 : ℝ) * 5 = -(9 : ℝ) by ring,
    Real.rpow_neg hb.le, show (9 : ℝ) = (9 : ℕ) by norm_num, Real.rpow_natCast,
    show (5 : ℝ) = (5 : ℕ) by norm_num, Real.rpow_natCast]
  exact h

private theorem nativeAtU :
    pureNativeBandDD (7 / 8) (9 / 5) > 49 / 500 := by
  let l := nativeL (7 / 8)
  let t := nativeT (7 / 8)
  let x := (7 / 8 : ℝ) ^ (-(9 / 5 : ℝ))
  let y := (15 / 8 : ℝ) ^ (-(9 / 5 : ℝ))
  have hl : 1335 / 10000 < l := nativeL_sevenEighths_bounds.1
  have hl' : l < 134 / 1000 := nativeL_sevenEighths_bounds.2
  have ht : 628 / 1000 < t := by
    have h := Real.sum_range_le_log_div (x := 7 / 23) (by norm_num) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at h
    dsimp only [t, nativeT]
    norm_num
    linarith only [h]
  have ht' : t < 629 / 1000 := (nativeT_upper_band (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8) le_rfl).2
  have hx : 12716 / 10000 < x := lowerPower (by norm_num) (by norm_num) (by norm_num)
  have hx' : x < 1272 / 1000 := by
    dsimp only [x]
    simpa only [neg_div] using fifth_rpow_upper (k := 9) (b := 7 / 8) (x := 1272 / 1000)
      (by norm_num) (by norm_num) (by norm_num)
  have hy : 3225 / 10000 < y := lowerPower (by norm_num) (by norm_num) (by norm_num)
  have hl₀ : 0 ≤ l := by linarith only [hl]
  have ht₀ : 0 ≤ t := by linarith only [ht]
  have hL₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1335 / 10000) hl.le 2
  have hT₂ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 628 / 1000) ht.le 2
  have hG1 : x * (73 / 100 + (314 / 1000) * l) -
      y * ((12268 / 10000) * t - 126 / 1000) < 775 / 1000 := by
    have h₁ := mul_le_mul hx'.le (show 73 / 100 + (314 / 1000) * l ≤ 73 / 100 + (314 / 1000) * (134 / 1000) by
      linarith only [hl']) (by positivity) (by norm_num : (0 : ℝ) ≤ 1272 / 1000)
    have h₂ := mul_le_mul hy.le
      (show (12268 / 10000) * (628 / 1000) - 126 / 1000 ≤ (12268 / 10000) * t - 126 / 1000 by linarith only [ht])
      (by linarith only [ht]) (show 0 ≤ y by linarith only [hy])
    linarith only [h₁, h₂]
  have hG2 : 3598 / 10000 < x * ((146 / 100) * l + (314 / 1000) * l ^ 2) +
      y * ((12268 / 10000) * t ^ 2 - (252 / 1000) * t) := by
    have h₁ := mul_le_mul hx.le
      (show (146 / 100) * (1335 / 10000) + (314 / 1000) * (1335 / 10000) ^ 2 ≤
        (146 / 100) * l + (314 / 1000) * l ^ 2 by linarith only [hl, hL₂])
      (by positivity) (show 0 ≤ x by linarith only [hx])
    have h₂ := mul_le_mul hy.le
      (show (12268 / 10000) * (628 / 1000) ^ 2 - (252 / 1000) * (629 / 1000) ≤
        (12268 / 10000) * t ^ 2 - (252 / 1000) * t by linarith only [hT₂, ht'])
      (by linarith only [hT₂, ht']) (show 0 ≤ y by linarith only [hy])
    linarith only [h₁, h₂]
  have hR : adjacentRatio (7 / 8) (9 / 5) = 23 / 25 := by norm_num [adjacentRatio]
  have hS : nativeS (7 / 8) = 73 / 100 := by norm_num [nativeS]
  have hA : nativeA (7 / 8) = 126 / 1000 := by norm_num [nativeA, middleA]
  unfold pureNativeBandDD pureNativeG1 pureNativeG2
  rw [hR, hS, hA, show 1 + (7 / 8 : ℝ) = 15 / 8 by norm_num]
  change 49 / 500 < (23 / 25) *
      (x * (2 * (73 / 100) * l + ((9 / 5) * (73 / 100) - 1) * l ^ 2) +
        y * ((1 + (9 / 5) * (126 / 1000)) * t ^ 2 - 2 * (126 / 1000) * t)) -
      (3 / 10) * (x * (73 / 100 + ((9 / 5) * (73 / 100) - 1) * l) -
        y * ((1 + (9 / 5) * (126 / 1000)) * t - 126 / 1000))
  nlinarith only [hG1, hG2]

theorem pureNativeBandDD_upper_gt {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hu : 3 / 4 ≤ u) (hu' : u ≤ 7 / 8) :
    49 / 500 < pureNativeBandDD u p := by
  have hU : (7 / 8 : ℝ) ∈ Icc (3 / 4) (7 / 8) := by constructor <;> norm_num
  have hP' : (9 / 5 : ℝ) ∈ Icc 1 (9 / 5) := by constructor <;> norm_num
  have h₁ := pureNativeBandDD_upper_spatial_antitone ⟨hu, hu'⟩ hU hu'
  have h₂ := pureNativeBandDD_exponent_antitone hu hu' ⟨hp, hP⟩ hP' hP
  exact nativeAtU.trans_le (h₁.trans h₂)

end ACS12.GammaMeasure
