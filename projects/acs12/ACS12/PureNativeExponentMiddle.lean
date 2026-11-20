import ACS12.PureNativeExponentGeometry

/-! The native curvature on the whole middle gap interval. -/

namespace ACS12.GammaMeasure

open Set

theorem pureNativeBandDD_middle_gt {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hu : 1 / 2 ≤ u) (hu' : u ≤ 3 / 4) :
    1 / 8 < pureNativeBandDD u p := by
  let s := nativeS u
  let l := nativeL u
  let q := adjacentRatio u p * l
  let Y := p * s - 1
  let f := s * (2 * q - 3 / 10) + Y * l * (q - 3 / 10)
  have hu₀ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hu
  have hu₁ := hu'.trans (by norm_num : (3 / 4 : ℝ) ≤ 1)
  have hs₀ : 64 / 100 ≤ s := by dsimp only [s, nativeS]; linarith only [hu]
  have hs₁ : s ≤ 7 / 10 := by dsimp only [s, nativeS]; linarith only [hu']
  have hs : 0 ≤ s := (by norm_num : (0 : ℝ) ≤ 64 / 100).trans hs₀
  have hl₀ : 0 ≤ l := nativeL_nonneg hu₀ hu₁
  have hl : l ≤ 694 / 1000 :=
    ((nativeL_mono_rev (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num) hu₀ hu).trans_lt nativeL_half_bounds.2).le
  have hq : 248 / 1000 < q := nativeCapLog_middle_lower hP hu₀ hu'
  have hY₀ : -1 ≤ Y := by dsimp only [Y]; linarith only [mul_nonneg (zero_le_one.trans hp) hs]
  have hY₁ : Y ≤ 26 / 100 := by
    have h := mul_le_mul hP hs₁ hs (by norm_num : (0 : ℝ) ≤ 9 / 5)
    dsimp only [Y]
    linarith only [h]
  have hF : 116 / 1000 < f := by
    rcases le_total (3 / 10) q with h | h
    · have hL := mul_le_mul_of_nonneg_right hY₀ hl₀
      have hB : 0 ≤ 2 * s + Y * l := by nlinarith only [hL, hs₀, hl]
      have hF := mul_nonneg (sub_nonneg.mpr h) hB
      dsimp only [f]
      nlinarith only [hF, hs₀]
    · have hB := mul_le_mul_of_nonneg_left (show 2 * (248 / 1000 : ℝ) - 3 / 10 ≤ 2 * q - 3 / 10 by linarith only [hq]) hs
      have hC := mul_le_mul_of_nonneg_right hs₀ (show (0 : ℝ) ≤ 2 * (248 / 1000) - 3 / 10 by norm_num)
      have hD : Y * l ≤ (26 / 100) * (694 / 1000) :=
        mul_le_mul hY₁ hl hl₀ (by norm_num)
      have hE := mul_le_mul_of_nonpos_right hD (sub_nonpos.mpr h)
      dsimp only [f]
      nlinarith only [hB, hC, hE, hq]
  have hU : 4 / 3 ≤ u ^ (-p) := by
    have h₁ : u ^ (-1 : ℝ) ≤ u ^ (-p) :=
      Real.rpow_le_rpow_of_exponent_ge hu₀ hu₁ (neg_le_neg hp)
    rw [Real.rpow_neg_one, ← one_div] at h₁
    exact (by
      have h := one_div_le_one_div_of_le hu₀ hu'
      norm_num at h
      simpa only [one_div] using h : 4 / 3 ≤ 1 / u).trans h₁
  have hG := pureNativeBandDD_unshifted_le hp hP hu₀ hu₁
  change u ^ (-p) * f ≤ _ at hG
  have hB := mul_le_mul hU hF.le (by norm_num : (0 : ℝ) ≤ 116 / 1000) (Real.rpow_nonneg hu₀.le (-p))
  linarith only [hG, hB]

end ACS12.GammaMeasure
