import ACS12.QuarticBarycenterPrices

/-! Only the actual barycenter and its curved hump are needed for the one-fifth contradiction. -/
namespace ACS12.HighCurrent

theorem quarticRatio_hump_scalar {x β D H : ℝ} (hx : 0 ≤ x) (hβ : x < β)
    (hId : D * (β + x) = H)
    (hD : D ≤ (3 * β - x) ^ 2 / (4 * β) +
      2 * Real.sqrt (3 * β) - 3 * Real.sqrt x + x * Real.sqrt x / (3 * β)) :
    H ≤ 3 * β ^ 2 + 4 * β * Real.sqrt β := by
  have hβ₀ : 0 < β := hx.trans_lt hβ
  have hAdd : 0 ≤ β + x := by positivity
  have hP : 0 ≤ 3 * β - x := by linarith only [hβ₀, hβ]
  have hPeak : (β + x) * ((3 * β - x) ^ 2 / (4 * β)) ≤ 3 * β ^ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 4 * β)]
    have h₁ : (β + x) * (3 * β - x) ≤ 4 * β ^ 2 := by nlinarith only [sq_nonneg (β - x)]
    have h₂ := mul_le_mul_of_nonneg_right h₁ hP
    have h₃ := mul_le_mul_of_nonneg_left (show 3 * β - x ≤ 3 * β by linarith only [hx])
      (show 0 ≤ 4 * β ^ 2 by positivity)
    linarith only [h₂, h₃]
  have hU : x * Real.sqrt x / (3 * β) ≤ Real.sqrt x / 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * β)).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hβ.le) (Real.sqrt_nonneg x)]
  have hB : Real.sqrt (3 * β) = Real.sqrt 3 * Real.sqrt β := Real.sqrt_mul (by norm_num) _
  have hS : Real.sqrt 3 ≤ 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hAM : 2 * Real.sqrt β * Real.sqrt x ≤ β + x := by
    nlinarith only [sq_nonneg (Real.sqrt β - Real.sqrt x), Real.sq_sqrt hx, Real.sq_sqrt hβ₀.le]
  have hLoss : 2 * x * Real.sqrt (3 * β) ≤ (β + x) * ((8 / 3) * Real.sqrt x) := by
    have h₁ := mul_le_mul_of_nonneg_right hAM (show 0 ≤ (8 / 3) * Real.sqrt x by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hS (show 0 ≤ 2 * x * Real.sqrt β by positivity)
    have h₃ : 0 ≤ x * Real.sqrt β := by positivity
    rw [hB]
    nlinarith only [h₁, h₂, h₃, congrArg ((16 / 3) * Real.sqrt β * ·) (Real.sq_sqrt hx)]
  have hGain := mul_le_mul_of_nonneg_right hS (show 0 ≤ 2 * β * Real.sqrt β by positivity)
  have hTail : (β + x) * (2 * Real.sqrt (3 * β) - 3 * Real.sqrt x + x * Real.sqrt x / (3 * β)) ≤
      4 * β * Real.sqrt β := by
    have h₁ := mul_le_mul_of_nonneg_left hU hAdd
    rw [hB] at hLoss
    rw [hB]
    linarith only [h₁, hLoss, hGain]
  have h := mul_le_mul_of_nonneg_left hD hAdd
  rw [mul_comm (β + x) D, hId] at h
  linarith only [h, hPeak, hTail]

theorem quarticRatio_contradiction {x β D H J : ℝ}
    (hx : 0 ≤ x) (hβ : x < β) (hH : 56 / 81 ≤ H) (hId : D * (β + x) = H)
    (hBounds : D * β ^ 2 / Real.sqrt (β - x) ≤ J) (hJ : J < 629 / 2000)
    (hD : D ≤ (3 * β - x) ^ 2 / (4 * β) +
      2 * Real.sqrt (3 * β) - 3 * Real.sqrt x + x * Real.sqrt x / (3 * β)) : False := by
  have hβcap := quarticBarycenter_ratio_mean hx hβ hH hId hBounds hJ
  have hβ₀ := hx.trans_lt hβ
  have hUpper := quarticRatio_hump_scalar hx hβ hId hD
  have hSq := pow_lt_pow_left₀ hβcap hβ₀.le (by decide : (2 : ℕ) ≠ 0)
  have hSqrt : Real.sqrt β < 1 / 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact Real.sqrt_lt_sqrt hβ₀.le (by norm_num; exact hβcap)
  have hTail : β * Real.sqrt β ≤ (1 / 4 : ℝ) * (1 / 2) :=
    mul_le_mul hβcap.le hSqrt.le (Real.sqrt_nonneg β) (by norm_num)
  nlinarith only [hH, hUpper, hSq, hTail]

end ACS12.HighCurrent
