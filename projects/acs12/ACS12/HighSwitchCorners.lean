import ACS12.HighMinimumPrice
import ACS12.HighUnitAffine

/-! Exact whole-rectangle corner payments for the high pressure switch. -/
namespace ACS12.Pressure

open Set

noncomputable def highPressureEnvelope (p R : ℝ) : ℝ :=
  (R / 2) * max 1 (highMinimumUnitPrice p (Real.sqrt (R / (7 * p))))

noncomputable def highPressureSwitch (p : ℝ) : ℝ :=
  (10264 - 919 * p) / 3840

private theorem highPressureEnvelope_corner_lt (k : ℕ) (hk : 0 < k) {R l u T : ℝ}
    (hR : 0 < R) (hl : 0 ≤ l) (hu : 0 < u)
    (hLow : l ^ 2 < R / (7 * k)) (hHigh : R / (7 * k) < u ^ 2)
    (hClip : R / 2 < T)
    (hPay : R / 2 * (((k : ℝ) + 5 / 12) * u + 1 / (2 + l / 2) ^ k) ≤ T) :
    highPressureEnvelope k R < T := by
  let y := Real.sqrt (R / (7 * k))
  have hk₀ : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hq : 0 < R / (7 * k) := div_pos hR (by positivity)
  have hy₀ : 0 ≤ y := Real.sqrt_nonneg _
  have hy₂ : y ^ 2 = R / (7 * k) := Real.sq_sqrt hq.le
  have hyl : l < y := by nlinarith only [hLow,hy₂,hy₀,hl]
  have hyu : y < u := by nlinarith only [hHigh,hy₂,hy₀,hu]
  have hBase : 0 < 2 + l / 2 := by positivity
  have hBaseY : 0 < 2 + y / 2 := by positivity
  have hPow := pow_lt_pow_left₀ (show 2 + l / 2 < 2 + y / 2 by linarith only [hyl]) hBase.le hk.ne'
  have hTail : 1 / (2 + y / 2) ^ k < 1 / (2 + l / 2) ^ k :=
    one_div_lt_one_div_of_lt (pow_pos hBase k) hPow
  have hLinear := mul_lt_mul_of_pos_left hyu (show 0 < (k : ℝ) + 5 / 12 by positivity)
  have hB : highMinimumUnitPrice k y <
      ((k : ℝ) + 5 / 12) * u + 1 / (2 + l / 2) ^ k := by
    unfold highMinimumUnitPrice
    rw [Real.rpow_neg hBaseY.le,Real.rpow_natCast,← one_div]
    linarith only [hTail,hLinear]
  have hB' := mul_lt_mul_of_pos_left hB (show 0 < R / 2 by positivity)
  unfold highPressureEnvelope
  change R / 2 * max 1 (highMinimumUnitPrice k y) < T
  rw [mul_max_of_nonneg _ _ (show 0 ≤ R / 2 by positivity),mul_one,max_lt_iff]
  exact ⟨hClip,hB'.trans_le hPay⟩

theorem highSwitch_corner_two_two :
    highPressureEnvelope 2 (4213 / 1920) < highUnitAffine 2 - 1 / 80 := by
  apply highPressureEnvelope_corner_lt 2 (by decide) (l := 39 / 100) (u := 99 / 250)
  all_goals norm_num [highUnitAffine]

theorem highSwitch_corner_four_four :
    highPressureEnvelope 4 (549 / 320) < highUnitAffine 4 - 1 / 80 := by
  apply highPressureEnvelope_corner_lt 4 (by decide) (l := 0) (u := 1 / 4)
  all_goals norm_num [highUnitAffine]

theorem highSwitch_corner_two_four :
    highPressureEnvelope 2 (549 / 320) < 11 / 12 := by
  apply highPressureEnvelope_corner_lt 2 (by decide) (l := 1 / 3) (u := 19 / 54)
  all_goals norm_num

theorem highSwitch_corner_four_two :
    highPressureEnvelope 4 (4213 / 1920) < 17 / 12 := by
  apply highPressureEnvelope_corner_lt 4 (by decide) (l := 1 / 4) (u := 7 / 25)
  all_goals norm_num

theorem highSwitch_boundary_two :
    highPressureEnvelope 2 (33 / 10) < (33 / 10) - (11 - 2) / 10 := by
  apply highPressureEnvelope_corner_lt 2 (by decide) (l := 2 / 5) (u := 1 / 2)
  all_goals norm_num

theorem highSwitch_boundary_four :
    highPressureEnvelope 4 (33 / 10) < (33 / 10) - (11 - 4) / 10 := by
  apply highPressureEnvelope_corner_lt 4 (by decide) (l := 1 / 3) (u := 11 / 32)
  all_goals norm_num

end ACS12.Pressure
