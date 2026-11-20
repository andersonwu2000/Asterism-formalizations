import ACS12.MaximumFeeStein

/-! The maximum-ray fee transferred from the reference law to the actual source. -/
namespace ACS12.GammaMeasure

theorem maximumActualFee_lt_line {p L : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4) (hL : 2 < L) :
    maximumActualFee p L < (11 - p) / 10 := by
  have hθ : 0 ≤ (p - 2) / 2 := div_nonneg (sub_nonneg.mpr hp) (by norm_num)
  have hθ₁ : (p - 2) / 2 ≤ 1 := by linarith only [hP]
  have h := (maximumActualFee_le_reference hp hP hL).trans_lt (maximumRefFee_lt_line hθ hθ₁)
  linarith only [h]

end ACS12.GammaMeasure
