import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Global tangent support of a negative real power, with no endpoint differentiation. -/
namespace ACS12

theorem negativePower_support {q x y : ℝ} (hq : q ≤ 0) (hx : 0 < x) (hy : 0 < y) :
    y^q+q*y^(q-1)*(x-y) ≤ x^q := by
  have hR := div_pos hx hy
  have hL := Real.log_le_sub_one_of_pos hR
  have hPay := mul_le_mul_of_nonpos_left hL hq
  have hE := Real.add_one_le_exp (q*Real.log (x/y))
  have hQ : 1+q*(x/y-1) ≤ (x/y)^q := by
    rw [Real.rpow_def_of_pos hR,mul_comm (Real.log (x/y)) q]
    linarith only [hPay,hE]
  have hMul := mul_le_mul_of_nonneg_left hQ (Real.rpow_pos_of_pos hy q).le
  rw [Real.div_rpow hx.le hy.le] at hMul
  have hY : y^(q-1) = y^q/y := by rw [Real.rpow_sub hy,Real.rpow_one]
  have hId : y^q*(1+q*(x/y-1)) = y^q+q*y^(q-1)*(x-y) := by
    rw [hY]
    field_simp [hy.ne']
    <;> ring
  rw [hId] at hMul
  simpa only [mul_div_cancel₀ _ (Real.rpow_pos_of_pos hy q).ne'] using hMul

end ACS12
