import ACS12.PressureRowShape
import ACS12.NativeRegularRow

/-! The actual normalized row and the independent full triangle certificate. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN
open GammaMeasure (powerTail powerTail_pos powerTail_B2 powerTail_exponent_antitone)
open NativeCells (analyticRow analyticRow_integer)

noncomputable def pressureNormalizedRow (p N : ℝ) : ℝ :=
  analyticRow p N / (2 * powerTail p 1 * N ^ p / Real.pi ^ p)

theorem pressureNormalizedRow_exp_eq {p v : ℝ} (hp : 1 < p) :
    pressureNormalizedRow p (Real.exp v) =
      (Real.pi ^ p / (2 * powerTail p 1)) * pressureLogCountRow p v := by
  have hP : 0 < powerTail p 1 := powerTail_pos hp (by decide)
  have hPi := Real.rpow_pos_of_pos Real.pi_pos p
  have hExp : 0 < Real.exp v ^ p := Real.rpow_pos_of_pos (Real.exp_pos _) _
  unfold pressureNormalizedRow pressureLogCountRow
  rw [show -p * v = -(v * p) by ring,Real.exp_neg,Real.exp_mul]
  field_simp [hPi.ne',hP.ne',hExp.ne']

theorem pressureNormalizedRow_mono {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) :
    MonotoneOn (pressureNormalizedRow p) (Ioi 1) := by
  intro x hx y hy hxy
  have hx₀ := zero_lt_one.trans (show 1 < x from hx)
  have hy₀ := zero_lt_one.trans (show 1 < y from hy)
  have hLog := (pressureLogCountRow_shape hp hp₂).2.monotoneOn
    (Real.log_pos hx) (Real.log_pos hy) (Real.log_le_log hx₀ hxy)
  have hC : 0 ≤ Real.pi ^ p / (2 * powerTail p 1) := by have := powerTail_pos hp (m := 1) (by decide); positivity
  rw [← Real.exp_log hx₀,← Real.exp_log hy₀,pressureNormalizedRow_exp_eq hp,pressureNormalizedRow_exp_eq hp]
  exact mul_le_mul_of_nonneg_left hLog hC

end ACS12.Pressure
