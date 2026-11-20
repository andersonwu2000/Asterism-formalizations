import ACS12.HighRationalPowerPeak
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Exact angular maximum for every original nonincident crossing edge. -/
namespace ACS12.HighCurrent

open Set
set_option backward.isDefEq.respectTransparency false

theorem crossing_angular_peak {p θ : ℝ} (hp : 3 ≤ p)
    (hθ : 0 ≤ θ) (hθHalf : θ ≤ Real.pi / 2) :
    Real.cos θ / Real.cos (θ / 2) ^ (p + 1) ≤
      (2 / (p - 1)) * (2 * (p - 1) / (p + 1)) ^ ((p + 1) / 2) := by
  let h := (p + 1) / 2
  let r := Real.cos θ
  let c := 1 / (h - 1)
  have hpM : 0 < p - 1 := by linarith only [hp]
  have hpP : 0 < p + 1 := by linarith only [hp]
  have hh : 1 < h := by unfold h; linarith only [hp]
  have hr : 0 ≤ r := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith only [hθ,Real.pi_pos],hθHalf⟩
  have hc : 0 < c := one_div_pos.mpr (sub_pos.mpr hh)
  have hCos : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo
    (by constructor <;> linarith only [hθ,hθHalf,Real.pi_pos])
  have hOneR : 0 < 1 + r := by linarith only [hr]
  have hOneC : 0 < 1 + c := by linarith only [hc]
  have hSq : Real.cos (θ / 2) ^ 2 = (1 + r) / 2 := by
    have hTrig := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hTrig
    unfold r
    linarith only [hTrig]
  have hPower : Real.cos (θ / 2) ^ (p + 1) = ((1 + r) / 2) ^ h := by
    calc
      _ = Real.cos (θ / 2) ^ (((2 : ℕ) : ℝ) * h) := by
        congr 1
        unfold h
        push_cast
        ring
      _ = (Real.cos (θ / 2) ^ (2 : ℕ)) ^ h := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hCos.le]
      _ = _ := by rw [hSq]
  have hPeak := mul_le_mul_of_nonneg_left (rationalPower_global_peak hh hr)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) h).le
  have hLeft : Real.cos θ / Real.cos (θ / 2) ^ (p + 1) =
      (2 : ℝ) ^ h * (r / (1 + r) ^ h) := by
    rw [hPower,Real.div_rpow hOneR.le (by norm_num : (0 : ℝ) ≤ 2)]
    change r / ((1 + r) ^ h / (2 : ℝ) ^ h) = _
    field_simp [(Real.rpow_pos_of_pos hOneR h).ne',(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) h).ne']
  have hC : c = 2 / (p - 1) := by
    unfold c
    apply (div_eq_div_iff (sub_pos.mpr hh).ne' hpM.ne').mpr
    unfold h
    ring
  have hRatio : 2 / (1 + c) = 2 * (p - 1) / (p + 1) := by
    rw [hC]
    field_simp [hpM.ne',hpP.ne']
    <;> ring
  have hRight : (2 : ℝ) ^ h * (c / (1 + c) ^ h) =
      (2 / (p - 1)) * (2 * (p - 1) / (p + 1)) ^ h := by
    rw [← hRatio,Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hOneC.le]
    rw [← hC]
    ring
  rw [← hLeft,hRight] at hPeak
  exact hPeak

end ACS12.HighCurrent
