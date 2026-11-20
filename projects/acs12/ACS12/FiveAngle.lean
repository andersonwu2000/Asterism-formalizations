import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! Exact original five-angle constants shared by the source count and native rank payments. -/
namespace ACS12

theorem sqrt_five_guards : (559 / 250 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
  have hSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hPos := Real.sqrt_nonneg 5
  constructor <;> nlinarith only [hSq,hPos]

theorem five_sin_sq : Real.sin (Real.pi / 5) ^ 2 = (5 - Real.sqrt 5) / 8 := by
  have hTrig := Real.sin_sq_add_cos_sq (Real.pi / 5)
  rw [Real.cos_pi_div_five] at hTrig
  have hSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith only [hTrig,hSq]

theorem five_cot_sq :
    (Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5)) ^ 2 = 1 + (2 / 5) * Real.sqrt 5 := by
  have hSin := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos] : 0 < Real.pi / 5)
    (by linarith [Real.pi_pos] : Real.pi / 5 < Real.pi)
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 hSin.ne')).mpr
  rw [five_sin_sq,Real.cos_pi_div_five]
  nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

theorem five_csc_sq :
    1 / Real.sin (Real.pi / 5) ^ 2 = 2 + (2 / 5) * Real.sqrt 5 := by
  have hSin := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos] : 0 < Real.pi / 5)
    (by linarith [Real.pi_pos] : Real.pi / 5 < Real.pi)
  apply (div_eq_iff (pow_ne_zero 2 hSin.ne')).mpr
  rw [five_sin_sq]
  nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]

theorem five_cot_bounds :
    (172 / 125 : ℝ) < Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5) ∧
      Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5) < 551 / 400 := by
  have hSin := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos] : 0 < Real.pi / 5)
    (by linarith [Real.pi_pos] : Real.pi / 5 < Real.pi)
  have hCos := Real.cos_pos_of_mem_Ioo
    (show Real.pi / 5 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith [Real.pi_pos])
  have hCot := div_pos hCos hSin
  have hLower : (172 / 125 : ℝ) ^ 2 <
      (Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5)) ^ 2 := by
    rw [five_cot_sq]
    linarith only [sqrt_five_guards.1]
  have hUpper : (Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5)) ^ 2 <
      (551 / 400 : ℝ) ^ 2 := by
    rw [five_cot_sq]
    linarith only [sqrt_five_guards.2]
  exact ⟨(sq_lt_sq₀ (by norm_num) hCot.le).mp hLower,(sq_lt_sq₀ hCot.le (by norm_num)).mp hUpper⟩

theorem five_theta_bounds :
    (33 / 40 : ℝ) < (Real.pi / 5) * (Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5)) ∧
      (Real.pi / 5) * (Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5)) < 6061 / 7000 := by
  have hx : 0 < Real.pi / 5 := by positivity
  have hLowPi : (3 / 5 : ℝ) < Real.pi / 5 := by linarith only [Real.pi_gt_three]
  have hLowCot : (11 / 8 : ℝ) < Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5) := by
    linarith only [five_cot_bounds.1]
  have hLow := (mul_lt_mul_of_pos_right hLowPi (by norm_num : (0 : ℝ) < 11 / 8)).trans
    (mul_lt_mul_of_pos_left hLowCot hx)
  have hHighPi : Real.pi / 5 < (22 / 35 : ℝ) := by linarith only [Real.pi_lt_d4]
  have hHigh := (mul_lt_mul_of_pos_left five_cot_bounds.2 hx).trans
    (mul_lt_mul_of_pos_right hHighPi (by norm_num : (0 : ℝ) < 551 / 400))
  constructor <;> linarith only [hLow,hHigh]

theorem five_G_lower :
    (73019 / 125000 : ℝ) <
      2 * (Real.pi / 5) * (Real.cos (Real.pi / 5) / Real.sin (Real.pi / 5)) -
        (Real.pi / 5) ^ 2 / Real.sin (Real.pi / 5) ^ 2 := by
  have hx : 0 < Real.pi / 5 := by positivity
  have hPi : (157 / 50 : ℝ) < Real.pi := by linarith only [Real.pi_gt_d4]
  have hP₂ : Real.pi ^ 2 < (247 / 25 : ℝ) := by
    have h := pow_lt_pow_left₀ Real.pi_lt_d4 Real.pi_pos.le (by decide : (2 : ℕ) ≠ 0)
    linarith only [h]
  have hCsc : 1 / Real.sin (Real.pi / 5) ^ 2 < (579 / 200 : ℝ) := by
    rw [five_csc_sq]
    linarith only [sqrt_five_guards.2]
  have hLpi : (157 / 250 : ℝ) < Real.pi / 5 := by linarith only [hPi]
  have hL := (mul_lt_mul_of_pos_right hLpi (by norm_num : (0 : ℝ) < 172 / 125)).trans
    (mul_lt_mul_of_pos_left five_cot_bounds.1 hx)
  have hUpper : (Real.pi / 5) ^ 2 / Real.sin (Real.pi / 5) ^ 2 < (143013 / 125000 : ℝ) := by
    calc
      _ = (Real.pi ^ 2 / 25) * (1 / Real.sin (Real.pi / 5) ^ 2) := by ring
      _ < (Real.pi ^ 2 / 25) * (579 / 200) :=
        mul_lt_mul_of_pos_left hCsc (by positivity)
      _ < (247 / 625 : ℝ) * (579 / 200) := by
        apply mul_lt_mul_of_pos_right _ (by norm_num : (0 : ℝ) < 579 / 200)
        linarith only [hP₂]
      _ = _ := by norm_num
  linarith only [hL,hUpper]

end ACS12
