import ACS12.HighSwitchCorners

/-! The complete exponent reserve paying the linear part of the high envelope. -/
namespace ACS12.Pressure

open Set

noncomputable def highExponentReserve (p : ℝ) : ℝ :=
  p ^ (5 / 2 : ℝ) * (4 / 9 : ℝ) ^ p / (4 * p - 5)

private theorem highExponentReserve_deriv {p : ℝ} (hp : 2 ≤ p) :
    HasDerivAt highExponentReserve
      (highExponentReserve p * (5 / (2 * p) + Real.log (4 / 9) - 4 / (4 * p - 5))) p := by
  have hp₀ : 0 < p := by linarith only [hp]
  have hDen : 0 < 4 * p - 5 := by linarith only [hp]
  have hP := Real.hasDerivAt_rpow_const (p := 5 / 2) (Or.inl hp₀.ne')
  have hE := (hasDerivAt_id p).const_rpow (show (0 : ℝ) < 4 / 9 by norm_num)
  have h := (hP.mul hE).div (((hasDerivAt_id p).const_mul 4).sub_const 5) hDen.ne'
  convert h using 1
  simp only [highExponentReserve,id_eq,mul_one,one_mul,Pi.mul_apply]
  rw [Real.rpow_sub_one hp₀.ne']
  field_simp [hp₀.ne',hDen.ne']
  <;> ring

theorem highExponentReserve_antitone : AntitoneOn highExponentReserve (Icc 2 4) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact fun p hp => (highExponentReserve_deriv hp.1).continuousAt.continuousWithinAt
  · exact fun p hp => (highExponentReserve_deriv (interior_subset hp).1).differentiableAt.differentiableWithinAt
  · intro p hp
    have hp₂ : 2 ≤ p := (interior_subset hp).1
    have hp₀ : 0 < p := by linarith only [hp₂]
    have hDen : 0 < 4 * p - 5 := by linarith only [hp₂]
    have hRat : 5 / (2 * p) - 4 / (4 * p - 5) ≤ (1 / 3 : ℝ) := by
      have hEq : 5 / (2 * p) - 4 / (4 * p - 5) =
          (5 * (4 * p - 5) - 8 * p) / (2 * p * (4 * p - 5)) := by
        field_simp [hp₀.ne',hDen.ne']
        <;> ring_nf
        <;> field_simp [show -5 + p * 4 ≠ 0 by linarith only [hp₂]]
        <;> ring
      rw [hEq]
      apply (div_le_iff₀ (show 0 < 2 * p * (4 * p - 5) by positivity)).mpr
      nlinarith only [sq_nonneg (p - 23 / 8)]
    have hLog : Real.log (4 / 9) ≤ -Real.log 2 := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4 / 9)
        (by norm_num : (4 / 9 : ℝ) ≤ 1 / 2)
      rw [one_div,Real.log_inv] at h
      exact h
    have hBracket : 5 / (2 * p) + Real.log (4 / 9) - 4 / (4 * p - 5) ≤ 0 := by
      linarith only [hRat,hLog,Real.log_two_gt_d9]
    have hPos : 0 ≤ highExponentReserve p := by unfold highExponentReserve; positivity
    rw [(highExponentReserve_deriv hp₂).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos hPos hBracket

theorem highExponentReserve_four : highExponentReserve 4 = 8192 / 72171 := by
  have hPow : (4 : ℝ) ^ (5 / 2 : ℝ) = 32 := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,Real.rpow_add (by norm_num : (0 : ℝ) < 4),
      Real.rpow_two,← Real.sqrt_eq_rpow]
    norm_num
  norm_num [highExponentReserve,hPow,Real.rpow_ofNat]

theorem highExponentReserve_lower {p : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4) :
    (8192 / 72171 : ℝ) ≤ highExponentReserve p := by
  rw [← highExponentReserve_four]
  exact highExponentReserve_antitone ⟨hp,hP⟩ (by norm_num) hP

theorem highExponentReserve_payment {p : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4) :
    (7 / 10) * (4 * p - 5) / (16 * p ^ (5 / 2 : ℝ)) ≤
      (4 / 9 : ℝ) * (4 / 9 : ℝ) ^ p := by
  have hp₀ : 0 < p := by linarith only [hp]
  have hDen : 0 < 4 * p - 5 := by linarith only [hp]
  have hPow : 0 < p ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hp₀ _
  have h := highExponentReserve_lower hp hP
  unfold highExponentReserve at h
  have hH := (le_div_iff₀ hDen).mp h
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) hPow)).mpr
  nlinarith only [hH,hDen]

end ACS12.Pressure
