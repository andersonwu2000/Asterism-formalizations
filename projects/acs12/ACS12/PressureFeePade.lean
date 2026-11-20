import ACS12.JointFrequencyGuards

/-! The whole-axis Bose lower and the positive-part fee envelope. -/
namespace ACS12.Pressure

open Set Polynomial CenteredCircle.AllN
open GammaMeasure (expGuard_remainder)

private noncomputable def feeQ : ℝ[X] := C 120 + C 60 * X + C 12 * X ^ 2 + X ^ 3

private noncomputable def feeP (n : ℕ) (s : ℝ) : ℝ :=
  -s ^ 3 + (12 - 3 * (n : ℝ)) * s ^ 2 +
    (-60 + 24 * (n : ℝ) - 3 * (n : ℝ) * ((n : ℝ) - 1)) * s +
    (120 - 60 * (n : ℝ) + 12 * (n : ℝ) * ((n : ℝ) - 1) -
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2))

private noncomputable def feeGuard (n : ℕ) (s : ℝ) : ℝ :=
  (derivative^[n] feeQ).eval s - Real.exp s * feeP n s

private theorem feeGuard_deriv (n : ℕ) (s : ℝ) : HasDerivAt (feeGuard n) (feeGuard (n + 1) s) s := by
  have h := hasDerivAt_id s
  have hD := (((h.pow 3).neg.add ((h.pow 2).const_mul (12 - 3 * (n : ℝ)))).add
    (h.const_mul (-60 + 24 * (n : ℝ) - 3 * (n : ℝ) * ((n : ℝ) - 1)))).add_const
    (120 - 60 * (n : ℝ) + 12 * (n : ℝ) * ((n : ℝ) - 1) -
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2))
  unfold feeGuard
  rw [Function.iterate_succ_apply']
  convert ((derivative^[n] feeQ).hasDerivAt s).sub ((Real.hasDerivAt_exp s).mul hD) using 1
  simp only [feeP,Pi.add_apply,Pi.neg_apply,Pi.pow_apply,id_eq,mul_one,Nat.cast_add,Nat.cast_one]
  ring

theorem bose_lower_pade {s : ℝ} (hs : 0 < s) :
    1 / s - 1 / 2 + 5 * s / (60 + s ^ 2) < 1 / (Real.exp s - 1) := by
  have h0 (n : ℕ) (hn : n < 7) : feeGuard n 0 = (derivative^[n] (0 : ℝ[X])).eval 0 := by
    interval_cases n <;> norm_num [feeGuard,feeP,feeQ,Function.iterate_succ_apply']
  have h7 (x : ℝ) (hx : 0 < x) : (derivative^[7] (0 : ℝ[X])).eval x < feeGuard 7 x := by
    have h : feeGuard 7 x = Real.exp x * (6 + 18 * x + 9 * x ^ 2 + x ^ 3) := by
      norm_num [feeGuard,feeP,feeQ,Function.iterate_succ_apply']
      ring
    rw [h]
    norm_num [Function.iterate_succ_apply']
    positivity
  have h := expGuard_remainder h0 feeGuard_deriv h7 hs
  have hG : 0 < 120 + 60 * s + 12 * s ^ 2 + s ^ 3 -
      (120 - 60 * s + 12 * s ^ 2 - s ^ 3) * Real.exp s := by
    norm_num [feeGuard,feeQ,feeP] at h
    nlinarith only [h]
  apply (lt_div_iff₀ (expTail_den_pos hs)).mpr
  apply (mul_lt_mul_iff_left₀ (show 0 < 2 * s * (60 + s ^ 2) by positivity)).mp
  have hD : 0 < 60 + s ^ 2 := by positivity
  field_simp [hs.ne',hD.ne']
  nlinarith only [hG]

theorem bose_slope_le_inv_sq {s : ℝ} (hs : 0 < s) :
    Real.exp s / (Real.exp s - 1) ^ 2 ≤ 1 / s ^ 2 := by
  have hS := Real.self_lt_sinh_iff.mpr (half_pos hs)
  rw [Real.sinh_eq] at hS
  have hE : Real.exp (s / 2) * (Real.exp (s / 2) - Real.exp (-(s / 2))) = Real.exp s - 1 := by
    rw [mul_sub,← Real.exp_add,← Real.exp_add,show s / 2 + s / 2 = s by ring,add_neg_cancel,Real.exp_zero]
  have hP := mul_lt_mul_of_pos_left (show s < Real.exp (s / 2) - Real.exp (-(s / 2)) by linarith only [hS])
    (Real.exp_pos (s / 2))
  rw [hE] at hP
  have hSq := pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp (s / 2) * s) hP.le 2
  rw [mul_pow,← Real.exp_nat_mul] at hSq
  norm_num at hSq
  rw [show (2 : ℝ) * (s / 2) = s by ring] at hSq
  apply (div_le_div_iff₀ (sq_pos_of_pos (expTail_den_pos hs)) (sq_pos_of_pos hs)).mpr
  simpa only [one_mul] using hSq

end ACS12.Pressure
