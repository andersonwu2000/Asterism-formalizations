import ACS12.JointFrequencyGuards

/-! Whole-ray curvature upper of the complete Bose head factor. -/
namespace ACS12.BoseShape

open CenteredCircle.AllN Polynomial Set

private noncomputable def boseCurvatureGuard (n : ℕ) (x : ℝ) : ℝ :=
  expQuad 3 0 0 (3 ^ n) x + expQuad 2 0 (-(6 * 2 ^ n)) (2 ^ n * (9 - 3 * n)) x +
    expQuad 1 0 (-6) (-9 - 6 * n) x - if n = 0 then 1 else 0

private theorem boseCurvatureGuard_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (boseCurvatureGuard n) (boseCurvatureGuard (n + 1) x) x := by
  unfold boseCurvatureGuard
  convert (((expQuad_deriv 3 0 0 (3 ^ n) x).add
    (expQuad_deriv 2 0 (-(6 * 2 ^ n)) (2 ^ n * (9 - 3 * n)) x)).add
    (expQuad_deriv 1 0 (-6) (-9 - 6 * n) x)).sub_const (if n = 0 then 1 else 0) using 1
  simp only [expQuad,Nat.succ_ne_zero,if_false,sub_zero,Nat.cast_add,Nat.cast_one,pow_succ]
  ring

private theorem boseCurvatureGuard_pos {x : ℝ} (hx : 0 < x) :
    0 < boseCurvatureGuard 0 x := by
  have h0 (n : ℕ) (hn : n < 5) : boseCurvatureGuard n 0 = (derivative^[n] (0 : ℝ[X])).eval 0 := by
    interval_cases n <;> norm_num [boseCurvatureGuard,expQuad,Function.iterate_succ_apply']
  have h5 (x : ℝ) (hx : 0 < x) : (derivative^[5] (0 : ℝ[X])).eval x < boseCurvatureGuard 5 x := by
    have hE := Real.add_one_le_exp x
    have hE' : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le)
    have hA := mul_le_mul_of_nonneg_left hE' (show 0 ≤ 39 + 6 * x by positivity)
    have hP : 0 < 243 * Real.exp x - 192 * (1 + x) - (39 + 6 * x) * Real.exp (-x) := by
      nlinarith only [hE,hA,hx]
    have hPos := mul_pos (Real.exp_pos (2 * x)) hP
    norm_num [boseCurvatureGuard,expQuad,Function.iterate_succ_apply']
    rw [mul_sub,mul_sub,mul_left_comm (Real.exp (2 * x)) 243,← Real.exp_add,
      show 2 * x + x = 3 * x by ring,
      mul_left_comm (Real.exp (2 * x)) (39 + 6 * x),← Real.exp_add,
      show 2 * x + -x = x by ring] at hPos
    nlinarith only [hPos]
  have h := GammaMeasure.expGuard_remainder h0 boseCurvatureGuard_deriv h5 hx
  simpa only [eval_zero] using h

theorem neg_C₁_lt_sixth {x : ℝ} (hx : 0 < x) : -C₁ x < 1 / 6 := by
  have h := boseCurvatureGuard_pos hx
  have hD := expTail_den_pos hx
  rw [neg_C₁_eq hx,Real.exp_neg]
  have hD' := expHead_den_pos hx
  rw [Real.exp_neg] at hD'
  apply (div_lt_iff₀ (pow_pos hD' _)).mpr
  have hEq : ((1 / 6) * (1 - (Real.exp x)⁻¹) ^ 3 -
      (Real.exp x)⁻¹ * ((x - 2) + (x + 2) * (Real.exp x)⁻¹)) * (6 * Real.exp x ^ 3) =
      boseCurvatureGuard 0 x := by
    norm_num [boseCurvatureGuard,expQuad]
    rw [show 3 * x = x + x + x by ring, show 2 * x = x + x by ring,
      Real.exp_add,Real.exp_add]
    field_simp [Real.exp_ne_zero x]
    ring
  have hPos : 0 < (1 / 6) * (1 - (Real.exp x)⁻¹) ^ 3 -
      (Real.exp x)⁻¹ * ((x - 2) + (x + 2) * (Real.exp x)⁻¹) :=
    pos_of_mul_pos_left (hEq.symm ▸ h) (by positivity)
  linarith only [hPos]

end ACS12.BoseShape
