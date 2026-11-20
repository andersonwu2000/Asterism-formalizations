import ACS12.JointBoseCurvature

/-! Monotonicity and the quadratic scaling limit of the whole Bose curvature. -/
namespace ACS12.BoseShape

open Set Polynomial CenteredCircle.AllN

noncomputable def curvatureHeat (x : ℝ) : ℝ := Real.exp x * (-C₁ x)

theorem curvatureHeat_pos {x : ℝ} (hx : 0 < x) : 0 < curvatureHeat x :=
  mul_pos (Real.exp_pos _) (neg_pos.mpr (C₁_neg hx))

private noncomputable def heatSlope (x : ℝ) : ℝ :=
  (1 + (4 - 4 * x) * Real.exp (-x) - (2 * x + 5) * (Real.exp (-x)) ^ 2) /
    (1 - Real.exp (-x)) ^ 4

private theorem heatFormula {x : ℝ} (hx : 0 < x) :
    curvatureHeat x = (x - 2 + (x + 2) * Real.exp (-x)) / (1 - Real.exp (-x)) ^ 3 := by
  rw [curvatureHeat,neg_C₁_eq hx]
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  rw [mul_div_assoc,← mul_assoc,he,one_mul]

private theorem heat_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt curvatureHeat (heatSlope x) x := by
  have h := hasDerivAt_id x
  have hE := h.neg.exp
  have hA := (h.sub_const 2).add ((h.add_const 2).mul hE)
  have hB := (hE.const_sub 1).pow 3
  have hD := hA.div hB (pow_ne_zero _ (expHead_den_pos hx).ne')
  have hI : HasDerivAt (fun q => (q - 2 + (q + 2) * Real.exp (-q)) / (1 - Real.exp (-q)) ^ 3)
      (heatSlope x) x := by
    convert hD using 1
    unfold heatSlope
    simp only [id_eq,Pi.add_apply,Pi.neg_apply,Pi.mul_apply,Pi.pow_apply,one_mul,Nat.reduceSub]
    field_simp [(expHead_den_pos hx).ne']
    ring
  apply hI.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with q hq
  exact heatFormula hq

private noncomputable def heatIncreaseJet (n : ℕ) (x : ℝ) : ℝ :=
  expQuad 2 0 0 (2 ^ n) x + expQuad 1 0 (-4) (4 - 4 * n) x +
    (derivative^[n] ((-2 : ℝ[X]) * X - 5)).eval x

private theorem heatIncreaseJet_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (heatIncreaseJet n) (heatIncreaseJet (n + 1) x) x := by
  unfold heatIncreaseJet
  convert (((expQuad_deriv 2 0 0 (2 ^ n) x).add (expQuad_deriv 1 0 (-4) (4 - 4 * n) x)).add
    ((derivative^[n] ((-2 : ℝ[X]) * X - 5)).hasDerivAt x)) using 1
  simp only [expQuad,Function.iterate_succ_apply',Nat.cast_add,Nat.cast_one,pow_succ]
  ring

private theorem heatIncrease_pos {x : ℝ} (hx : 0 < x) : 0 < heatIncreaseJet 0 x := by
  have h0 (n : ℕ) (hn : n < 4) : heatIncreaseJet n 0 = (derivative^[n] (0 : ℝ[X])).eval 0 := by
    interval_cases n <;> norm_num [heatIncreaseJet,expQuad,Function.iterate_succ_apply']
  have h4 (x : ℝ) (hx : 0 < x) : (derivative^[4] (0 : ℝ[X])).eval x < heatIncreaseJet 4 x := by
    have h : 0 < 16 * Real.exp x - 4 * x - 12 := by linarith only [Real.add_one_le_exp x,hx]
    have h' := mul_pos (Real.exp_pos x) h
    norm_num [heatIncreaseJet,expQuad,Function.iterate_succ_apply',two_mul,Real.exp_add]
    nlinarith only [h']
  simpa only [eval_zero] using GammaMeasure.expGuard_remainder h0 heatIncreaseJet_deriv h4 hx

private noncomputable def heatScaleJet (n : ℕ) (x : ℝ) : ℝ :=
  expQuad 2 0 (2 ^ n) (2 ^ n * ((n : ℝ) / 2 - 4)) x +
    expQuad 1 4 (8 * n - 4) (4 * (n : ℝ) ^ 2 - 8 * n + 8) x +
    (derivative^[n] ((2 : ℝ[X]) * X ^ 2 + 3 * X - 4)).eval x

private theorem heatScaleJet_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (heatScaleJet n) (heatScaleJet (n + 1) x) x := by
  unfold heatScaleJet
  convert (((expQuad_deriv 2 0 (2 ^ n) (2 ^ n * ((n : ℝ) / 2 - 4)) x).add
    (expQuad_deriv 1 4 (8 * n - 4) (4 * (n : ℝ) ^ 2 - 8 * n + 8) x)).add
      ((derivative^[n] ((2 : ℝ[X]) * X ^ 2 + 3 * X - 4)).hasDerivAt x)) using 1
  simp only [expQuad,Function.iterate_succ_apply',Nat.cast_add,Nat.cast_one,pow_succ]
  ring

private noncomputable def heatScalePolynomial : ℝ[X] :=
  Polynomial.C (1 / 3 : ℝ) * X ^ 4 + Polynomial.C (1 / 6 : ℝ) * X ^ 5 + Polynomial.C (1 / 18 : ℝ) * X ^ 6 + Polynomial.C (1 / 60 : ℝ) * X ^ 7

private theorem heatScale_pos {x : ℝ} (hx : 0 < x) : 0 < heatScaleJet 0 x := by
  have h0 (n : ℕ) (hn : n < 8) : heatScaleJet n 0 = (derivative^[n] heatScalePolynomial).eval 0 := by
    interval_cases n <;> norm_num [heatScaleJet,heatScalePolynomial,expQuad,Function.iterate_succ_apply']
  have h8 (x : ℝ) (hx : 0 < x) : (derivative^[8] heatScalePolynomial).eval x < heatScaleJet 8 x := by
    norm_num [heatScaleJet,heatScalePolynomial,expQuad,Function.iterate_succ_apply']
    positivity
  have hP : 0 ≤ heatScalePolynomial.eval x := by simp only [heatScalePolynomial,eval_add,eval_mul,eval_pow,eval_C,eval_X]; positivity
  exact hP.trans_lt (GammaMeasure.expGuard_remainder h0 heatScaleJet_deriv h8 hx)

theorem curvatureHeat_mono : MonotoneOn curvatureHeat (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
  · exact fun x hx => (heat_deriv hx).continuousAt.continuousWithinAt
  · exact fun x hx => (heat_deriv (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx₀ : 0 < x := interior_subset hx
    rw [(heat_deriv hx₀).deriv]
    unfold heatSlope
    apply div_nonneg _ (by positivity : 0 ≤ (1 - Real.exp (-x)) ^ (4 : ℕ))
    have h := heatIncrease_pos hx₀
    have he : Real.exp (2 * x) = Real.exp x ^ 2 := by rw [two_mul,Real.exp_add,pow_two]
    norm_num [heatIncreaseJet,expQuad,he] at h
    have hP : 0 < (1 + (4 - 4 * x) * Real.exp (-x) - (2 * x + 5) * (Real.exp (-x)) ^ 2) *
        Real.exp x ^ 2 := by
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero x]
      nlinarith only [h]
    exact (pos_of_mul_pos_left hP (sq_nonneg (Real.exp x))).le

theorem curvatureHeat_div_sq_anti :
    AntitoneOn (fun x : ℝ => curvatureHeat x / x ^ 2) (Ioi 0) := by
  have hD (x : ℝ) (hx : 0 < x) := (heat_deriv hx).div ((hasDerivAt_id x).pow 2) (pow_ne_zero _ hx.ne')
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
  · exact fun x hx => (hD x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hD x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx₀ : 0 < x := interior_subset hx
    change deriv (curvatureHeat / id ^ (2 : ℕ)) x ≤ 0
    rw [(hD x hx₀).deriv]
    simp only [id_eq,Pi.pow_apply,one_mul,mul_one,Nat.reduceSub,pow_one]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    let X := Real.exp (-x)
    let Y := (x - 4) + (4 * x ^ 2 - 4 * x + 8) * X + (2 * x ^ 2 + 3 * x - 4) * X ^ 2
    have hE : (2 * curvatureHeat x - x * heatSlope x) * (1 - X) ^ 4 = Y := by
      rw [heatFormula hx₀]
      unfold heatSlope Y X
      field_simp [(expHead_den_pos hx₀).ne']
      ring
    have hs := heatScale_pos hx₀
    have he : Real.exp (2 * x) = Real.exp x ^ 2 := by rw [two_mul,Real.exp_add,pow_two]
    norm_num [heatScaleJet,expQuad,he] at hs
    have hP : 0 < Y * Real.exp x ^ 2 := by
      unfold Y X
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero x]
      nlinarith only [hs]
    have hY := pos_of_mul_pos_left hP (sq_nonneg (Real.exp x))
    rw [← hE] at hY
    have h := pos_of_mul_pos_left hY (by positivity : 0 ≤ (1 - X) ^ (4 : ℕ))
    norm_num only [Nat.cast_ofNat]
    nlinarith only [mul_pos hx₀ h]

theorem curvatureHeat_scaled {s r m : ℝ} (hs : 0 < s) (hr : 0 < r) (hrm : r ≤ m) :
    (r / m) ^ 2 * (-C₁ (m * s)) ≤ Real.exp (-s * (m - r)) * (-C₁ (r * s)) := by
  have hm := hr.trans_le hrm
  have hR := mul_pos hr hs
  have hM := mul_pos hm hs
  have h := curvatureHeat_div_sq_anti hR hM (mul_le_mul_of_nonneg_right hrm hs.le)
  have h' := (div_le_div_iff₀ (sq_pos_of_pos hM) (sq_pos_of_pos hR)).mp h
  have hE : Real.exp (-s * (m - r)) = Real.exp (r * s) / Real.exp (m * s) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hE,div_pow,div_mul_eq_mul_div,div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hm) (Real.exp_pos _)).mpr
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos hs)
  unfold curvatureHeat at h'
  nlinarith only [h']

end ACS12.BoseShape
