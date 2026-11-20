import ACS12.HighEnvelopeRadial

/-! Complete exponent derivatives of the uncut high pressure law. -/
namespace ACS12.Pressure

noncomputable def highExponentScale (c p : ℝ) : ℝ := c * p ^ (-(1 / 2 : ℝ))
noncomputable def highExponentLinear (c p : ℝ) : ℝ := (p + 5 / 12) * highExponentScale c p
noncomputable def highExponentLogTail (c p : ℝ) : ℝ := -p * Real.log (2 + highExponentScale c p / 2)
noncomputable def highExponentTail (c p : ℝ) : ℝ := Real.exp (highExponentLogTail c p)
noncomputable def highExponentLogSlope (c p : ℝ) : ℝ :=
  -Real.log (2 + highExponentScale c p / 2) +
    highExponentScale c p / (2 * (4 + highExponentScale c p))
noncomputable def highExponentLogCurvature (c p : ℝ) : ℝ :=
  highExponentScale c p * (2 + highExponentScale c p) /
    (2 * p * (4 + highExponentScale c p) ^ 2)

theorem highExponentScale_deriv {c p : ℝ} (hp : 0 < p) :
    HasDerivAt (highExponentScale c) (-highExponentScale c p / (2 * p)) p := by
  convert (Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hp.ne')).const_mul c using 1
  rw [Real.rpow_sub_one hp.ne']
  unfold highExponentScale
  ring

theorem highExponentLinear_deriv {c p : ℝ} (hp : 0 < p) :
    HasDerivAt (highExponentLinear c)
      (highExponentScale c p * (1 / 2 - 5 / (24 * p))) p := by
  convert ((hasDerivAt_id p).add_const (5 / 12 : ℝ)).mul (highExponentScale_deriv hp) using 1
  simp only [id_eq,one_mul]
  field_simp [hp.ne']
  <;> ring

theorem highExponentLinear_second {c p : ℝ} (hp : 0 < p) :
    HasDerivAt (fun x => highExponentScale c x * (1 / 2 - 5 / (24 * x)))
      (highExponentScale c p * (5 - 4 * p) / (16 * p ^ 2)) p := by
  have hFrac := (hasDerivAt_const p (5 : ℝ)).div ((hasDerivAt_id p).const_mul 24)
    (show (24 : ℝ) * p ≠ 0 by positivity)
  convert (highExponentScale_deriv (c := c) hp).mul (hFrac.const_sub (1 / 2 : ℝ)) using 1
  simp only [id_eq,zero_mul,zero_sub,Pi.div_apply,Pi.mul_apply,Pi.neg_apply,Pi.sub_apply]
  field_simp [hp.ne']
  <;> ring

theorem highExponentLogTail_deriv {c p : ℝ} (hc : 0 ≤ c) (hp : 0 < p) :
    HasDerivAt (highExponentLogTail c) (highExponentLogSlope c p) p := by
  have hy : 0 ≤ highExponentScale c p := by unfold highExponentScale; positivity
  have hBase : 0 < 2 + highExponentScale c p / 2 := by positivity
  have hLog := (((highExponentScale_deriv (c := c) hp).div_const 2).const_add 2).log hBase.ne'
  convert (hasDerivAt_id p).neg.mul hLog using 1
  simp only [id_eq,Pi.neg_apply,highExponentLogSlope]
  field_simp [hp.ne',hBase.ne',show 4 + highExponentScale c p ≠ 0 by positivity]
  <;> ring

theorem highExponentLogSlope_deriv {c p : ℝ} (hc : 0 ≤ c) (hp : 0 < p) :
    HasDerivAt (highExponentLogSlope c) (highExponentLogCurvature c p) p := by
  let y := highExponentScale c p
  have hy : 0 ≤ y := by unfold y highExponentScale; positivity
  have hBase : 0 < 2 + y / 2 := by positivity
  have hDen : 0 < 4 + y := by positivity
  have hY := highExponentScale_deriv (c := c) hp
  have hLog := (((hY.div_const 2).const_add 2).log hBase.ne').neg
  have hFrac := hY.div ((hY.const_add 4).const_mul 2) (show 2 * (4 + y) ≠ 0 by positivity)
  convert hLog.add hFrac using 1
  simp only [highExponentLogCurvature]
  have hy' : 0 ≤ highExponentScale c p := hy
  field_simp [hp.ne',show 2 + highExponentScale c p / 2 ≠ 0 by positivity,
    show 4 + highExponentScale c p ≠ 0 by positivity]
  <;> ring_nf
  <;> field_simp [show 16 + highExponentScale c p * 8 + highExponentScale c p ^ 2 ≠ 0 by positivity,
    show 4 + highExponentScale c p ≠ 0 by positivity]
  <;> ring

theorem highExponentTail_deriv {c p : ℝ} (hc : 0 ≤ c) (hp : 0 < p) :
    HasDerivAt (highExponentTail c)
      (highExponentTail c p * highExponentLogSlope c p) p :=
  (highExponentLogTail_deriv hc hp).exp

theorem highExponentTail_second {c p : ℝ} (hc : 0 ≤ c) (hp : 0 < p) :
    HasDerivAt (fun x => highExponentTail c x * highExponentLogSlope c x)
      (highExponentTail c p * (highExponentLogSlope c p ^ 2 + highExponentLogCurvature c p)) p := by
  convert (highExponentTail_deriv hc hp).mul (highExponentLogSlope_deriv hc hp) using 1
  ring

end ACS12.Pressure
