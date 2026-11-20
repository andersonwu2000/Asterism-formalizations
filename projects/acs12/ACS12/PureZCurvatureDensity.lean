import ACS12.PeanoExponentShape

/-! Exponent curvature and its spatial derivatives for the complete Z estimate. -/

namespace ACS12.GammaMeasure

open Set

noncomputable def zetaCurvature (p x : ℝ) : ℝ :=
  x ^ (-(p + 1)) * Real.log x * (p * Real.log x - 2)

noncomputable def zetaCurvatureSlope (p x : ℝ) : ℝ :=
  x ^ (-(p + 2)) * peanoExponentQuadratic p (Real.log x)

noncomputable def zetaCurvatureQuadratic (p y : ℝ) : ℝ :=
  p * (p + 1) * (p + 2) * y ^ 2 - (6 * p ^ 2 + 12 * p + 4) * y + 6 * p + 6

noncomputable def zetaCurvatureSpatial (p x : ℝ) : ℝ :=
  x ^ (-(p + 3)) * zetaCurvatureQuadratic p (Real.log x)

noncomputable def zetaCurvaturePrimitive (p x : ℝ) : ℝ :=
  -(x ^ (-p) * Real.log x ^ 2)

theorem zetaCurvaturePrimitive_hasDerivAt (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zetaCurvaturePrimitive p) (zetaCurvature p x) x := by
  have hL := Real.hasDerivAt_log hx.ne'
  have hP := Real.hasDerivAt_rpow_const (p := -p) (Or.inl hx.ne')
  convert (hP.mul (hL.pow 2)).neg using 1
  simp only [Pi.pow_apply]
  rw [zetaCurvature, show -(p + 1) = -p - 1 by ring, Real.rpow_sub_one hx.ne']
  field_simp [hx.ne']
  ring

theorem zetaCurvature_hasDerivAt (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zetaCurvature p) (zetaCurvatureSlope p x) x := by
  have hL := Real.hasDerivAt_log hx.ne'
  have hP := Real.hasDerivAt_rpow_const (p := -(p + 1)) (Or.inl hx.ne')
  convert (hP.mul hL).mul ((hL.const_mul p).sub_const 2) using 1
  simp only [zetaCurvatureSlope, peanoExponentQuadratic, Pi.mul_apply]
  rw [show -(p + 2) = -(p + 1) - 1 by ring, Real.rpow_sub_one hx.ne']
  field_simp [hx.ne']
  ring

theorem zetaCurvatureSlope_hasDerivAt (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (zetaCurvatureSlope p) (zetaCurvatureSpatial p x) x := by
  have hL := Real.hasDerivAt_log hx.ne'
  have hP := Real.hasDerivAt_rpow_const (p := -(p + 2)) (Or.inl hx.ne')
  have hQ := ((hL.const_mul (2 * (2 * p + 1))).sub ((hL.pow 2).const_mul (p * (p + 1)))).sub_const 2
  convert hP.mul hQ using 1
  simp only [Pi.pow_apply, Pi.sub_apply]
  rw [zetaCurvatureSpatial, zetaCurvatureQuadratic, show -(p + 3) = -(p + 2) - 1 by ring,
    Real.rpow_sub_one hx.ne']
  field_simp [hx.ne']
  ring

theorem zetaCurvatureSpatial_continuousOn (p : ℝ) :
    ContinuousOn (zetaCurvatureSpatial p) (Ioi 0) := by
  have hL : ContinuousOn Real.log (Ioi 0) :=
    fun x hx => (Real.continuousAt_log (show 0 < x from hx).ne').continuousWithinAt
  have hQ : Continuous (zetaCurvatureQuadratic p) := by unfold zetaCurvatureQuadratic; fun_prop
  exact (continuousOn_id.rpow_const (fun x hx => Or.inl (show 0 < x from hx).ne')).mul
    (hQ.comp_continuousOn hL)

theorem zetaTerm_exponent_hasDerivAt {x : ℝ} (hx : 0 < x) (p : ℝ) :
    HasDerivAt (fun q => q * x ^ (-(q + 1))) (x ^ (-(p + 1)) * (1 - p * Real.log x)) p := by
  have hP : HasDerivAt (fun q => x ^ (-(q + 1))) (x ^ (-(p + 1)) * (-Real.log x)) p := by
    simp_rw [Real.rpow_def_of_pos hx]
    convert (((hasDerivAt_id p).add_const 1).neg.const_mul (Real.log x)).exp using 1
    simp only [Pi.neg_apply, id_eq]
    ring
  convert (hasDerivAt_id p).mul hP using 1
  simp only [id_eq]
  ring

theorem zetaTerm_exponent_second_hasDerivAt {x : ℝ} (hx : 0 < x) (p : ℝ) :
    HasDerivAt (fun q => x ^ (-(q + 1)) * (1 - q * Real.log x)) (zetaCurvature p x) p := by
  have hP : HasDerivAt (fun q => x ^ (-(q + 1))) (x ^ (-(p + 1)) * (-Real.log x)) p := by
    simp_rw [Real.rpow_def_of_pos hx]
    convert (((hasDerivAt_id p).add_const 1).neg.const_mul (Real.log x)).exp using 1
    simp only [Pi.neg_apply, id_eq]
    ring
  convert hP.mul (((hasDerivAt_id p).mul_const (Real.log x)).const_sub 1) using 1
  simp only [zetaCurvature, id_eq]
  ring

end ACS12.GammaMeasure
