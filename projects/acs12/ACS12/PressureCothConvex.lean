import ACS12.PressureCanonicalData
import ACS12.BoseShape

/-! Pointwise convexity after the exact literal-self calibration. -/
namespace ACS12.Pressure

open Set CenteredCircle.AllN

noncomputable def rowBoseBeta (x : ℝ) : ℝ := 1 / (Real.exp x - 1)

theorem rowBoseBeta_eq_decay {x : ℝ} (hx : 0 < x) :
    rowBoseBeta x = Real.exp (-x) / (1 - Real.exp (-x)) := by
  have h := BoseShape.expTail_eq_decay hx
  unfold expTailFactor at h
  unfold rowBoseBeta
  apply (mul_right_inj' hx.ne').mp
  simpa only [← mul_div_assoc,mul_one] using h

private theorem rowBoseBeta_add_half_eq {x : ℝ} (hx : 0 < x) :
    rowBoseBeta x + 1 / 2 = Real.cosh (x / 2) / (2 * Real.sinh (x / 2)) := by
  have hx' : 0 < x / 2 := half_pos hx
  let E := Real.exp (x / 2)
  have hE : 0 < E := Real.exp_pos _
  have hE' : E ^ 2 - 1 ≠ 0 := by
    have h : 1 < E := Real.one_lt_exp_iff.mpr hx'
    nlinarith only [h,sq_nonneg (E - 1)]
  have hS : E - E⁻¹ ≠ 0 := by
    have h : 0 < Real.sinh (x / 2) := Real.sinh_pos_iff.mpr hx'
    rw [Real.sinh_eq,Real.exp_neg] at h
    exact ne_of_gt (by linarith only [h])
  have hX : Real.exp x = E ^ 2 := by
    unfold E
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [rowBoseBeta,hX,Real.cosh_eq,Real.sinh_eq,Real.exp_neg]
  change 1 / (E ^ 2 - 1) + 1 / 2 = ((E + E⁻¹) / 2) / (2 * ((E - E⁻¹) / 2))
  field_simp [hE.ne',hE',hS]
  ring

private theorem sinh_sub_self_cosh_nonpos {x : ℝ} (hx : 0 < x) :
    Real.sinh x - x * Real.cosh x ≤ 0 := by
  let f (x : ℝ) := x * Real.cosh x - Real.sinh x
  have hD (x : ℝ) : HasDerivAt f (x * Real.sinh x) x := by
    convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x) using 1
    simp only [id_eq,one_mul,add_sub_cancel_left]
  have h := BoseShape.positive_of_derivative (by simp [f]) hD
    (fun x hx => mul_pos hx (Real.sinh_pos_iff.mpr hx)) hx
  dsimp only [f] at h
  linarith only [h]

private theorem self_div_sinh_anti : AntitoneOn (fun x : ℝ => x / Real.sinh x) (Ioi 0) := by
  have hD (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x => x / Real.sinh x) ((Real.sinh x - x * Real.cosh x) / Real.sinh x ^ 2) x := by
    simpa only [id_eq,one_mul] using (hasDerivAt_id x).div (Real.hasDerivAt_sinh x)
      (Real.sinh_pos_iff.mpr hx).ne'
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _)
  · exact fun x hx => (hD x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hD x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx₀ : 0 < x := interior_subset hx
    rw [(hD x hx₀).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (sinh_sub_self_cosh_nonpos hx₀) (sq_nonneg _)

private noncomputable def cothLog (p s v : ℝ) : ℝ :=
  -p * v + Real.log (Real.cosh (s * Real.exp (-v) / 2)) -
    Real.log (Real.sinh (s * Real.exp (-v) / 2))

private theorem cothLog_deriv {p s : ℝ} (hs : 0 < s) (v : ℝ) :
    HasDerivAt (cothLog p s) (-p + (s * Real.exp (-v)) / Real.sinh (s * Real.exp (-v))) v := by
  let z := s * Real.exp (-v) / 2
  have hz : 0 < z := by dsimp only [z]; positivity
  have hZ : HasDerivAt (fun v => s * Real.exp (-v) / 2) (-z) v := by
    convert (((hasDerivAt_id v).neg.exp).const_mul s).div_const 2 using 1
    simp only [Pi.neg_apply,id_eq,z]
    ring
  have hC := hZ.cosh.log (Real.cosh_pos z).ne'
  have hS := hZ.sinh.log (Real.sinh_pos_iff.mpr hz).ne'
  convert (((hasDerivAt_id v).const_mul (-p)).add hC).sub hS using 1
  change -p + s * Real.exp (-v) / Real.sinh (s * Real.exp (-v)) =
    -p * 1 + Real.sinh z * -z / Real.cosh z - Real.cosh z * -z / Real.sinh z
  have hT : s * Real.exp (-v) = z + z := by dsimp only [z]; ring
  have hDen : Real.sinh z * Real.cosh z + Real.cosh z * Real.sinh z ≠ 0 :=
    (add_pos (mul_pos (Real.sinh_pos_iff.mpr hz) (Real.cosh_pos z))
      (mul_pos (Real.cosh_pos z) (Real.sinh_pos_iff.mpr hz))).ne'
  have hM : s * Real.exp (-v) / Real.sinh (s * Real.exp (-v)) = z / (Real.sinh z * Real.cosh z) := by
    rw [hT,Real.sinh_add]
    field_simp [(Real.cosh_pos z).ne',(Real.sinh_pos_iff.mpr hz).ne',hDen]
  rw [hM]
  field_simp [(Real.cosh_pos z).ne',(Real.sinh_pos_iff.mpr hz).ne']
  linear_combination -z * (Real.cosh_sq_sub_sinh_sq z)

noncomputable def calibratedBose (p s v : ℝ) : ℝ :=
  Real.exp (-p * v) * (rowBoseBeta (s * Real.exp (-v)) + 1 / 2)

private theorem calibratedBose_eq {p s v : ℝ} (hs : 0 < s) :
    calibratedBose p s v = (1 / 2) * Real.exp (cothLog p s v) := by
  have hT := mul_pos hs (Real.exp_pos (-v))
  have hS : 0 < Real.sinh (s * Real.exp (-v) / 2) := Real.sinh_pos_iff.mpr (by positivity)
  unfold calibratedBose cothLog
  rw [rowBoseBeta_add_half_eq hT,Real.exp_sub,Real.exp_add,
    Real.exp_log (Real.cosh_pos _),Real.exp_log hS]
  ring

private theorem cothLog_strictAnti {p s : ℝ} (hp : 1 ≤ p) (hs : 0 < s) :
    StrictAnti (cothLog p s) := by
  apply strictAnti_of_deriv_neg
  intro v
  rw [(cothLog_deriv hs v).deriv]
  have hX := mul_pos hs (Real.exp_pos (-v))
  have h := (div_lt_one (Real.sinh_pos_iff.mpr hX)).mpr (Real.self_lt_sinh_iff.mpr hX)
  linarith only [hp,h]

theorem calibratedBose_strictConvex {p s : ℝ} (hp : 1 ≤ p) (hs : 0 < s) :
    StrictConvexOn ℝ univ (calibratedBose p s) := by
  have hD (v : ℝ) := cothLog_deriv (p := p) hs v
  have hLog : ConvexOn ℝ univ (cothLog p s) := by
    apply MonotoneOn.convexOn_of_deriv convex_univ
    · exact fun v _ => (hD v).continuousAt.continuousWithinAt
    · exact fun v _ => (hD v).differentiableAt.differentiableWithinAt
    · intro x hx y hy h
      rw [(hD x).deriv,(hD y).deriv]
      have hE := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg h)) hs.le
      exact add_le_add_right (self_div_sinh_anti (mul_pos hs (Real.exp_pos _))
        (mul_pos hs (Real.exp_pos _)) hE) _
  refine ⟨convex_univ,?_⟩
  intro x hx y hy hxy a b ha hb hab
  simp only [smul_eq_mul,calibratedBose_eq hs]
  have hA := hLog.2 hx hy ha.le hb.le hab
  simp only [smul_eq_mul] at hA
  have hB := strictConvexOn_exp.2 (mem_univ (cothLog p s x)) (mem_univ (cothLog p s y))
    ((cothLog_strictAnti hp hs).injective.ne hxy) ha hb hab
  simp only [smul_eq_mul] at hB
  have h := (Real.exp_le_exp.mpr hA).trans_lt hB
  linarith only [h]

theorem calibratedBose_strictAnti {p s : ℝ} (hp : 1 ≤ p) (hs : 0 < s) :
    StrictAnti (calibratedBose p s) := by
  intro x y h
  rw [calibratedBose_eq hs,calibratedBose_eq hs]
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (cothLog_strictAnti hp hs h)) (by norm_num)

end ACS12.Pressure
