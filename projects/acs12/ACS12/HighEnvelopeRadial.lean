import ACS12.HighSwitchCorners

/-! The high pressure envelope is increasing and convex in its actual pressure coordinate. -/
namespace ACS12.Pressure

open Set

noncomputable def highMinimumUnitSlope (p y : ℝ) : ℝ :=
  p + 5 / 12 - (p / 2) * (2 + y / 2) ^ (-(p + 1))

noncomputable def highMinimumUnitCurvature (p y : ℝ) : ℝ :=
  (p * (p + 1) / 4) * (2 + y / 2) ^ (-(p + 2))

theorem highMinimumUnitPrice_deriv {p y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (highMinimumUnitPrice p) (highMinimumUnitSlope p y) y := by
  have hBase : 0 < 2 + y / 2 := by positivity
  convert ((hasDerivAt_id y).const_mul (p + 5 / 12)).add
    ((((hasDerivAt_id y).div_const 2).const_add 2).rpow_const (p := -p) (Or.inl hBase.ne')) using 1
  simp only [highMinimumUnitSlope,id_eq,mul_one]
  rw [show -p - 1 = -(p + 1) by ring]
  ring

theorem highMinimumUnitSlope_deriv {p y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (highMinimumUnitSlope p) (highMinimumUnitCurvature p y) y := by
  have hBase : 0 < 2 + y / 2 := by positivity
  convert (((((hasDerivAt_id y).div_const 2).const_add 2).rpow_const
    (p := -(p + 1)) (Or.inl hBase.ne')).const_mul (p / 2)).const_sub (p + 5 / 12) using 1
  simp only [highMinimumUnitCurvature,id_eq,mul_one]
  rw [show -(p + 1) - 1 = -(p + 2) by ring]
  ring

theorem highMinimumUnitSlope_pos {p y : ℝ} (hp : 2 ≤ p) (hy : 0 ≤ y) :
    0 < highMinimumUnitSlope p y := by
  have hp₀ : 0 ≤ p := by linarith only [hp]
  have hBase : 1 ≤ 2 + y / 2 := by linarith only [hy]
  have hPow : (2 + y / 2) ^ (-(p + 1)) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hBase (show -(p + 1) ≤ 0 by linarith only [hp])
    simpa only [Real.rpow_zero] using h
  have h := mul_le_mul_of_nonneg_left hPow (div_nonneg hp₀ (by norm_num : (0 : ℝ) ≤ 2))
  unfold highMinimumUnitSlope
  linarith only [h,hp]

theorem highMinimumUnitPrice_mono {p : ℝ} (hp : 2 ≤ p) :
    MonotoneOn (highMinimumUnitPrice p) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact fun y hy => (highMinimumUnitPrice_deriv hy).continuousAt.continuousWithinAt
  · exact fun y hy => (highMinimumUnitPrice_deriv (interior_subset hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [(highMinimumUnitPrice_deriv (interior_subset hy)).deriv]
    exact (highMinimumUnitSlope_pos hp (interior_subset hy)).le

noncomputable def highPressureScale (p R : ℝ) : ℝ := Real.sqrt (R / (7 * p))
noncomputable def highPressureSmooth (p R : ℝ) : ℝ := (R / 2) * highMinimumUnitPrice p (highPressureScale p R)
noncomputable def highPressureRadialSlope (p R : ℝ) : ℝ :=
  highMinimumUnitPrice p (highPressureScale p R) / 2 +
    highPressureScale p R * highMinimumUnitSlope p (highPressureScale p R) / 4

theorem highPressureScale_pos {p R : ℝ} (hp : 2 ≤ p) (hR : 0 < R) : 0 < highPressureScale p R :=
  Real.sqrt_pos.mpr (div_pos hR (by linarith only [hp]))

theorem highPressureScale_deriv {p R : ℝ} (hp : 2 ≤ p) (hR : 0 < R) :
    HasDerivAt (highPressureScale p) (highPressureScale p R / (2 * R)) R := by
  have hp₀ : 0 < p := by linarith only [hp]
  have hY := highPressureScale_pos hp hR
  have hQ : 0 < R / (7 * p) := div_pos hR (by positivity)
  have hSquare : highPressureScale p R ^ 2 = R / (7 * p) := Real.sq_sqrt hQ.le
  convert ((hasDerivAt_id R).div_const (7 * p)).sqrt hQ.ne' using 1
  simp only [id_eq,one_div]
  unfold highPressureScale at *
  field_simp [hY.ne',hR.ne',hp₀.ne']
  have hSq := (eq_div_iff (show 7 * p ≠ 0 by positivity)).mp hSquare
  nlinarith only [hSq]

theorem highPressureSmooth_deriv {p R : ℝ} (hp : 2 ≤ p) (hR : 0 < R) :
    HasDerivAt (highPressureSmooth p) (highPressureRadialSlope p R) R := by
  have hy := highPressureScale_pos hp hR
  have hY := highPressureScale_deriv hp hR
  convert ((hasDerivAt_id R).div_const 2).mul ((highMinimumUnitPrice_deriv (p := p) hy.le).comp R hY) using 1
  simp only [highPressureRadialSlope,Function.comp_apply,id_eq]
  field_simp [hR.ne']
  <;> ring

theorem highPressureRadialSlope_deriv {p R : ℝ} (hp : 2 ≤ p) (hR : 0 < R) :
    let y := highPressureScale p R
    HasDerivAt (highPressureRadialSlope p)
      (y / (8 * R) * (3 * highMinimumUnitSlope p y + y * highMinimumUnitCurvature p y)) R := by
  have hy := highPressureScale_pos hp hR
  have hY := highPressureScale_deriv hp hR
  have hB := (highMinimumUnitPrice_deriv (p := p) hy.le).comp R hY
  have hD := (highMinimumUnitSlope_deriv (p := p) hy.le).comp R hY
  convert (hB.div_const 2).add ((hY.mul hD).div_const 4) using 1
  simp only [Function.comp_apply]
  ring

theorem highPressureSmooth_convex {p : ℝ} (hp : 2 ≤ p) :
    ConvexOn ℝ (Ioi 0) (highPressureSmooth p) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi _)
    (f' := highPressureRadialSlope p)
    (f'' := fun R => let y := highPressureScale p R
      y / (8 * R) * (3 * highMinimumUnitSlope p y + y * highMinimumUnitCurvature p y))
  · exact fun R hR => (highPressureSmooth_deriv hp hR).continuousAt.continuousWithinAt
  · exact fun R hR => (highPressureSmooth_deriv hp (interior_subset hR)).hasDerivWithinAt
  · exact fun R hR => (highPressureRadialSlope_deriv hp (interior_subset hR)).hasDerivWithinAt
  · intro R hR
    have hR₀ : 0 < R := interior_subset hR
    have hy := highPressureScale_pos hp hR₀
    have hD := highMinimumUnitSlope_pos hp hy.le
    unfold highMinimumUnitCurvature
    positivity

theorem highPressureSmooth_mono {p : ℝ} (hp : 2 ≤ p) :
    MonotoneOn (highPressureSmooth p) (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
  · exact fun R hR => (highPressureSmooth_deriv hp hR).continuousAt.continuousWithinAt
  · exact fun R hR => (highPressureSmooth_deriv hp (interior_subset hR)).differentiableAt.differentiableWithinAt
  · intro R hR
    have hR₀ : 0 < R := interior_subset hR
    have hy := highPressureScale_pos hp hR₀
    have hD := highMinimumUnitSlope_pos hp hy.le
    rw [(highPressureSmooth_deriv hp hR₀).deriv]
    unfold highPressureRadialSlope highMinimumUnitPrice
    positivity

theorem highPressureEnvelope_eq {p R : ℝ} (hR : 0 < R) :
    highPressureEnvelope p R = max (R / 2) (highPressureSmooth p R) := by
  unfold highPressureEnvelope highPressureSmooth highPressureScale
  rw [mul_max_of_nonneg _ _ (by positivity : 0 ≤ R / 2),mul_one]

theorem highPressureEnvelope_convex_radial {p : ℝ} (hp : 2 ≤ p) :
    ConvexOn ℝ (Ioi 0) (highPressureEnvelope p) := by
  have hA : ConvexOn ℝ (Ioi 0) (fun R : ℝ => R / 2) := by
    refine ⟨convex_Ioi _,?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    ring_nf
    exact le_rfl
  exact (hA.sup (highPressureSmooth_convex hp)).congr
    (fun R hR => (highPressureEnvelope_eq hR).symm)

theorem highPressureEnvelope_mono_radial {p : ℝ} (hp : 2 ≤ p) :
    MonotoneOn (highPressureEnvelope p) (Ioi 0) := by
  intro R hR T hT h
  rw [highPressureEnvelope_eq hR,highPressureEnvelope_eq hT]
  exact max_le_max (by linarith only [h]) (highPressureSmooth_mono hp hR hT h)

end ACS12.Pressure
