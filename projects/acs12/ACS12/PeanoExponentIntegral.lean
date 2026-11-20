import ACS12.PeanoExponentShape

/-! The complete integral of the adverse Peano exponent curvature. -/

namespace ACS12.GammaMeasure

open MeasureTheory Set Filter

theorem peanoExponentBad_integral {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    IntegrableOn (peanoExponentBad p) (Ioi 0) ∧
      (∫ x : ℝ in Ioi 0, peanoExponentBad p x) < 8 / 25 := by
  let A := 2 * (2 * p + 1)
  let B := p * (p + 1)
  let D := A ^ 2 - 8 * B
  let q := Real.sqrt D
  let r₁ := (A - q) / (2 * B)
  let r₂ := (A + q) / (2 * B)
  let x₁ := Real.exp r₁
  let x₂ := Real.exp r₂
  let G (x : ℝ) := x ^ (-(p + 2)) * peanoExponentQuadratic p (Real.log x)
  let F (x : ℝ) := x ^ (-(p + 1)) * Real.log x * (p * Real.log x - 2)
  have hp₀ := zero_lt_one.trans_le hp
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hD : 0 < D := by
    dsimp only [D, A, B]
    nlinarith only [hp, sq_nonneg p]
  have hq : 0 < q := Real.sqrt_pos_of_pos hD
  have hq₂ : q ^ 2 = D := Real.sq_sqrt hD.le
  have hqA : q < A := by
    by_contra! h
    have hM := pow_le_pow_left₀ hA.le h 2
    dsimp only [D] at hq₂
    nlinarith only [hM, hq₂, hB]
  have hr₁ : 0 < r₁ := div_pos (sub_pos.mpr hqA) (by positivity)
  have hr : r₁ < r₂ := div_lt_div_of_pos_right (by linarith only [hq]) (by positivity)
  have hr₂ := hr₁.trans hr
  have hx : x₁ < x₂ := Real.exp_lt_exp.mpr hr
  have hx₁ : 0 < x₁ := Real.exp_pos _
  have hFactor (y : ℝ) : peanoExponentQuadratic p y = B * (y - r₁) * (r₂ - y) := by
    change A * y - B * y ^ 2 - 2 = _
    have hDen : 2 * B ≠ 0 := by positivity
    have h₁ : y - r₁ = (2 * B * y - A + q) / (2 * B) := by
      dsimp only [r₁]
      field_simp [hDen, hB.ne'] <;> ring
    have h₂ : r₂ - y = (A + q - 2 * B * y) / (2 * B) := by
      dsimp only [r₂]
      field_simp [hDen, hB.ne'] <;> ring
    rw [h₁, h₂]
    calc
      _ = (B * (2 * B * y - A + q) * (A + q - 2 * B * y)) / (2 * B) ^ 2 := by
        apply (eq_div_iff (pow_ne_zero _ hDen)).mpr
        dsimp only [D] at hq₂
        linear_combination -B * hq₂
      _ = _ := by ring
  have hPoint (x : ℝ) (hx₀ : x ∈ Ioi (0 : ℝ)) :
      peanoExponentBad p x = (Ioc x₁ x₂).indicator G x := by
    have hx' : 0 < x := hx₀
    by_cases h : x ∈ Ioc x₁ x₂
    · have h1 : r₁ ≤ Real.log x := by
        have h' := Real.log_le_log hx₁ h.1.le
        simpa only [x₁, Real.log_exp] using h'
      have h2 : Real.log x ≤ r₂ := by
        have h' := Real.log_le_log hx' h.2
        simpa only [x₂, Real.log_exp] using h'
      have hQ : 0 ≤ peanoExponentQuadratic p (Real.log x) := by
        rw [hFactor]
        exact mul_nonneg (mul_nonneg hB.le (sub_nonneg.mpr h1)) (sub_nonneg.mpr h2)
      rw [indicator_of_mem h, peanoExponentBad, max_eq_right hQ]
    · have hQ : peanoExponentQuadratic p (Real.log x) ≤ 0 := by
        rw [hFactor]
        rcases le_or_gt x x₁ with h' | h'
        · have hL : Real.log x ≤ r₁ := by
            simpa only [x₁, Real.log_exp] using Real.log_le_log hx' h'
          exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hB.le
            (sub_nonpos.mpr hL)) (sub_nonneg.mpr (hL.trans hr.le))
        · have hx₂ : x₂ ≤ x := le_of_not_ge (fun h₂ => h ⟨h', h₂⟩)
          have hL : r₂ ≤ Real.log x := by
            simpa only [x₂, Real.log_exp] using Real.log_le_log (Real.exp_pos r₂) hx₂
          exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg hB.le (sub_nonneg.mpr (hr.le.trans hL))) (sub_nonpos.mpr hL)
      rw [indicator_of_notMem h, peanoExponentBad, max_eq_left hQ, mul_zero]
  have hGcont : ContinuousOn G (Icc x₁ x₂) := by
    have hL : ContinuousOn Real.log (Icc x₁ x₂) :=
      fun x hx => (Real.continuousAt_log (hx₁.trans_le hx.1).ne').continuousWithinAt
    have hQ : Continuous (peanoExponentQuadratic p) := by unfold peanoExponentQuadratic; fun_prop
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (hx₁.trans_le hx.1).ne')).mul
      (hQ.comp_continuousOn hL)
  have hGI := hGcont.intervalIntegrable_of_Icc (μ := volume) hx.le
  have hSub : Ioc x₁ x₂ ∩ Ioi (0 : ℝ) = Ioc x₁ x₂ :=
    inter_eq_left.mpr (fun x h => hx₁.trans h.1)
  have hI : IntegrableOn ((Ioc x₁ x₂).indicator G) (Ioi 0) := by
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioc, hSub]
    exact hGI.1
  refine ⟨hI.congr ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hPoint x hx).symm
  · rw [setIntegral_congr_fun measurableSet_Ioi hPoint, integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, hSub, ← intervalIntegral.integral_of_le hx.le]
    have hFD (x : ℝ) (hx : 0 < x) : HasDerivAt F (G x) x := by
      have hL := Real.hasDerivAt_log hx.ne'
      have hP := Real.hasDerivAt_rpow_const (p := -(p + 1)) (Or.inl hx.ne')
      convert (hP.mul hL).mul ((hL.const_mul p).sub_const 2) using 1
      simp only [G, peanoExponentQuadratic, Pi.mul_apply]
      rw [show -(p + 1) - 1 = -(p + 2) by ring,
        show x ^ (-(p + 2)) = x ^ (-(p + 1)) / x by
          rw [show -(p + 2) = -(p + 1) - 1 by ring, Real.rpow_sub_one hx.ne']]
      field_simp [hx.ne']
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx' => hFD x (by
      rw [uIcc_of_le hx.le] at hx'
      exact hx₁.trans_le hx'.1)) hGI]
    have hVal (r : ℝ) : F (Real.exp r) = Real.exp (-(p + 1) * r) * r * (p * r - 2) := by
      simp only [F, Real.rpow_def_of_pos (Real.exp_pos r), Real.log_exp]
      rw [mul_comm r (-(p + 1))]
    change F (Real.exp r₂) - F (Real.exp r₁) < _
    rw [hVal, hVal]
    have hL := lower_cut_value_le hp hr₁.le
    have hU := upper_cut_value_lt hp hP hr₂.le
    nlinarith only [hL, hU]

end ACS12.GammaMeasure
