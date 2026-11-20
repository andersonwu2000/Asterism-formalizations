import ACS12.LowLineConvex

/-! The positive decreasing test weight for the exact mixed deficit. -/

namespace ACS12.GammaDeficit

open MeasureTheory Set
open CenteredCircle.AllN

noncomputable def tailDifference (b s : ℝ) : ℝ := scaledExpTail s b - scaledExpTail s 1

noncomputable def defectCore (b s : ℝ) : ℝ :=
  rightMixPolynomial s * tailDifference b s - (1 - b) * ((s / 4 + 5 / 4) * Real.exp (-s))

noncomputable def defectConstant (b : ℝ) : ℝ := (5 / 4) * (1 - b)

noncomputable def defectWeight (b s : ℝ) : ℝ := (defectConstant b + defectCore b s) / s

private theorem hasDerivAt_rightMixPolynomial (s : ℝ) :
    HasDerivAt rightMixPolynomial (1 - (1 + s / 4) * Real.exp (-s)) s := by
  convert (hasDerivAt_polyB s).sub ((hasDerivAt_polyA s).div_const 4) using 1
  ring

private theorem rightMixPolynomial_div_monotone :
    MonotoneOn (fun s : ℝ => rightMixPolynomial s / s) (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
  · intro s hs
    exact ((hasDerivAt_rightMixPolynomial s).div (hasDerivAt_id s)
      (mem_Ioi.mp hs).ne').continuousAt.continuousWithinAt
  · intro s hs
    have hs₀ : 0 < s := by simpa only [interior_Ioi, mem_Ioi] using hs
    exact ((hasDerivAt_rightMixPolynomial s).div (hasDerivAt_id s)
      hs₀.ne').differentiableAt.differentiableWithinAt
  · intro s hs
    have hs₀ : 0 < s := by simpa only [interior_Ioi, mem_Ioi] using hs
    have h := ((hasDerivAt_rightMixPolynomial s).div (hasDerivAt_id s) hs₀.ne').deriv
    change deriv (fun x => rightMixPolynomial x / x) s = _ at h
    rw [h]
    apply div_nonneg _ (sq_nonneg s)
    have he : Real.exp s * Real.exp (-s) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h := mul_le_mul_of_nonneg_right (Real.quadratic_le_exp_of_nonneg hs₀.le)
      (Real.exp_pos (-s)).le
    rw [he] at h
    have h₀ : 0 ≤ s ^ 2 * Real.exp (-s) := by positivity
    simp only [id_eq, mul_one, rightMixPolynomial, polyA, polyB]
    nlinarith only [h, h₀]

private theorem rightMixPolynomial_div_bounds {s : ℝ} (hs : 0 < s) :
    0 ≤ rightMixPolynomial s / s ∧ rightMixPolynomial s / s ≤ 1 := by
  refine ⟨(div_pos (rightMixPolynomial_pos hs) hs).le, (div_le_one hs).mpr ?_⟩
  unfold rightMixPolynomial polyB
  linarith [polyA_pos hs, Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs)]

private theorem neg_deriv_expTailFactor_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ -deriv expTailFactor x ∧ -deriv expTailFactor x ≤ 1 := by
  refine ⟨neg_nonneg.mpr ?_, ?_⟩
  · rw [← derivWithin_of_mem_nhds (Ioi_mem_nhds hx)]
    exact strictAntiOn_expTailFactor.antitoneOn.derivWithin_nonpos
  · rw [(hasDerivAt_expTailFactor hx).deriv, ← neg_div, div_le_iff₀ (sq_pos_of_pos (expTail_den_pos hx))]
    have h := mul_le_mul_of_nonneg_right ((Real.add_one_lt_exp hx.ne').le) (Real.exp_pos x).le
    nlinarith only [h]

private theorem tailDifference_continuousOn {b s : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1) (hs : 0 < s) :
    ContinuousOn (fun x : ℝ => -deriv expTailFactor (s * x)) (uIcc b 1) := by
  have hpos (x : ℝ) (hx : x ∈ uIcc b 1) : 0 < s*x := by
    rw [uIcc_of_le hb₁] at hx
    exact mul_pos hs (hb.trans_le hx.1)
  have he : EqOn (fun x : ℝ => -deriv expTailFactor (s * x))
      (fun x : ℝ => -((Real.exp (s*x) - 1 - (s*x)*Real.exp (s*x)) /
        (Real.exp (s*x) - 1)^2)) (uIcc b 1) := by
    intro x hx
    dsimp only
    rw [(hasDerivAt_expTailFactor (hpos x hx)).deriv]
  apply ContinuousOn.congr _ he
  intro x hx
  have hne := pow_ne_zero 2 (expTail_den_pos (hpos x hx)).ne'
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := assumption)

private theorem tailDifference_eq_integral {b s : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1)
    (hs : 0 < s) : tailDifference b s = ∫ x : ℝ in b..1, -deriv expTailFactor (s * x) := by
  have hSub : uIcc b 1 ⊆ Ioi 0 := by
    rw [uIcc_of_le hb₁]
    exact fun x hx => hb.trans_le hx.1
  have hD (x : ℝ) (hx : x ∈ uIcc b 1) :
      HasDerivAt (fun y : ℝ => -(expTailFactor (s * y) / s)) (-deriv expTailFactor (s * x)) x := by
    have h := (((hasDerivAt_expTailFactor (mul_pos hs (hSub hx))).comp x
      ((hasDerivAt_id x).const_mul s)).div_const s).neg
    convert h using 1
    rw [(hasDerivAt_expTailFactor (mul_pos hs (hSub hx))).deriv]
    field_simp [hs.ne']
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD (tailDifference_continuousOn hb hb₁ hs).intervalIntegrable, tailDifference,
    scaledExpTail_eq_factor hs, scaledExpTail_eq_factor hs]
  ring

private theorem tailDifference_bounds {b s : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1) (hs : 0 < s) :
    0 ≤ tailDifference b s ∧ tailDifference b s ≤ 1 - b := by
  rw [tailDifference_eq_integral hb hb₁ hs]
  refine ⟨intervalIntegral.integral_nonneg hb₁ (fun x hx =>
    (neg_deriv_expTailFactor_bounds (mul_pos hs (hb.trans_le hx.1))).1), ?_⟩
  have h := intervalIntegral.integral_mono_on (μ := volume) hb₁
    (tailDifference_continuousOn hb hb₁ hs).intervalIntegrable
    (intervalIntegrable_const (c := (1 : ℝ)))
    (fun x hx => (neg_deriv_expTailFactor_bounds (mul_pos hs (hb.trans_le hx.1))).2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using h

private theorem tailDifference_antitone {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1) :
    AntitoneOn (tailDifference b) (Ioi 0) := by
  intro s hs t ht hst
  rw [tailDifference_eq_integral hb hb₁ ht, tailDifference_eq_integral hb hb₁ hs]
  apply intervalIntegral.integral_mono_on hb₁ (tailDifference_continuousOn hb hb₁ ht).intervalIntegrable
    (tailDifference_continuousOn hb hb₁ hs).intervalIntegrable
  intro x hx
  have hx₀ := hb.trans_le hx.1
  apply neg_le_neg
  exact (LowScalar.expTail_convex.monotoneOn_deriv
    (fun _ hx => (hasDerivAt_expTailFactor hx).differentiableAt))
    (mul_pos hs hx₀) (mul_pos ht hx₀) (mul_le_mul_of_nonneg_right hst hx₀.le)

private theorem defectWeight_eq {b s : ℝ} (hs : 0 < s) :
    defectWeight b s = (1 - b) - (rightMixPolynomial s / s) * ((1 - b) - tailDifference b s) := by
  unfold defectWeight defectConstant defectCore rightMixPolynomial polyA polyB
  field_simp [hs.ne']
  ring

theorem defectWeight_bounds {b s : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1) (hs : 0 < s) :
    0 ≤ defectWeight b s ∧ defectWeight b s ≤ 1 - b := by
  rw [defectWeight_eq hs]
  obtain ⟨hv, hv₁⟩ := rightMixPolynomial_div_bounds hs
  obtain ⟨hd, hd₁⟩ := tailDifference_bounds hb hb₁ hs
  have hcost := sub_nonneg.mpr hd₁
  exact ⟨sub_nonneg.mpr ((mul_le_of_le_one_left hcost hv₁).trans (by linarith)),
    sub_le_self _ (mul_nonneg hv hcost)⟩

theorem defectWeight_antitone {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1) :
    AntitoneOn (defectWeight b) (Ioi 0) := by
  intro s hs t ht hst
  rw [defectWeight_eq ht, defectWeight_eq hs]
  apply sub_le_sub_left
  apply mul_le_mul (rightMixPolynomial_div_monotone hs ht hst)
    (sub_le_sub_left (tailDifference_antitone hb hb₁ hs ht hst) _)
    (sub_nonneg.mpr (tailDifference_bounds hb hb₁ hs).2) (rightMixPolynomial_div_bounds ht).1

theorem contDiffOn_defectWeight {b : ℝ} (hb : 0 < b) :
    ContDiffOn ℝ 1 (defectWeight b) (Ioi 0) := by
  intro s hs
  have hs₀ : 0 < s := hs
  have hne : s ≠ 0 := hs₀.ne'
  have h₁ := (expTail_den_pos hs₀).ne'
  have h₂ := (expTail_den_pos (mul_pos hs₀ hb)).ne'
  apply ContDiffAt.contDiffWithinAt
  unfold defectWeight defectCore tailDifference rightMixPolynomial polyA polyB scaledExpTail
  simp only [mul_one]
  fun_prop (disch := assumption)

end ACS12.GammaDeficit
