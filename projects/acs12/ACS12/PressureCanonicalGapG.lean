import ACS12.PressureGapSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The exact first-order canonical gap comparison, using the full residual. -/
namespace ACS12.Pressure

open Set

noncomputable def canonicalGapG (v : ℝ) : ℝ :=
  Real.cosh v ^ (5 / 14 : ℝ) - Real.cosh ((5 / 14) * v)

noncomputable def canonicalGapLower (v : ℝ) : ℝ :=
  (45 / 392) * v ^ 2 * (1 + v ^ 2 / 10) / (1 + (887 / 3920) * v ^ 2)

private theorem canonicalGapG_deriv (v : ℝ) :
    HasDerivAt canonicalGapG
      ((5 / 14) * Real.sinh v * Real.cosh v ^ (5 / 14 : ℝ) / Real.cosh v -
        (5 / 14) * Real.sinh ((5 / 14) * v)) v := by
  have hC := Real.cosh_pos v
  have h := ((Real.hasDerivAt_cosh v).rpow_const (p := (5 / 14 : ℝ)) (Or.inl hC.ne')).sub
    (((hasDerivAt_id v).const_mul (5 / 14 : ℝ)).cosh)
  convert h using 1
  simp only [id_eq,mul_one,Real.rpow_sub hC,Real.rpow_one]
  ring

private noncomputable def canonicalGapLowerD (v : ℝ) : ℝ :=
  (45 / 392) * (2 * v * (1 + 2 * (1 / 10) * v ^ 2 + (1 / 10) * (887 / 3920) * v ^ 4)) /
    (1 + (887 / 3920) * v ^ 2) ^ 2

private theorem canonicalGapLower_deriv (v : ℝ) :
    HasDerivAt canonicalGapLower (canonicalGapLowerD v) v := by
  have h := (hasDerivAt_id v).pow 2
  have hA := (((h.div_const 10).const_add 1).mul h).const_mul (45 / 392 : ℝ)
  have hB := (h.const_mul (887 / 3920 : ℝ)).const_add 1
  have hDen : 1 + (887 / 3920 : ℝ) * v ^ 2 ≠ 0 := by positivity
  convert hA.div hB hDen using 1
  · funext x
    simp only [canonicalGapLower,Pi.pow_apply,Pi.div_apply,Pi.mul_apply,id_eq]
    ring
  · norm_num [canonicalGapLowerD]
    field_simp [hDen]
    ring

private theorem canonicalGapResidual_eq (v : ℝ) :
    (5 / 14) * Real.sinh ((9 / 14) * v) + (5 / 14) * canonicalGapLower v * Real.sinh v -
        canonicalGapLowerD v * Real.cosh v =
      (45 / 392) * pressureGapResidual v / (1 + (887 / 3920) * v ^ 2) ^ 2 := by
  unfold canonicalGapLowerD canonicalGapLower pressureGapResidual
  field_simp [show 1 + (887 / 3920 : ℝ) * v ^ 2 ≠ 0 by positivity]
  ring

private theorem canonicalGapQuot_deriv (v : ℝ) :
    HasDerivAt (fun t => (canonicalGapG t - canonicalGapLower t) / Real.cosh t ^ (5 / 14 : ℝ))
      ((45 / 392) * pressureGapResidual v /
        ((1 + (887 / 3920) * v ^ 2) ^ 2 * (Real.cosh v ^ (5 / 14 : ℝ) * Real.cosh v))) v := by
  have hC := Real.cosh_pos v
  have hQ := (canonicalGapG_deriv v).sub (canonicalGapLower_deriv v)
  have hP := (Real.hasDerivAt_cosh v).rpow_const (p := (5 / 14 : ℝ)) (Or.inl hC.ne')
  have hN := Real.rpow_pos_of_pos hC (5 / 14)
  convert hQ.div hP hN.ne' using 1
  have hR := canonicalGapResidual_eq v
  have hS : Real.sinh ((9 / 14) * v) =
      Real.sinh v * Real.cosh ((5 / 14) * v) - Real.cosh v * Real.sinh ((5 / 14) * v) := by
    rw [← Real.sinh_sub,show v - (5 / 14) * v = (9 / 14) * v by ring]
  rw [hS] at hR
  have hDen : (1 + (887 / 3920 : ℝ) * v ^ 2) ≠ 0 := by positivity
  rw [show (45 / 392 : ℝ) * pressureGapResidual v /
        ((1 + (887 / 3920) * v ^ 2) ^ 2 * (Real.cosh v ^ (5 / 14 : ℝ) * Real.cosh v)) =
      ((45 / 392 : ℝ) * pressureGapResidual v / (1 + (887 / 3920) * v ^ 2) ^ 2) /
        (Real.cosh v ^ (5 / 14 : ℝ) * Real.cosh v) by rw [div_div]]
  rw [← hR,Real.rpow_sub hC,Real.rpow_one]
  simp only [Pi.sub_apply,canonicalGapG]
  field_simp [hC.ne',hN.ne']
  ring

theorem canonicalGapLower_lt {v : ℝ} (hv : 0 < v) (hV : v ^ 2 ≤ 2) :
    canonicalGapLower v < canonicalGapG v := by
  let F (t : ℝ) := (canonicalGapG t - canonicalGapLower t) / Real.cosh t ^ (5 / 14 : ℝ)
  have hC : Continuous F := continuous_iff_continuousAt.mpr fun t => (canonicalGapQuot_deriv t).continuousAt
  have hD : Differentiable ℝ F := fun t => (canonicalGapQuot_deriv t).differentiableAt
  have h₀ : F 0 = 0 := by norm_num [F,canonicalGapG,canonicalGapLower]
  obtain ⟨t,ht,hEq⟩ := exists_deriv_eq_slope F hv hC.continuousOn hD.differentiableOn
  have ht₂ := (pow_le_pow_left₀ ht.1.le ht.2.le 2).trans hV
  have hP := pressureGapResidual_pos ht.1 ht₂
  rw [(canonicalGapQuot_deriv t).deriv,h₀,sub_zero,sub_zero] at hEq
  have hQ : 0 < F v / v := hEq ▸ (by positivity)
  have hG : 0 < F v := (div_pos_iff_of_pos_right hv).mp hQ
  exact sub_pos.mp ((div_pos_iff_of_pos_right (Real.rpow_pos_of_pos (Real.cosh_pos v) (5 / 14))).mp hG)

theorem canonicalGapG_weak {v : ℝ} (hv : 0 ≤ v) (hV : v ^ 2 ≤ 2) :
    (45 / 392) * v ^ 2 / (1 + (99 / 784) * v ^ 2) ≤ canonicalGapG v := by
  rcases hv.eq_or_lt with rfl | hv
  · norm_num [canonicalGapG]
  apply le_trans _ (canonicalGapLower_lt hv hV).le
  unfold canonicalGapLower
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h : 0 ≤ v ^ 2 * v ^ 2 := by positivity
  nlinarith only [h,sq_nonneg (v ^ 2 * v)]

end ACS12.Pressure

