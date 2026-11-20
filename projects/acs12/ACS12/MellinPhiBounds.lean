import ACS12.JointLaplaceCarrier

/-! Whole positive-axis Phi bounds pay the actual Mellin carrier tail on every compact positive-shape set. -/
namespace ACS12.NativeCells
open MeasureTheory ProbabilityTheory Set GammaMixture

noncomputable def mellinPhi (t : ℝ) : ℝ :=
  Real.sqrt t/(2*Real.sinh (Real.sqrt t/2))

theorem mellinPhi_pos {t : ℝ} (ht : 0 < t) : 0 < mellinPhi t := by
  unfold mellinPhi
  positivity

theorem mellinPhi_le_one {t : ℝ} (ht : 0 < t) : mellinPhi t ≤ 1 := by
  have hv := Real.sqrt_pos.mpr ht
  unfold mellinPhi
  apply (div_le_one (by positivity)).mpr
  have h := Real.self_le_sinh_iff.mpr (half_pos hv).le
  linarith only [h]

theorem mellinPhi_tail {t : ℝ} (ht : 1 ≤ t) :
    mellinPhi t ≤ (1-Real.exp (-1))⁻¹*Real.sqrt t*Real.exp (-Real.sqrt t/2) := by
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  let v := Real.sqrt t
  have hv : 0 < v := Real.sqrt_pos.mpr ht₀
  have hv₁ : 1 ≤ v := by
    unfold v
    have h := Real.sqrt_le_sqrt ht
    simpa only [Real.sqrt_one] using h
  have hK : 0 < 1-Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hD : 2*Real.sinh (v/2) = Real.exp (v/2)*(1-Real.exp (-v)) := by
    rw [Real.sinh_eq,mul_sub,mul_one,← Real.exp_add]
    rw [show v/2 + -v = -(v/2) by ring]
    ring
  have hGap : 1-Real.exp (-1) ≤ 1-Real.exp (-v) :=
    sub_le_sub_left (Real.exp_le_exp.mpr (by linarith only [hv₁])) 1
  have hBound : v/(2*Real.sinh (v/2)) ≤ v/(Real.exp (v/2)*(1-Real.exp (-1))) := by
    apply div_le_div_of_nonneg_left hv.le (mul_pos (Real.exp_pos _) hK)
    rw [hD]
    exact mul_le_mul_of_nonneg_left hGap (Real.exp_pos _).le
  have hEq : v/(Real.exp (v/2)*(1-Real.exp (-1))) =
      (1-Real.exp (-1))⁻¹*v*Real.exp (-v/2) := by
    rw [show -v/2 = -(v/2) by ring,Real.exp_neg]
    field_simp [hK.ne',Real.exp_ne_zero]
    simp only [← Real.exp_add,add_neg_cancel,Real.exp_zero,one_div]
  exact hBound.trans_eq hEq

theorem gammaLaplaceGerm_one_real {t : ℝ} (ht : 0 < t) :
    gammaLaplaceGerm 1 (t:ℂ) = (mellinPhi t:ℂ) := by
  have h := gammaLaplaceGerm_real zero_lt_one (Real.sqrt_pos.mpr ht)
  rw [Real.sq_sqrt ht.le,Real.rpow_one] at h
  exact h

theorem jointLaplaceCarrier_norm_le {α : ℂ} {z t : ℝ} (hz : 0 ≤ z) (ht : 0 < t) :
    ‖jointLaplaceCarrier α z (t:ℂ)‖ ≤ (mellinPhi t)^α.re := by
  letI := boseNoise_probability
  have hφ := mellinPhi_pos ht
  have hLog : jointPhiLog (t:ℂ) = (Real.log (mellinPhi t):ℂ) := by
    unfold jointPhiLog
    rw [gammaLaplaceGerm_one_real ht,← Complex.ofReal_log hφ.le]
  have hNoise : ‖complexMGF boseNoise boseNoiseMeasure (-(z:ℂ)*(t:ℂ))‖ ≤ 1 := by
    have h := norm_complexMGF_le_mgf (X := boseNoise) (μ := boseNoiseMeasure)
      (z := -(z:ℂ)*(t:ℂ))
    have hR : (-(z:ℂ)*(t:ℂ)).re = -(z*t) := by simp
    rw [hR] at h
    apply h.trans
    unfold mgf
    have hB := integral_mono_of_nonneg (μ := boseNoiseMeasure)
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le) (integrable_const (1:ℝ))
      (boseNoise_ae_pos.mono fun s hs =>
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hz ht.le)) hs.le))
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hB
  unfold jointLaplaceCarrier
  rw [hLog,norm_mul,Complex.norm_exp]
  have hRe : (α*(Real.log (mellinPhi t):ℂ)).re = α.re*Real.log (mellinPhi t) := by simp
  rw [hRe,Real.rpow_def_of_pos hφ]
  have h := mul_le_mul_of_nonneg_left hNoise (Real.exp_pos (α.re*Real.log (mellinPhi t))).le
  simpa only [mul_one,one_mul,mul_comm] using h

end ACS12.NativeCells
