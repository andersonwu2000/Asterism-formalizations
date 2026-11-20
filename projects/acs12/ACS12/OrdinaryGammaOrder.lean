import ACS12.RealBetaCore

/-! One ordinary beta integral orders the normalized Gamma modulus at every positive real shape. -/
namespace ACS12
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem ordinaryBeta_norm_le {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ‖Complex.betaIntegral u v‖ ≤ GammaDeficit.betaReal u.re v.re := by
  rw [← GammaDeficit.betaReal_eq_integral hu hv]
  unfold Complex.betaIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo]
  calc
    _ ≤ ∫ x : ℝ in Ioo 0 1, ‖(x:ℂ)^(u-1)*(1-(x:ℂ))^(v-1)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      change ‖(x:ℂ)^(u-1)*(1-(x:ℂ))^(v-1)‖ = GammaDeficit.betaKernel u.re v.re x
      rw [norm_mul,show (1:ℂ)-(x:ℂ) = ((1-x:ℝ):ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
        Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
      simp only [Complex.sub_re,Complex.one_re,GammaDeficit.betaKernel]

theorem normalizedGammaModulus_le_of_lt {s t ξ : ℝ} (hs : 0 < s) (hst : s < t) :
    ‖Complex.Gamma ((s:ℂ)+(ξ:ℂ)*Complex.I)‖/Real.Gamma s ≤
      ‖Complex.Gamma ((t:ℂ)+(ξ:ℂ)*Complex.I)‖/Real.Gamma t := by
  let u : ℂ := (s:ℂ)+(ξ:ℂ)*Complex.I
  let v : ℂ := ((t-s:ℝ):ℂ)
  have hReu : u.re = s := by simp [u,Complex.mul_re]
  have hRev : v.re = t-s := by simp [v]
  have hu : 0 < u.re := by rwa [hReu]
  have hv : 0 < v.re := by rw [hRev]; exact sub_pos.mpr hst
  have ht : 0 < t := hs.trans hst
  have hGs := Real.Gamma_pos_of_pos hs
  have hGt := Real.Gamma_pos_of_pos ht
  have hGv := Real.Gamma_pos_of_pos (sub_pos.mpr hst)
  have hSum : u+v = (t:ℂ)+(ξ:ℂ)*Complex.I := by
    dsimp only [u,v]
    push_cast
    ring
  have hNormV : ‖Complex.Gamma v‖ = Real.Gamma (t-s) := by
    dsimp only [v]
    rw [Complex.Gamma_ofReal,Complex.norm_real,Real.norm_of_nonneg hGv.le]
  have hNorm := congrArg norm (Complex.Gamma_mul_Gamma_eq_betaIntegral hu hv)
  rw [norm_mul,norm_mul,hSum,hNormV] at hNorm
  have hBeta := ordinaryBeta_norm_le hu hv
  unfold GammaDeficit.betaReal at hBeta
  rw [hReu,hRev,show s+(t-s) = t by ring] at hBeta
  have hScaled := mul_le_mul_of_nonneg_left hBeta
    (norm_nonneg (Complex.Gamma ((t:ℂ)+(ξ:ℂ)*Complex.I)))
  rw [← hNorm] at hScaled
  have hId : ‖Complex.Gamma ((t:ℂ)+(ξ:ℂ)*Complex.I)‖*
      (Real.Gamma s*Real.Gamma (t-s)/Real.Gamma t) =
      ‖Complex.Gamma ((t:ℂ)+(ξ:ℂ)*Complex.I)‖*Real.Gamma s*Real.Gamma (t-s)/Real.Gamma t := by ring
  rw [hId] at hScaled
  have hPaid := (le_div_iff₀ hGt).mp hScaled
  have hCancel : (‖Complex.Gamma u‖*Real.Gamma t)*Real.Gamma (t-s) ≤
      (‖Complex.Gamma ((t:ℂ)+(ξ:ℂ)*Complex.I)‖*Real.Gamma s)*Real.Gamma (t-s) := by
    nlinarith only [hPaid]
  have h := (mul_le_mul_iff_of_pos_right hGv).mp hCancel
  exact (div_le_div_iff₀ hGs hGt).mpr h

theorem normalizedGammaModulus_mono {s t ξ : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    ‖Complex.Gamma ((s:ℂ)+(ξ:ℂ)*Complex.I)‖/Real.Gamma s ≤
      ‖Complex.Gamma ((t:ℂ)+(ξ:ℂ)*Complex.I)‖/Real.Gamma t := by
  rcases hst.eq_or_lt with h | h
  · subst t
    exact le_rfl
  · exact normalizedGammaModulus_le_of_lt hs h

end ACS12
