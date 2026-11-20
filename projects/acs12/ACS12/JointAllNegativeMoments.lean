import ACS12.MellinFarIntegrability
import ACS12.NegativeMomentMellin

/-! The full explicit Laplace tail pays every negative joint moment, including the compact zero end. -/
namespace ACS12.NativeCells
open Set MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false

theorem joint_negative_kernel_integrable {p z r : ℝ} (hp : 0 < p) (hz : 0 ≤ z) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t^(r-1)*nativeJointLaplaceValue p z t) (Ioi 0) := by
  let K (t : ℝ) := (t:ℂ)^((r:ℂ)-1)*jointLaplaceCarrier (p:ℂ) z (t:ℂ)
  have hM : Measurable K := by
    apply Measurable.mul (by fun_prop)
    exact measurable_jointLaplaceCarrier _ _
  have hNear : IntegrableOn K (Ioo 0 1) := by
    have hR : IntegrableOn (fun t : ℝ => t^(r-1)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith only [hr])
    apply hR.mono' hM.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    dsimp only [K]
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.one_re]
    have hC : ‖jointLaplaceCarrier (p:ℂ) z (t:ℂ)‖ ≤ 1 := by
      exact (jointLaplaceCarrier_norm_le hz ht.1).trans
        (Real.rpow_le_one (mellinPhi_pos ht.1).le (mellinPhi_le_one ht.1) hp.le)
    exact mul_le_of_le_one_right (Real.rpow_nonneg ht.1.le _) hC
  have hFar : IntegrableOn K (Ioi 1) := by
    have h := mellinFar_integrable (α:=(p:ℂ)) (h:=(-r:ℂ)) hp hz
    have he : -(-r:ℂ)-1 = (r:ℂ)-1 := by ring
    simpa only [he] using h
  have hKC : IntegrableOn K (Ioi 0) := by
    rw [←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1),integrableOn_union]
    exact ⟨(integrableOn_Ioc_iff_integrableOn_Ioo (μ:=volume)).mpr hNear,hFar⟩
  have hPoint (t : ℝ) (ht : 0 < t) : K t = (t^(r-1)*nativeJointLaplaceValue p z t:ℝ) := by
    dsimp only [K]
    rw [jointLaplaceCarrier_real hp hz ht,
      show (r:ℂ)-1 = ((r-1:ℝ):ℂ) by push_cast; rfl,
      ←Complex.ofReal_cpow ht.le,←Complex.ofReal_mul]
  have hRe := hKC.re
  apply hRe.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (K t).re = _
  rw [hPoint t ht,Complex.ofReal_re]

theorem nativeJoint_all_negative_moments {p z r : ℝ} (hp : 0 < p) (hz : 0 ≤ z) (hr : 0 < r) :
    Integrable (fun s => nativeJointEnergy z s^(-r)) (nativeJointMeasure p) ∧
      (∫ s, nativeJointEnergy z s^(-r) ∂nativeJointMeasure p) =
        (Real.Gamma r)⁻¹*∫ t : ℝ in Ioi 0, t^(r-1)*nativeJointLaplaceValue p z t := by
  letI := nativeJoint_probability hp
  exact ACS12.negativeMoment_eq_laplace (measurable_nativeJointEnergy z)
    (nativeJointEnergy_ae_pos hp hz) hr (joint_negative_kernel_integrable hp hz hr)

end ACS12.NativeCells
