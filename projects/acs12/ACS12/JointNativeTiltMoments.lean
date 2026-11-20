import ACS12.JointNativeTiltRatio
import ACS12.JointWeightedPowerCalculus

/-! Every bounded tilt moment is the same actual joint weighted moment, without size bias or a second law. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter
set_option backward.isDefEq.respectTransparency false

noncomputable def jointNativeMoment (p z : ℝ) (j : ℕ) : ℝ :=
  ∫ s, (jointNativeVariable z s)^j ∂jointNativeTilt p z

theorem jointNativeMoment_integrable {p z : ℝ} (hp : 0 < p) (hz : 0 < z) (j : ℕ) :
    Integrable (fun s => (jointNativeVariable z s)^j) (jointNativeTilt p z) := by
  letI := jointNativeTilt_probability hp hz.le
  apply (integrable_const (μ:=jointNativeTilt p z) (1:ℝ)).mono'
    ((measurable_jointNativeVariable z).pow_const j).aestronglyMeasurable
  filter_upwards [jointNativeVariable_ae_mem hp hz] with s hs
  rw [Real.norm_of_nonneg (pow_nonneg hs.1.le j)]
  exact pow_le_one₀ hs.1.le hs.2.le

theorem jointNativeMoment_weighted {p z : ℝ} (hp : 0 < p) (hz : 0 < z) (j : ℕ) :
    jointNativeMoment p z j =
      z^j*jointWeightedPowerRow p ((p-2)/2) j z/jointPowerRow p ((p-2)/2) z := by
  let μ := nativeJointMeasure p
  let β := (p-2)/2
  let Y := jointNativeVariable z
  have hDen : (∫ s, Real.exp (jointNativeTiltWeight p z s) ∂μ) = jointPowerRow p β z :=
    integral_congr_ae (jointNativeTilt_exp_eq hp hz.le)
  have hNum : (fun s => Real.exp (jointNativeTiltWeight p z s)*(Y s)^j) =ᵐ[μ]
      (fun s => z^j*jointWeightedPower β j z s) := by
    filter_upwards [nativeJoint_coordinates_ae_pos hp,jointNativeTilt_exp_eq hp hz.le] with s hs hE
    have hEnergy : 0 < nativeJointEnergy z s :=
      add_pos_of_pos_of_nonneg hs.1 (mul_nonneg hz.le hs.2.le)
    rw [hE,jointWeightedPower_ratio j s hEnergy]
    unfold Y jointNativeVariable
    rw [div_pow,mul_pow,div_pow]
    ring
  unfold jointNativeMoment jointNativeTilt
  rw [integral_tilted,hDen]
  simp_rw [smul_eq_mul,div_mul_eq_mul_div]
  rw [integral_div,integral_congr_ae hNum,integral_const_mul]
  rfl

theorem jointNativeMean_weighted {p z : ℝ} (hp : 0 < p) (hz : 0 < z) :
    jointNativeMean p z =
      z*jointWeightedPowerRow p ((p-2)/2) 1 z/jointPowerRow p ((p-2)/2) z := by
  simpa only [jointNativeMoment,pow_one,jointNativeMean] using jointNativeMoment_weighted hp hz 1

theorem jointNativeMean_bounds {p z : ℝ} (hp : 0 < p) (hz : 0 < z) :
    0 ≤ jointNativeMean p z ∧ jointNativeMean p z ≤ 1 := by
  letI := jointNativeTilt_probability hp hz.le
  have hY := jointNativeVariable_ae_mem hp hz
  have hI : Integrable (jointNativeVariable z) (jointNativeTilt p z) := by
    simpa only [pow_one] using jointNativeMoment_integrable hp hz 1
  constructor
  · exact integral_nonneg_of_ae (hY.mono fun s hs => hs.1.le)
  · have h := integral_mono_ae hI (integrable_const (1:ℝ)) (hY.mono fun s hs => hs.2.le)
    simpa only [integral_const,probReal_univ,one_smul] using h

theorem jointNative_second_moment_le_mean {p z : ℝ} (hp : 0 < p) (hz : 0 < z) :
    jointNativeMoment p z 2 ≤ jointNativeMean p z := by
  have hI : Integrable (jointNativeVariable z) (jointNativeTilt p z) := by
    simpa only [pow_one] using jointNativeMoment_integrable hp hz 1
  exact integral_mono_ae (jointNativeMoment_integrable hp hz 2) hI
    ((jointNativeVariable_ae_mem hp hz).mono fun s hs => by
      nlinarith [mul_nonneg hs.1.le (sub_nonneg.mpr hs.2.le)])

end ACS12.NativeCells
