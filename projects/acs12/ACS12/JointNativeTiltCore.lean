import ACS12.JointPowerContinuity
import Mathlib.MeasureTheory.Measure.Tilted

/-! The count tilt and bounded fraction of the same actual joint law. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter

noncomputable def jointNativeTiltWeight (p z : ℝ) (s : NativeJointSample) : ℝ :=
  ((p-2)/2)*Real.log (nativeJointEnergy z s)
noncomputable def jointNativeTilt (p z : ℝ) : Measure NativeJointSample :=
  (nativeJointMeasure p).tilted (jointNativeTiltWeight p z)
noncomputable def jointNativeVariable (z : ℝ) (s : NativeJointSample) : ℝ :=
  z*boseNoise s.2/nativeJointEnergy z s
noncomputable def jointNativeMean (p z : ℝ) : ℝ :=
  ∫ s, jointNativeVariable z s ∂jointNativeTilt p z

theorem jointPowerRow_pos {p q z : ℝ} (hp : 0 < p) (hz : 0 ≤ z) :
    0 < jointPowerRow p q z := by
  letI := nativeJoint_probability hp
  have hEq : (fun s => nativeJointEnergy z s^q) =ᵐ[nativeJointMeasure p]
      (fun s => Real.exp (q*Real.log (nativeJointEnergy z s))) := by
    filter_upwards [nativeJointEnergy_ae_pos hp hz] with s hs
    rw [Real.rpow_def_of_pos hs,mul_comm]
  have hPos := integral_exp_pos ((nativeJoint_all_real_moments (q:=q) hp hz).congr hEq)
  rw [←integral_congr_ae hEq] at hPos
  exact hPos

theorem measurable_jointNativeVariable (z : ℝ) : Measurable (jointNativeVariable z) :=
  ((measurable_boseNoise.comp measurable_snd).const_mul z).div (measurable_nativeJointEnergy z)

theorem jointNativeTilt_exp_eq {p z : ℝ} (hp : 0 < p) (hz : 0 ≤ z) :
    (fun s => Real.exp (jointNativeTiltWeight p z s)) =ᵐ[nativeJointMeasure p]
      (fun s => nativeJointEnergy z s^((p-2)/2)) := by
  filter_upwards [nativeJointEnergy_ae_pos hp hz] with s hs
  rw [jointNativeTiltWeight,Real.rpow_def_of_pos hs,mul_comm]

theorem jointNativeTilt_probability {p z : ℝ} (hp : 0 < p) (hz : 0 ≤ z) :
    IsProbabilityMeasure (jointNativeTilt p z) := by
  letI := nativeJoint_probability hp
  exact isProbabilityMeasure_tilted ((nativeJoint_all_real_moments hp hz).congr
    (jointNativeTilt_exp_eq hp hz).symm)

theorem jointNativeTilt_coordinates_ae_pos {p z : ℝ} (hp : 0 < p) :
    ∀ᵐ s ∂jointNativeTilt p z, 0 < GammaMixture.gammaTotal s.1 ∧ 0 < boseNoise s.2 :=
  (tilted_absolutelyContinuous _ _).ae_le (nativeJoint_coordinates_ae_pos hp)

theorem jointNativeVariable_ae_mem {p z : ℝ} (hp : 0 < p) (hz : 0 < z) :
    ∀ᵐ s ∂jointNativeTilt p z, jointNativeVariable z s ∈ Ioo (0:ℝ) 1 := by
  filter_upwards [jointNativeTilt_coordinates_ae_pos (z:=z) hp] with s hs
  have hY : 0 < nativeJointEnergy z s :=
    add_pos_of_pos_of_nonneg hs.1 (mul_nonneg hz.le hs.2.le)
  constructor
  · exact div_pos (mul_pos hz hs.2) hY
  · apply (div_lt_one hY).mpr
    unfold nativeJointEnergy
    linarith only [hs.1]

end ACS12.NativeCells
