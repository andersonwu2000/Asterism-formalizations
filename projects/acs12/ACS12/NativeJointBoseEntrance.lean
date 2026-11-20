import ACS12.OrdinaryBetaBoseEntrance
import ACS12.NativeBoseNoiseSine
import ACS12.NativeJointNegativeMoment
import ACS12.NativeJointEntranceScale

/-! The original, absolutely normalized Bose row equals the actual joint-law moment at the ordinary beta entrance. -/
namespace ACS12.NativeCells
open MeasureTheory Set GammaDeficit

theorem boseRow_joint_mellin_entrance {p N : ℝ} (hp : 0 < p) (hp₁ : p < 1) (hN : 0 < N) :
    boseRow p N = (N^2*nativeGammaScale p/(12*sineScale p)) *
      ∫ t : ℝ in Ioi 0, nativeJointNegativeKernel p N t := by
  rw [ordinaryBeta_bose_sine hp hp₁ hN,nativeJointNegativeKernel_integral hp hN]
  have hPoint (v : ℝ) (hv : v ∈ Ioi (0:ℝ)) :
      sinhProfile p v * (∫ s : ℝ in Ioi 0,
          Real.sin (v*s)/(Real.exp ((2*Real.pi/N)*s)-1)) =
        (N^2/24)*((v*sinhProfile p v) *
          ∫ s, Real.exp (-(v^2*N^2)*boseNoise s) ∂boseNoiseMeasure) := by
    have hv₀ : 0 < v := hv
    have h := boseNoise_laplace_eq_fullSine hN hv₀
    rw [show N^2*v^2 = v^2*N^2 by ring] at h
    have hPaid : (∫ s : ℝ in Ioi 0,
        Real.sin (v*s)/(Real.exp ((2*Real.pi/N)*s)-1)) =
        (N^2*v/24)*(∫ s, Real.exp (-(v^2*N^2)*boseNoise s) ∂boseNoiseMeasure) := by
      rw [h]
      have hCoeff : (N^2*v/24)*(24/(N^2*v)) = 1 := by
        field_simp [hN.ne',hv₀.ne']
      rw [← mul_assoc,hCoeff,one_mul]
    rw [hPaid]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hPoint,integral_const_mul]
  field_simp [(sineScale_pos hp hp₁).ne']
  <;> ring

theorem boseRow_joint_ordinary_entrance {p N : ℝ} (hp : 0 < p) (hp₁ : p < 1) (hN : 0 < N) :
    boseRow p N = N^2*nativeJointScale p *
      ∫ s, nativeJointEnergy (N^2) s^((p-2)/2) ∂nativeJointMeasure p := by
  have hMoment := (nativeJoint_negative_moment hp (by linarith : p<2) hN).2
  have hΓ := Real.Gamma_pos_of_pos (by linarith : 0<1-p/2)
  have hIntegral : (∫ t : ℝ in Ioi 0, nativeJointNegativeKernel p N t) =
      Real.Gamma (1-p/2)*(∫ s, nativeJointEnergy (N^2) s^((p-2)/2) ∂nativeJointMeasure p) := by
    rw [hMoment]
    rw [← mul_assoc,mul_inv_cancel₀ hΓ.ne',one_mul]
  rw [boseRow_joint_mellin_entrance hp hp₁ hN,hIntegral]
  have hScale := nativeJoint_entrance_scale hp hp₁
  convert congrArg (fun a : ℝ => N^2*a*
    (∫ s, nativeJointEnergy (N^2) s^((p-2)/2) ∂nativeJointMeasure p)) hScale using 1 <;> ring

end ACS12.NativeCells
