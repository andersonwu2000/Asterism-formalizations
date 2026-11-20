import ACS12.NativeJointMellinKernel
import ACS12.NegativeMomentMellin
import ACS12.PositiveSquareSubstitution

/-! The actual joint law has its finite ordinary negative moment at the beta entrance. -/
namespace ACS12.NativeCells
open MeasureTheory Set Filter GammaDeficit

theorem nativeJoint_negative_moment {p N : ℝ} (hp : 0 < p) (hp₂ : p < 2) (hN : 0 < N) :
    Integrable (fun s => nativeJointEnergy (N^2) s^((p-2)/2)) (nativeJointMeasure p) ∧
      (∫ s, nativeJointEnergy (N^2) s^((p-2)/2) ∂nativeJointMeasure p) =
        (Real.Gamma (1-p/2))⁻¹ * ∫ t : ℝ in Ioi 0, nativeJointNegativeKernel p N t := by
  letI := nativeJoint_probability hp
  have hR : 0 < 1-p/2 := by linarith only [hp₂]
  have hExp : 1-p/2-1 = -p/2 := by ring
  have hPow : -(1-p/2) = (p-2)/2 := by ring
  have hK : IntegrableOn
      (fun t => t^(1-p/2-1)*(∫ s, Real.exp (-t*nativeJointEnergy (N^2) s) ∂nativeJointMeasure p))
      (Ioi 0) := by
    simpa only [hExp,nativeJointNegativeKernel,nativeJointLaplaceValue] using
      nativeJointNegativeKernel_integrable hp hp₂ hN
  have h := negativeMoment_eq_laplace (measurable_nativeJointEnergy (N^2))
    (nativeJointEnergy_ae_pos hp (sq_nonneg N)) hR hK
  simpa only [hPow,hExp,nativeJointNegativeKernel,nativeJointLaplaceValue] using h

theorem nativeJointNegativeKernel_integral {p N : ℝ} (hp : 0 < p) (hN : 0 < N) :
    (∫ t : ℝ in Ioi 0, nativeJointNegativeKernel p N t) =
      2 * ∫ v : ℝ in Ioi 0, (v*sinhProfile p v) *
        ∫ s, Real.exp (-(v^2*N^2)*boseNoise s) ∂boseNoiseMeasure := by
  rw [integral_positiveSquare,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  have hv₀ : 0 < v := hv
  dsimp only
  have h := jointNegativeKernel_square hp hN hv₀
  rw [abs_of_pos (mul_pos zero_lt_two hv₀)] at h
  simpa only [mul_assoc] using h

end ACS12.NativeCells
