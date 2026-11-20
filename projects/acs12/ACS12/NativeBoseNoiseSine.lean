import ACS12.NativeJointLaplace
import ACS12.FullBoseSine

/-! The fixed Bose noise is exactly the full original sine/Bose transform, without discarding any mode. -/
namespace ACS12.NativeCells
open MeasureTheory Set GammaMeasure

theorem boseNoise_laplace_eq_fullSine {N v : ℝ} (hN : 0 < N) (hv : 0 < v) :
    (∫ s, Real.exp (-(N^2*v^2)*boseNoise s) ∂boseNoiseMeasure) =
      (24/(N^2*v)) * ∫ s : ℝ in Ioi 0,
        Real.sin (v*s)/(Real.exp ((2*Real.pi/N)*s)-1) := by
  rw [boseNoise_laplace (by positivity : 0 ≤ N^2*v^2)]
  have hS := fullBoseSine_hasSum (d := 2*Real.pi/N) (by positivity) v
  have hZ : powerTail 2 1 = Real.pi^2/6 := by
    simpa only [pureZ,one_mul,show (1:ℝ)+1=2 by norm_num] using pureZ_one_eq
  have hTerm (k : ℕ) :
      nativeZetaWeight 2 k/(1+(N^2*v^2)/GammaMixture.gammaRate k) =
        (24/(N^2*v)) * (v/(((2*Real.pi/N)*((k:ℝ)+1))^2+v^2)) := by
    unfold nativeZetaWeight GammaMixture.gammaRate
    rw [hZ,Real.rpow_neg (by positivity),Real.rpow_two]
    have hK : 0 < 1+(k:ℝ) := by positivity
    have hD : 0 < ((2*Real.pi/N)*((k:ℝ)+1))^2+v^2 := by positivity
    field_simp [hN.ne',hv.ne',Real.pi_ne_zero,hK.ne',
      show (k:ℝ)+1 ≠ 0 by positivity,hD.ne']
    <;> ring
  simp_rw [hTerm]
  rw [tsum_mul_left,hS.tsum_eq]

end ACS12.NativeCells
