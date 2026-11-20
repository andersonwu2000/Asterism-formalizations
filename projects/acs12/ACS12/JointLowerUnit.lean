import ACS12.JointLowerDiagonal
import ACS12.JointLowerUnitNative
import ACS12.JointLowerUnitSource

/-! The unit extension of the complete lower diagonal quotient. -/
namespace ACS12.GammaMeasure

open Set

theorem lowerDiagonalResponse_at_zero {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    lowerDiagonalResponse 0 p 0 = 0 := by
  have hp₂ : p ≤ 2 := hpP.trans (by norm_num)
  rw [lowerDiagonalResponse_zero_eq (L := 1) hp hp₂ zero_lt_one (by norm_num)]
  have hMu := jointCanonicalMu_bounds
  have h := jointPure_unit_zero hp hp₂ (L := 1) zero_lt_one
    (by linarith only [hMu.1]) (by linarith only [hMu.2])
  simpa only [lowerDiagonalMass,mul_zero,sub_zero] using h

theorem lowerDiagonalResponse_first_unit {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    lowerDiagonalResponse 1 p 0 = jointPureUnit 1 0 p := by
  have hp₂ : p ≤ 2 := hpP.trans (by norm_num)
  unfold lowerDiagonalResponse
  change (-(1 + (6 / 25) * p - pureZ p) - 2 * ((6 / 25) * p) * 0 + 3 * ((6 / 25) * p) * (0 : ℝ) ^ 2) +
    lowerNativeStream 1 p 0 +
    (jointPureLambda - jointCanonicalMu) * (lowerDiagonalKnownD1 p 0 + lowerDiagonalRightD1 p 0) +
    jointCanonicalMu * lowerSourcePair 1 p 0 = jointPureUnit 1 0 p
  rw [lowerNativeStream_first_unit hp,lowerAdjacent_first_unit hp hp₂,lowerSourcePair_first_unit hp hp₂]
  unfold jointPureUnit jointUnitValue jointUnitK jointUnitNativeM jointPureD
  rw [pureP_eq]
  ring

theorem lowerDiagonalQuotient_convex {p : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) :
    ConvexOn ℝ (Icc (0 : ℝ) (1 / 8))
      (fun d => if d = 0 then jointPureUnit 1 0 p else lowerDiagonalResponse 0 p d / d) := by
  have hp₂ : p ≤ 2 := hpP.trans (by norm_num)
  rw [← lowerDiagonalResponse_first_unit hp hpP]
  refine quotient_convex_of_third_nonneg (by norm_num) (lowerDiagonalResponse_at_zero hp hpP)
    (fun d hd => lowerDiagonalResponse_deriv (k := 0) (by decide) hp hp₂ hd)
    (fun d hd => lowerDiagonalResponse_deriv (k := 1) (by decide) hp hp₂ hd)
    (fun d hd => lowerDiagonalResponse_deriv (k := 2) (by decide) hp hp₂ hd) ?_
  intro d hd
  apply le_trans _ (lowerDiagonalResponse_third_gt hp hpP hd).le
  have hm : 0 < lowerDiagonalMass d := by unfold lowerDiagonalMass; linarith only [hd.2]
  have hp₀ := zero_lt_one.trans_le hp
  positivity

end ACS12.GammaMeasure
