import ACS12.JointFixedDualReturn
import ACS12.JointConeValue
import ACS12.OuterJointHead
import ACS12.JointActualCone
import ACS12.OuterReturn
import ACS12.AdjacentReturn
import ACS12.JointFeasibleSource
import ACS12.JointOuterFeasible

/-! The complete clipped receiver at source-feasible comparison points. -/

namespace ACS12.GammaMeasure

open Set MeasureTheory CenteredCircle.AllN

theorem feasible_joint_receiver_neg {p L u m : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (huL : 7 / 8 ≤ u) (hu₁ : u < 1) (hm : m ∈ Ioo (u / 2) u)
    (hmL : 2 * u - 1 ≤ m) (hFeasible : 0 ≤ diagonalAdjacent p L 1 u m) (hG : 0 ≤ lawRightTest p L 1 u u) :
    adjacentLawValue p L 1 u m < 0 := by
  let r := fourthComparisonRoot p L 1 u m m
  have hp₂ : p < 2 := hP.trans_lt (by norm_num)
  have hu : 0 < u := by linarith only [huL]
  have hm₀ : 0 < m := (half_pos hu).trans hm.1
  have h0 : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  obtain ⟨⟨hr,hrm⟩,hH,_⟩ := fourthComparisonRoot_spec hp hp₂ hL h1 hm₀ hm.2.le hu₁ hm₀.le le_rfl
  have hGap := fourthComparisonRoot_high_bracket hp hP hL h1 hm₀ hm.2.le hu₁ hmL
  have hReturn := jointAugmentedValue_actual_lt hp hP hL huL hu₁ hmL hm.2.le hr hrm.le hGap.le
  rw [jointAugmentedValue_zero] at hReturn
  have hPay : 0 ≤ ((1 - u) / 30) *
      ∫ s : ℝ in Ioi 0, GammaDeficit.signedDensity p L s * (1 - Real.exp (-s)) := by
    apply mul_nonneg (div_nonneg (sub_nonneg.mpr hu₁.le) (by norm_num))
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (signedDensity_pos hp hp₂ hL hs).le (expHead_den_pos hs).le
  have hCone := (feasible_joint_cone hp hP hL h1 huL hu₁ hm hFeasible).2
  change m - r < (25 / 28) * (u - m) at hCone
  have hGapCone : m - r ≤ (9 / 10) * (u - m) := by linarith only [hCone,hm.2]
  have hPure := jointPure_cone_value_neg (r := r) hp hP hL huL hu₁
    ⟨hmL,hm.2.le⟩ (sub_nonneg.mpr hrm.le) hGapCone
  have hClip := lawRightNegative_tail_antitone (u := u) hp hp₂ hL h0 h1 zero_le_one hu.le hm₀
  have hValue := adjacentLawValue_eq hp hp₂.le hL h1 hu hm₀
  rw [show lawRightClip p L 1 u u = lawRightTest p L 1 u u from max_eq_right hG,
    sub_self,mul_zero,add_zero] at hValue
  change 0 ≤ adjacentSourceLaw p L 1 u m m r at hFeasible
  change fourthSourceRow p L 1 u m r m = 0 at hH
  unfold jointAugmentedValue at hReturn
  rw [hH,mul_zero,add_zero] at hReturn
  have hSource : 0 ≤ jointPureLambda * adjacentSourceLaw p L 1 u m m r :=
    mul_nonneg (by unfold jointPureLambda; positivity) hFeasible
  linarith only [hPure,hReturn,hClip,hValue,hPay,hSource]

theorem _root_.ACS12.Configuration.inner_actual_high_impossible {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hn : 2 ≤ n) (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k)
    (huL : 7 / 8 ≤ C.source.forwardDistance C.source.neighbor j)
    (hu₁ : C.source.forwardDistance C.source.neighbor j < 1)
    (hInner : C.source.forwardDistance j k ≤ C.source.forwardDistance C.source.neighbor j) : False := by
  let u := C.source.forwardDistance C.source.neighbor j
  let L := C.source.period
  have hp₀ := zero_lt_one.trans_le hp
  have hp₂ : p < 2 := hP.trans_lt (by norm_num)
  have hu : 0 < u := C.source.forwardDistance_pos _ _
  have hG : 0 ≤ lawRightTest p L 1 u u := by
    rw [lawRightTest_one hp₀ C.source.period_pos hu]
    exact (F.rightTest_active hn hp₀ hp₂.le C hj hk hu₁.le).le
  obtain ⟨m,hm,hmL,hFeasible,hPos⟩ := F.inner_feasible_necessary hn hp hP C hj hk huL hu₁ hInner
  have hNeg := feasible_joint_receiver_neg hp hP C.source.period_pos huL hu₁ hm hmL hFeasible hG
  rw [adjacentLawValue_one hp₀ C.source.period_pos hu ((half_pos hu).trans hm.1)] at hNeg
  exact hNeg.not_ge hPos

theorem _root_.ACS12.Configuration.outer_actual_high_impossible {n : ℕ} {p : ℝ}
    (F : Configuration n p) (hn : 2 ≤ n) (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) {j k : Fin n}
    (hj : C.source.IsNext C.source.neighbor j) (hk : C.source.IsNext j k)
    (huL : 7 / 8 ≤ C.source.forwardDistance C.source.neighbor j)
    (hu₁ : C.source.forwardDistance C.source.neighbor j < 1)
    (hOuter : C.source.forwardDistance C.source.neighbor j ≤ C.source.forwardDistance j k) : False := by
  let u := C.source.forwardDistance C.source.neighbor j
  let L := C.source.period
  have hL : 0 < L := C.source.period_pos
  have hp₀ := zero_lt_one.trans_le hp
  have hp₂ := hP.trans_lt (by norm_num : (9 / 5 : ℝ) < 2)
  have hu : 0 < u := C.source.forwardDistance_pos _ _
  have h1 : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hG : 0 < lawRightTest p L 1 u u := by
    rw [lawRightTest_one hp₀ hL hu]
    exact F.rightTest_active hn hp₀ hp₂.le C hj hk hu₁.le
  let m := outerLawMass p L 1 u
  obtain ⟨hm,hmL,hFeasible⟩ := outerMass_feasible hp hP hL h1 huL hu₁
  have hm₀ := (half_pos hu).trans hm.1
  have hNeg := feasible_joint_receiver_neg hp hP hL huL hu₁ hm hmL hFeasible hG.le
  have hOrig : 0 ≤ outerLawValue p L 1 u := by
    rw [outerLawValue_one hp hp₂.le hL hu]
    exact F.outer_scalar_necessary hn hp₀ hp₂.le C hj hk hu₁.le hOuter
  have hQ := lawRightClip_quadratureData (u := u) hp hp₂.le hL h1 hu
  have hT := hQ.tail_anti u le_rfl hm₀ hu hm.2.le
  have hK : lawRightClip p L 1 u u = lawRightTest p L 1 u u := max_eq_right hG.le
  have hCompare : outerLawValue p L 1 u ≤ adjacentLawValue p L 1 u m := by
    rw [outerLawValue_clipped hp hp₂.le hL h1 hu,adjacentLawValue,
      samplingHead_split _ _ _ (hQ.summable u m le_rfl hm₀),hK]
    change middleLawBase p L 1 u + outerLawMass p L 1 u * lawRightTest p L 1 u u +
      samplingTail (lawRightClip p L 1 u) u u ≤
        middleLawBase p L 1 u + (m * lawRightTest p L 1 u u + samplingTail (lawRightClip p L 1 u) u m)
    dsimp only [m]
    linarith only [hT]
  exact hNeg.not_ge (hOrig.trans hCompare)

end ACS12.GammaMeasure
