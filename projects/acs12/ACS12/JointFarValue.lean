import ACS12.JointFarEnvelopes

/-! The zero-gap far value and its two strict endpoint prices. -/
namespace ACS12.GammaMeasure

open Set MeasureTheory
open GammaDeficit (lineDensity)

noncomputable def jointFarValue (p : ℝ) : ℝ :=
  jointFarNative p + jointPureLambda * jointFarAdjacent p + jointCanonicalMu * jointFarFourth p +
    jointClipPrice p / 8 +
      (1 / 10) * (3 / 4 : ℝ) ^ (-p) * max 0 (jointPureMismatch p)

theorem jointPureMismatch_one_upper : max 0 (jointPureMismatch 1) ≤ 8606 / 1000000 := by
  have hQ : pureQ 1 < 24042 / 10000 := by
    unfold pureQ
    norm_num
    linarith only [powerTail_three_bounds.2]
  have hQ₀ : 0 ≤ pureQ 1 := by linarith only [powerTail_three_bounds.1,show pureQ 1 = 2 * powerTail 3 1 by norm_num [pureQ]]
  have hP : pureP 1 = 0 := by norm_num [pureP]
  have hM := mul_le_mul jointCanonicalMu_bounds.2.le hQ.le hQ₀ (by norm_num : (0 : ℝ) ≤ 17765 / 1000000)
  unfold jointPureMismatch jointPureD jointPureB
  rw [hP]
  apply max_le (by norm_num)
  norm_num [jointPureLambda] at ⊢
  linarith only [hM,hQ]

theorem jointFarValue_endpoint_lt : jointFarValue (9 / 5) < -(52 / 100000 : ℝ) := by
  have hAdj := mul_le_mul_of_nonneg_left jointFarAdjacent_endpoint_lt.le
    (by norm_num [jointPureLambda] : 0 ≤ jointPureLambda)
  have hH := jointFarFourth_endpoint_lt
  obtain ⟨hμ,hμ'⟩ := jointCanonicalMu_bounds
  have hFourth := (mul_le_mul_of_nonneg_left hH.le (by linarith only [hμ] : 0 ≤ jointCanonicalMu)).trans
    (mul_le_mul_of_nonpos_right hμ.le (by norm_num : -(4438 / 10000 : ℝ) ≤ 0))
  have hClip := jointClipPrice_endpoint_lt
  unfold jointFarValue
  rw [jointPureMismatch_endpoint,max_self,mul_zero,add_zero]
  norm_num [jointPureLambda] at hAdj ⊢
  linarith only [jointFarNative_endpoint_lt,hAdj,hFourth,hClip]

theorem jointFarValue_one_lt : jointFarValue 1 < -(54 / 1000 : ℝ) := by
  have hAdj := mul_le_mul_of_nonneg_left jointFarAdjacent_one_lt.le
    (by norm_num [jointPureLambda] : 0 ≤ jointPureLambda)
  have hH := jointFarFourth_one_lt
  obtain ⟨hμ,hμ'⟩ := jointCanonicalMu_bounds
  have hFourth := (mul_le_mul_of_nonneg_left hH.le (by linarith only [hμ] : 0 ≤ jointCanonicalMu)).trans
    (mul_le_mul_of_nonpos_right hμ.le (by norm_num : -(13 / 100 : ℝ) ≤ 0))
  unfold jointFarValue
  rw [jointClipPrice_one,Real.rpow_neg_one]
  norm_num [jointPureLambda] at hAdj ⊢
  linarith only [jointFarNative_one_lt,hAdj,hFourth,jointPureMismatch_one_upper]

end ACS12.GammaMeasure
