import ACS12.JointReturnSign
import ACS12.JointPureUpperDiagonal
import ACS12.JointCanonicalMoments

/-! Returning the augmented value at fixed geometry, with both source rows. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN MeasureTheory Set Filter
open GammaDeficit (signedDensity)

noncomputable def jointAugmentedValue (p L θ u m r : ℝ) : ℝ :=
  adjacentLawSignedValue p L θ u m +
    jointPureLambda * adjacentSourceLaw p L θ u m m r +
    jointCanonicalMu * fourthSourceRow p L θ u m r m

theorem jointAugmentedValue_zero (p L u m r : ℝ) :
    jointAugmentedValue p L 0 u m r = jointPureValue p L u m r jointCanonicalMu := rfl

theorem jointAugmentedValue_actual_lt {p L u m r : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (huL : 7 / 8 ≤ u) (hu₁ : u < 1)
    (hmL : 2 * u - 1 ≤ m) (hmu : m ≤ u) (hr : 0 < r) (hrm : r ≤ m)
    (hGap : m - r ≤ (4 / 5) * (1 - u)) :
    jointAugmentedValue p L 1 u m r < jointAugmentedValue p L 0 u m r -
      ((1 - u) / 30) * ∫ s : ℝ in Ioi 0, signedDensity p L s * (1 - Real.exp (-s)) := by
  have hp₂ : p < 2 := hP.trans_lt (by norm_num)
  have hm := hr.trans_le hrm
  have hu := hm.trans_le hmu
  have h0 : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  let e := signedDensity p L
  let R := adjacentNativeResponse u m
  let Q := jointSourceResponse u m r
  let H := fourthSourceResponse u m r
  obtain ⟨hIR,hRE⟩ := adjacentSignedValue_law_difference hp hp₂ hL h0 h1 hu hm
  obtain ⟨hIQ,hQE⟩ := jointAdjacent_law_difference hp hp₂ hL h0 h1 hu hm hr
  obtain ⟨hIH,hHE⟩ := fourthSource_law_difference hp hp₂ hL h0 h1 hu hm hr
  change IntegrableOn (fun s => e s * R s) (Ioi 0) at hIR
  change IntegrableOn (fun s => e s * Q s) (Ioi 0) at hIQ
  change IntegrableOn (fun s => e s * H s) (Ioi 0) at hIH
  let A (s : ℝ) := e s * R s
  let B (s : ℝ) := jointPureLambda * (e s * Q s)
  let C (s : ℝ) := jointCanonicalMu * (e s * H s)
  let Z (s : ℝ) := e s * (1 - Real.exp (-s))
  let μ := volume.restrict (Ioi (0 : ℝ))
  letI : NeZero μ := ⟨positiveHalfLine_ne_zero⟩
  have hI : Integrable (fun s => A s - B s - C s) μ :=
    (hIR.sub (hIQ.const_mul jointPureLambda)).sub (hIH.const_mul jointCanonicalMu)
  have hZI : Integrable Z μ := by
    obtain ⟨he,_⟩ := signedDensity_total hp hp₂ hL
    apply he.mono' (he.aestronglyMeasurable.mul (by fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have he := signedDensity_pos hp hp₂ hL hs
    have hE : 0 ≤ 1 - Real.exp (-s) := (expHead_den_pos hs).le
    change ‖e s * (1 - Real.exp (-s))‖ ≤ e s
    rw [Real.norm_of_nonneg (mul_nonneg he.le hE)]
    exact mul_le_of_le_one_right he.le (by linarith only [(Real.exp_pos (-s)).le])
  have hM : jointCanonicalMu ≤ 3553 / 200000 := by linarith only [jointCanonicalMu_bounds.2]
  have hPos : ((1 - u) / 30) * (∫ s : ℝ in Ioi 0, Z s) < ∫ s : ℝ in Ioi 0, A s - B s - C s := by
    rw [← integral_const_mul]
    apply integral_strict_of_ae_lt μ (hZI.const_mul _) hI
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hF := fixedDual_density_gt huL hu₁ hmL hmu hr hrm hGap hs hM
    have hE := mul_lt_mul_of_pos_left hF (signedDensity_pos hp hp₂ hL hs)
    dsimp only [A,B,C,Z,e,R,Q,H]
    unfold jointPureLambda
    linarith only [hE]
  change _ < ∫ s : ℝ in Ioi 0, (A - B) s - C s at hPos
  rw [integral_sub (hIR.sub (hIQ.const_mul jointPureLambda)) (hIH.const_mul jointCanonicalMu)] at hPos
  change _ < (∫ s : ℝ in Ioi 0, A s - B s) - ∫ s : ℝ in Ioi 0, C s at hPos
  rw [integral_sub hIR (hIQ.const_mul jointPureLambda)] at hPos
  change _ < (∫ s : ℝ in Ioi 0, e s * R s) -
    (∫ s : ℝ in Ioi 0, jointPureLambda * (e s * Q s)) -
      ∫ s : ℝ in Ioi 0, jointCanonicalMu * (e s * H s) at hPos
  rw [integral_const_mul,integral_const_mul] at hPos
  simp only [sub_zero,one_mul,neg_mul] at hRE hQE hHE
  unfold jointAugmentedValue
  dsimp only [Z,e] at hPos
  linarith only [hPos,hRE,congrArg (jointPureLambda * ·) hQE,congrArg (jointCanonicalMu * ·) hHE]

end ACS12.GammaMeasure
