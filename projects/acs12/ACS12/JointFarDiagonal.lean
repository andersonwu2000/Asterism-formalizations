import ACS12.JointFarNativeLicense
import ACS12.JointFarFourthLicense
import ACS12.JointFarAdjacentLicense

/-! The complete finite value at the far zero-gap point. -/
namespace ACS12.GammaMeasure

open Set CenteredCircle.AllN

theorem jointPure_farDiagonal_le {p L : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) (hL : 0 < L) :
    jointPureValue p L (7 / 8) (3 / 4) (3 / 4) jointCanonicalMu ≤
      jointFarNative p + jointPureLambda * jointFarAdjacent p + jointCanonicalMu * jointFarFourth p := by
  let u : ℝ := 7 / 8
  let m : ℝ := 3 / 4
  have hu : 0 < u := by norm_num [u]
  have hm : 0 < m := by norm_num [m]
  have hp₂ : p ≤ 2 := hpP.trans (by norm_num)
  have h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl,zero_le_one⟩
  have hA := lawRight_abs_samples_summable (u := u) (t := 1 / 8) (q := m)
    hp hp₂ hL h0 (by norm_num) hm
  have hS : Summable (fun j : ℕ => pureRight p u (u + (j : ℝ) * m)) := by
    apply Summable.of_norm
    apply hA.congr
    intro j
    simp only [Nat.cast_succ,Real.norm_eq_abs]
    rw [show (1 / 8 : ℝ) + ((j : ℝ) + 1) * m = u + (j : ℝ) * m by norm_num [u,m]; ring]
    rw [lawRightTest_zero hp hp₂ hL (by positivity)]
  have hT : samplingTail (lawRightTest p L 0 u) u m = samplingTail (pureRight p u) u m := by
    unfold samplingTail
    congr 1
    apply tsum_congr
    intro j
    exact lawRightTest_zero hp hp₂ hL (by positivity)
  have hN : adjacentLawSignedValue p L 0 u m ≤ jointFarNative p := by
    rw [adjacentLawSignedValue,middleLawBase_zero hp hp₂ hL,lawRightTest_zero hp hp₂ hL hu,hT,
      add_assoc,← samplingHead_split _ _ _ hS]
    have h := jointFarNative_full_upper hp hpP
    unfold u m
    rw [show middleA (7 / 8) = 189 / 800 by norm_num [middleA]]
    exact h.le
  have hQ := jointFarAdjacent_full_upper hp hpP hL
  have hH := jointFarFourth_full_upper hp hpP hL
  have hMu : 0 ≤ jointCanonicalMu := by linarith only [jointCanonicalMu_bounds.1]
  change adjacentDiagonal p L 0 u m ≤ _ at hQ
  change fourthSourceRow p L 0 u m m m ≤ _ at hH
  change jointPureValue p L u m m jointCanonicalMu ≤ _
  unfold jointPureValue
  exact add_le_add (add_le_add hN (mul_le_mul_of_nonneg_left hQ (by norm_num [jointPureLambda])))
    (mul_le_mul_of_nonneg_left hH hMu)

end ACS12.GammaMeasure
