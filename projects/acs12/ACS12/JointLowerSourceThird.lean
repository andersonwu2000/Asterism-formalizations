import ACS12.JointLowerLeftThird

/-! The complete positive third response of the original sum of the two source rows. -/
namespace ACS12.GammaMeasure

open Set

private noncomputable def lowerMassResponse (k : ℕ) (p δ : ℝ) : ℝ :=
  let m := lowerDiagonalMass δ
  match k with
  | 0 => m ^ (1 - p)
  | 1 => 2 * (p - 1) * m ^ (-p)
  | 2 => 4 * p * (p - 1) * m ^ (-p - 1)
  | _ => 8 * (p - 1) * (p * (p + 1) * m ^ (-p - 2))

private theorem lowerMassResponse_deriv {k : ℕ} (hk : k < 3) {p δ : ℝ} (hD : δ ≤ 1 / 8) :
    HasDerivAt (lowerMassResponse k p) (lowerMassResponse (k + 1) p δ) δ := by
  have hm : 0 < lowerDiagonalMass δ := by unfold lowerDiagonalMass; linarith only [hD]
  have hM : HasDerivAt lowerDiagonalMass (-2) δ := by
    simpa only [lowerDiagonalMass,id_eq,mul_one] using ((hasDerivAt_id δ).const_mul 2).const_sub 1
  have hP (r : ℝ) := hM.rpow_const (p := r) (Or.inl hm.ne')
  interval_cases k
  · convert hP (1 - p) using 1
    simp only [lowerMassResponse,show 1 - p - 1 = -p by ring]
    ring
  · convert (hP (-p)).const_mul (2 * (p - 1)) using 1
    simp only [lowerMassResponse]
    ring
  · convert (hP (-p - 1)).const_mul (4 * p * (p - 1)) using 1
    simp only [lowerMassResponse,show -p - 1 - 1 = -p - 2 by ring]
    ring

noncomputable def lowerSourcePair (k : ℕ) (p δ : ℝ) : ℝ :=
  let right := match k with
    | 0 => lowerDiagonalRight p δ
    | 1 => lowerDiagonalRightD1 p δ
    | 2 => lowerDiagonalRightD2 p δ
    | _ => p * (p + 1) * lowerDiagonalMass δ ^ (-p - 2) *
      lowerRightResponseTotal p (lowerDiagonalRatio δ)
  lowerLeftCombined k p δ + right - (pureZ p - 1) * lowerMassResponse k p δ

theorem lowerSourcePair_deriv {k : ℕ} (hk : k < 3) {p δ : ℝ}
    (hp : 1 ≤ p) (hP : p ≤ 2) (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    HasDerivAt (lowerSourcePair k p) (lowerSourcePair (k + 1) p δ) δ := by
  have hB : δ ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) := ⟨by linarith only [hδ],by linarith only [hD]⟩
  have h := lowerLeftCombined_deriv hk hp hP hB
  have hM := (lowerMassResponse_deriv hk (p := p) hD).const_mul (pureZ p - 1)
  interval_cases k
  · exact (h.add (lowerDiagonalRight_deriv1 hp hP hδ hD)).sub hM
  · exact (h.add (lowerDiagonalRight_deriv2 hp hP hδ hD)).sub hM
  · exact (h.add (lowerDiagonalRight_deriv3 hp hP hδ hD)).sub hM

theorem lowerSourcePair_zero_eq {p L δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 2) (hL : 0 < L)
    (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) :
    lowerSourcePair 0 p δ = adjacentDiagonal p L 0 (1 - δ) (lowerDiagonalMass δ) +
      fourthSourceRow p L 0 (1 - δ) (lowerDiagonalMass δ) (lowerDiagonalMass δ) (lowerDiagonalMass δ) := by
  have hB : δ ∈ Ioo (-(1 / 4) : ℝ) (1 / 4) := ⟨by linarith only [hδ],by linarith only [hD]⟩
  unfold lowerSourcePair
  dsimp only
  rw [lowerLeftCombined_zero_eq hp hP hB,lowerDiagonal_adjacent_source_eq hp hP hL hδ hD,
    lowerDiagonal_fourth_source_eq hp hP hL hδ hD]
  unfold lowerMassResponse
  ring

theorem lowerSourcePair_third_pos {p δ : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hδ : 0 ≤ δ) (hD : δ ≤ 1 / 8) : 0 < lowerSourcePair 3 p δ := by
  let m := lowerDiagonalMass δ
  have hp₀ := zero_lt_one.trans_le hp
  have hm : 0 < m := by unfold m lowerDiagonalMass; linarith only [hD]
  have hM : 0 < p * (p + 1) * m ^ (-p - 2) := by positivity
  have hA := mul_lt_mul_of_pos_left (lowerRightResponseTotal_left_gt hp hP (lowerDiagonalRatio_mem hδ hD)) hM
  have hL := lowerLeftCombined_third_pos hp hP hδ hD
  change 0 < lowerLeftCombined 3 p δ + (p * (p + 1) * m ^ (-p - 2)) *
    lowerRightResponseTotal p (lowerDiagonalRatio δ) -
      (pureZ p - 1) * (8 * (p - 1) * (p * (p + 1) * m ^ (-p - 2)))
  nlinarith only [hA,hL]

end ACS12.GammaMeasure
