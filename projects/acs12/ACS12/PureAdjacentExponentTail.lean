import ACS12.ActiveClipSlope
import ACS12.PureRightExponent
import ACS12.AdjacentEndpointCertificate
import ACS12.PureAdjacentCapConvex

/-! The complete following-tail exponent loss at the common cubic mass. -/

namespace ACS12.GammaMeasure

open CenteredCircle.AllN Set
open scoped BigOperators

noncomputable def atomIndex (i : Fin 5) : ℝ := (i.val : ℝ) + 1

private theorem atomIndex_ge_one (i : Fin 5) : 1 ≤ atomIndex i := by
  unfold atomIndex
  exact le_add_of_nonneg_left (Nat.cast_nonneg _)

noncomputable def upperFollowingValue (u : ℝ) : ℝ :=
  ∑ i : Fin 5, max 0 (upperSignedAtom (atomIndex i) u)

private theorem frozen_sixth_nonpos {p u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hu : 1 / 2 ≤ u) (hu' : u ≤ 7 / 8) :
    pureRight p u (u + 6 * upperCapMass u) ≤ 0 := by
  have hu₀ : 0 < u := by linarith only [hu]
  exact pureRight_nonpos_of_exponent_le hp hP (by norm_num)
    (add_pos_of_pos_of_nonneg hu₀ (mul_nonneg (by norm_num) (upperCapMass_pos hu₀).le))
    (pureRight_sixth_endpoint_neg ⟨hu,hu'⟩).le

private theorem frozen_following_eq {p L u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hu : 1 / 2 ≤ u) (hu' : u ≤ 7 / 8) :
    samplingTail (lawRightClip p L 0 u) u (upperCapMass u) =
      upperCapMass u * ∑ i : Fin 5, max 0 (pureRight p u (upperAtomX (atomIndex i) u)) := by
  let m := upperCapMass u
  let K := lawRightClip p L 0 u
  have hu₀ : 0 < u := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hu
  have hm := upperCapMass_pos hu₀
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hT : 0 < u + 6 * m := by positivity
  have hZero : K (u + 6 * m) = 0 := by
    change max 0 (lawRightTest p L 0 u (u + 6 * m)) = 0
    rw [lawRightTest_zero hp hp₂ hL hT, max_eq_left
      (show pureRight p u (u + 6 * m) ≤ 0 from frozen_sixth_nonpos hp hP hu hu')]
  have hTail (j : ℕ) : K (u + (((j + 5) + 1 : ℕ) : ℝ) * m) = 0 := by
    have hArg : u + 6 * m ≤ u + (((j + 5) + 1 : ℕ) : ℝ) * m := by
      push_cast
      nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hm.le]
    apply le_antisymm _ (le_max_left _ _)
    exact (lawRightClip_antitone hp hp₂ hL hθ hT (hT.trans_le hArg) hArg).trans_eq hZero
  have hQ := lawRightClip_quadratureData (u := u) hp hp₂ hL hθ hu₀
  have hS := summable_tail_shift (hQ.summable (u + m) m (le_add_of_nonneg_right hm.le) hm)
  have h := hS.sum_add_tsum_nat_add 5
  change (∑ j ∈ Finset.range 5, K (u + (((j + 1 : ℕ)) : ℝ) * m)) +
      (∑' j : ℕ, K (u + (((j + 5) + 1 : ℕ) : ℝ) * m)) = _ at h
  simp only [hTail, tsum_zero, add_zero] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  unfold samplingTail
  rw [← h]
  apply congrArg (m * ·)
  apply Finset.sum_congr rfl
  intro i _
  have hx := upperAtomX_pos (zero_le_one.trans (atomIndex_ge_one i)) hu₀
  simp only [Nat.cast_add, Nat.cast_one]
  change max 0 (lawRightTest p L 0 u (upperAtomX (atomIndex i) u)) = _
  rw [lawRightTest_zero hp hp₂ hL hx]

theorem pureCapTail_upper_eq {L u : ℝ} (hL : 0 < L) (hu : 1 / 2 ≤ u) (hu' : u ≤ 7 / 8) :
    samplingTail (lawRightClip (9 / 5) L 0 u) u (adjacentCap (9 / 5) u) =
      ∑ i : Fin 5, max 0 (upperSignedAtom (atomIndex i) u) := by
  have hu₀ : 0 < u := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hu
  rw [← upperCapMass_eq, frozen_following_eq (by norm_num) le_rfl hL hu hu', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_max_of_nonneg _ _ (upperCapMass_pos hu₀).le, mul_zero, upperSignedAtom]

private theorem log_first_frozen_lt {u : ℝ} (hu : 0 < u) (hu' : u ≤ 7 / 8) :
    Real.log (upperAtomX 1 u) < 13 / 25 := by
  have hS := pow_le_pow_left₀ hu.le hu' 2
  have hm : upperCapMass u ≤ 161 / 200 := by
    unfold upperCapMass
    have hT : 5 / 7 + (2304 / 8575) * u ^ 2 ≤ (23 / 25 : ℝ) := by linarith only [hS]
    exact (mul_le_mul hu' hT (by positivity) (by norm_num)).trans_eq (by norm_num)
  have hx := upperAtomX_pos zero_le_one hu
  have hx' : upperAtomX 1 u ≤ 42 / 25 := by unfold upperAtomX; linarith only [hm, hu']
  have h := Real.log_div_le_sum_range_add (x := 17 / 67) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  exact (Real.log_le_log hx hx').trans_lt (by linarith only [h])

theorem pureCapTail_exponent_le {p L u : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5)
    (hL : 0 < L) (hu : 1 / 2 ≤ u) (hu' : u ≤ 7 / 8) :
    samplingTail (lawRightClip p L 0 u) u (adjacentCap p u) ≤
      samplingTail (lawRightClip (9 / 5) L 0 u) u (adjacentCap (9 / 5) u) +
        (13 / 1875) * u * (9 / 5 - p) := by
  let m := upperCapMass u
  let g (q : ℝ) (i : Fin 5) := max 0 (pureRight q u (upperAtomX (atomIndex i) u))
  let c (i : Fin 5) : ℝ := if i = 0 then 0 else 1 / 600
  have hu₀ : 0 < u := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hu
  have hm := upperCapMass_pos hu₀
  have hp₂ := hP.trans (by norm_num : (9 / 5 : ℝ) ≤ 2)
  have hθ : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hM : m ≤ adjacentCap p u := by
    rw [show m = adjacentCap (9 / 5) u from upperCapMass_eq u, adjacentCap_eq_ratio, adjacentCap_eq_ratio]
    exact mul_le_mul_of_nonneg_left ((adjacentRatio_antitone u) hP) hu₀.le
  have hStep (i : Fin 5) : g p i ≤ g (9 / 5) i + c i * (9 / 5 - p) := by
    let x := upperAtomX (atomIndex i) u
    have hx := upperAtomX_pos (zero_le_one.trans (atomIndex_ge_one i)) hu₀
    apply ACS12.max_zero_le_add_of_activeSlope hP (show 0 ≤ c i by dsimp only [c]; split <;> norm_num)
      (fun _ => pureRight_exponent_deriv hx)
    intro q hq hA
    have hq₁ := hp.trans hq.1
    have hq₀ := zero_lt_one.trans_le hq₁
    by_cases hI : i = 0
    · have hX : x = upperAtomX 1 u := by simp [x, hI, atomIndex]
      have hLog : Real.log x ≤ 1 / q := by
        rw [hX]
        have hInv := one_div_le_one_div_of_le hq₀ hq.2
        linarith only [hInv, log_first_frozen_lt hu₀ hu']
      simpa only [c, hI, if_true, neg_zero] using (pureRightExponentD_pos_of_log_le hq₀ hx hLog hA).le
    · simpa only [c, hI, if_false] using (pureRightExponentD_gt_neg hq₁ hq.2 hu₀ hu' hx hA).le
  have hQd := lawRightClip_quadratureData (u := u) hp hp₂ hL hθ hu₀
  have hTail := hQd.tail_anti u le_rfl hm (adjacentCap_pos hP hu₀) hM
  rw [frozen_following_eq hp hP hL hu hu'] at hTail
  rw [← upperCapMass_eq, frozen_following_eq (by norm_num) le_rfl hL hu hu']
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hStep i)
  have hC : (∑ i : Fin 5, c i) = 4 / 600 := by norm_num [c, Fin.sum_univ_succ]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hC] at hSum
  have hB : m ≤ (26 / 25) * u := by
    rw [show m = adjacentCap (9 / 5) u from upperCapMass_eq u, adjacentCap_eq_ratio]
    have hU := pow_le_pow_left₀ hu₀.le hu' 2
    have hA : adjacentRatio u (9 / 5) ≤ 26 / 25 := by unfold adjacentRatio; linarith only [hU]
    simpa only [mul_comm u] using mul_le_mul_of_nonneg_left hA hu₀.le
  have hE := mul_le_mul_of_nonneg_left hSum hm.le
  have hF := mul_le_mul_of_nonneg_right hB (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 600) (sub_nonneg.mpr hP))
  change samplingTail (lawRightClip p L 0 u) u (adjacentCap p u) ≤ m * ∑ i : Fin 5, g p i at hTail
  change _ ≤ m * (∑ i : Fin 5, g (9 / 5) i) + _
  nlinarith only [hTail, hE, hF]

end ACS12.GammaMeasure
