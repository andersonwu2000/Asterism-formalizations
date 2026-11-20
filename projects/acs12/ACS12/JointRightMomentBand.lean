import ACS12.JointRightLogMoments

/-! The three full power-tail bounds in W31. -/
namespace ACS12.GammaMeasure

open Set

noncomputable def rightMoment2Lower (d : ℝ) : ℝ :=
  9751 / 100000 + (835 / 10000) * d + (405 / 10000) * d ^ 2 +
    (94 / 6000) * d ^ 3 + (126 / 24000) * d ^ 4

theorem rightMoment2Lower_le {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    rightMoment2Lower (9 / 5 - p) ≤ powerTail (p + 2) 2 := by
  let d := 9 / 5 - p
  let q : ℝ := 19 / 5
  let a (j : ℕ) := (2 : ℝ) + (j : ℝ)
  let f (k j : ℕ) := a j ^ (-q) * Real.log (a j) ^ k
  have hd : 0 ≤ d := sub_nonneg.mpr hP
  have hq : 1 < q := by norm_num [q]
  have hM (k : ℕ) : HasSum (f k) (powerLogTail q k 2) :=
    (powerLogTail_summable hq k 2 (by decide)).hasSum
  have h₀ := hM 0
  have h₁ := (hM 1).mul_left d
  have h₂ := (hM 2).mul_left (d ^ 2 / 2)
  have h₃ := (hM 3).mul_left (d ^ 3 / 6)
  have h₄ := (hM 4).mul_left (d ^ 4 / 24)
  have hS := (((h₀.add h₁).add h₂).add h₃).add h₄
  have hI (j : ℕ) : f 0 j + d * f 1 j + (d ^ 2 / 2) * f 2 j + (d ^ 3 / 6) * f 3 j +
      (d ^ 4 / 24) * f 4 j ≤ a j ^ (-(p + 2)) := by
    have ha : 1 ≤ a j := (by norm_num : (1 : ℝ) ≤ 2).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
    have ha₀ := zero_lt_one.trans_le ha
    have h := Real.sum_le_exp_of_nonneg (mul_nonneg hd (Real.log_nonneg ha)) 5
    norm_num [Finset.sum_range_succ,Nat.factorial] at h
    have hT := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ha₀.le (-q))
    have hP' : a j ^ (-q) * Real.exp (d * Real.log (a j)) = a j ^ (-(p + 2)) := by
      rw [mul_comm d (Real.log (a j)),← Real.rpow_def_of_pos ha₀,← Real.rpow_add ha₀,show -q + d = -(p + 2) by unfold d q; ring]
    rw [hP'] at hT
    convert hT using 1
    unfold f
    ring
  have hS' : Summable (fun j : ℕ => a j ^ (-(p + 2))) := powerTail_summable (by linarith only [hp]) 2
  have hTop := hS.summable.tsum_le_tsum hI hS'
  rw [hS.tsum_eq] at hTop
  change _ ≤ powerTail (p + 2) 2 at hTop
  have hV : (9751 / 100000 : ℝ) ≤ powerLogTail q 0 2 := by
    rw [powerLogTail_zero]
    have h := powerTail_shift hq 1
    norm_num at h
    rw [show q = (19 / 5 : ℝ) by rfl] at *
    linarith only [h,powerTail_second_endpoint.1]
  obtain ⟨hL₁,hL₂,hL₃,hL₄⟩ := rightLog_endpoint_lower
  have hT₁ := mul_le_mul_of_nonneg_left hL₁.le hd
  have hT₂ := mul_le_mul_of_nonneg_left hL₂.le (show 0 ≤ d ^ 2 / 2 by positivity)
  have hT₃ := mul_le_mul_of_nonneg_left hL₃.le (show 0 ≤ d ^ 3 / 6 by positivity)
  have hT₄ := mul_le_mul_of_nonneg_left hL₄.le (show 0 ≤ d ^ 4 / 24 by positivity)
  change rightMoment2Lower d ≤ _
  unfold rightMoment2Lower
  change powerLogTail q 0 2 + d * powerLogTail q 1 2 + d ^ 2 / 2 * powerLogTail q 2 2 +
    d ^ 3 / 6 * powerLogTail q 3 2 + d ^ 4 / 24 * powerLogTail q 4 2 ≤ powerTail (p + 2) 2 at hTop
  dsimp only [q] at hTop hV
  nlinarith only [hTop,hV,hT₁,hT₂,hT₃,hT₄]

private theorem rightTail_start_le {q : ℝ} (hq : 1 < q) :
    powerTail q 2 < (2 : ℝ) ^ (-q) + (3 : ℝ) ^ (-q) + (4 : ℝ) ^ (-q) +
      (5 : ℝ) ^ (1 - q) / (q - 1) + (5 : ℝ) ^ (-q) / 2 + q / 12 * (5 : ℝ) ^ (-(q + 1)) := by
  have h₂ := powerTail_shift hq 2
  have h₃ := powerTail_shift hq 3
  have h₄ := powerTail_shift hq 4
  have hB := powerTail_B2 hq (m := 5) (by decide)
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at h₂ h₃ h₄ hB
  linarith only [h₂,h₃,h₄,hB]

private theorem rightTail_four_lt : powerTail 4 2 < 824 / 10000 := by
  have h := rightTail_start_le (q := 4) (by norm_num)
  norm_num [Real.rpow_neg] at h
  linarith only [h]

private theorem rightTail_far_lt : powerTail (24 / 5) 2 < 432 / 10000 := by
  have h := rightTail_start_le (q := 24 / 5) (by norm_num)
  norm_num at h
  have h₂ : (2 : ℝ) ^ (-(24 / 5 : ℝ)) < 3589684 / 100000000 := by
    rw [← neg_div]
    exact fifth_rpow_upper (k := 24) (by norm_num) (by norm_num) (by norm_num)
  have h₃ : (3 : ℝ) ^ (-(24 / 5 : ℝ)) < 512648 / 100000000 := by
    rw [← neg_div]
    exact fifth_rpow_upper (k := 24) (by norm_num) (by norm_num) (by norm_num)
  have h₄ : (4 : ℝ) ^ (-(24 / 5 : ℝ)) < 128860 / 100000000 := by
    rw [← neg_div]
    exact fifth_rpow_upper (k := 24) (by norm_num) (by norm_num) (by norm_num)
  have h₅ : (5 : ℝ) ^ (-(19 / 5 : ℝ)) < 220758 / 100000000 := by
    rw [← neg_div]
    exact fifth_rpow_upper (k := 19) (by norm_num) (by norm_num) (by norm_num)
  have h₆ : (5 : ℝ) ^ (-(24 / 5 : ℝ)) < 44153 / 100000000 := by
    rw [← neg_div]
    exact fifth_rpow_upper (k := 24) (by norm_num) (by norm_num) (by norm_num)
  have h₇ : (5 : ℝ) ^ (-(29 / 5 : ℝ)) < 8832 / 100000000 := by
    rw [← neg_div]
    exact fifth_rpow_upper (k := 29) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h₂ h₃ h₄ h₅ h₆ h₇
  linarith only [h,h₂,h₃,h₄,h₅,h₆,h₇]

theorem rightMoment3_le {p : ℝ} (hp : 1 ≤ p) (hP : p ≤ 9 / 5) :
    powerTail (p + 3) 2 ≤ 824 / 10000 - (49 / 1000) * (p - 1) := by
  let t := (5 / 4) * (p - 1)
  let a (j : ℕ) := (2 : ℝ) + (j : ℝ)
  have ht : 0 ≤ t := mul_nonneg (by norm_num) (sub_nonneg.mpr hp)
  have ht₁ : t ≤ 1 := by unfold t; linarith only [hP]
  have hW : 1 - t + t = 1 := by ring
  have hAtom (j : ℕ) : a j ^ (-(p + 3)) ≤
      (1 - t) * a j ^ (-(4 : ℝ)) + t * a j ^ (-(24 / 5 : ℝ)) := by
    have ha : 0 < a j := by unfold a; positivity
    have h := convexOn_exp.2 (show Real.log (a j) * (-4) ∈ Set.univ from Set.mem_univ _)
      (show Real.log (a j) * (-(24 / 5 : ℝ)) ∈ Set.univ from Set.mem_univ _)
      (sub_nonneg.mpr ht₁) ht hW
    simp only [smul_eq_mul] at h
    rw [show (1 - t) * (Real.log (a j) * (-4)) + t * (Real.log (a j) * (-(24 / 5 : ℝ))) =
      Real.log (a j) * (-(p + 3)) by unfold t; ring,← Real.rpow_def_of_pos ha,← Real.rpow_def_of_pos ha,
      ← Real.rpow_def_of_pos ha] at h
    exact h
  have hI := (powerTail_summable (q := 4) (by norm_num) 2).hasSum.mul_left (1 - t)
  have hJ := (powerTail_summable (q := 24 / 5) (by norm_num) 2).hasSum.mul_left t
  have h := (powerTail_summable (q := p + 3) (by linarith only [hp]) 2).tsum_le_tsum hAtom (hI.add hJ).summable
  have hSum : HasSum (fun j : ℕ => (1 - t) * a j ^ (-(4 : ℝ)) + t * a j ^ (-(24 / 5 : ℝ)))
      ((1 - t) * powerTail 4 2 + t * powerTail (24 / 5) 2) := hI.add hJ
  rw [hSum.tsum_eq] at h
  have hB := add_le_add (mul_le_mul_of_nonneg_left rightTail_four_lt.le (sub_nonneg.mpr ht₁))
    (mul_le_mul_of_nonneg_left rightTail_far_lt.le ht)
  change powerTail (p + 3) 2 ≤ _ at h
  apply h.trans (hB.trans_eq ?_)
  unfold t
  ring

theorem rightMoment4_ge {p : ℝ} (hp : 1 ≤ p) :
    (1 / 32 : ℝ) - (216875 / 10000000) * (p - 1) ≤ powerTail (p + 4) 2 := by
  let t := p - 1
  have ht : 0 ≤ t := sub_nonneg.mpr hp
  have hL : Real.log 2 ≤ 694 / 1000 := by linarith only [Real.log_two_lt_d9]
  have hE : (2 : ℝ) ^ (-(p + 4)) = (1 / 32) * Real.exp (-t * Real.log 2) := by
    rw [show -(p + 4) = -5 + -t by unfold t; ring,Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show (2 : ℝ) ^ (-t) = Real.exp (-t * Real.log 2) by rw [Real.rpow_def_of_pos (by norm_num),mul_comm]]
    norm_num [Real.rpow_neg]
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-t * Real.log 2)) (by norm_num : (0 : ℝ) ≤ 1 / 32)
  rw [← hE] at h
  have h' := mul_le_mul_of_nonneg_left hL ht
  have hBound : (1 / 32 : ℝ) - (216875 / 10000000) * t ≤ (2 : ℝ) ^ (-(p + 4)) := by nlinarith only [h,h']
  refine hBound.trans ?_
  have hShift := powerTail_shift (q := p + 4) (by linarith only [hp]) 2
  have hP := powerTail_pos (q := p + 4) (by linarith only [hp]) (m := 3) (by decide)
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at hShift
  linarith only [hShift,hP]

end ACS12.GammaMeasure
