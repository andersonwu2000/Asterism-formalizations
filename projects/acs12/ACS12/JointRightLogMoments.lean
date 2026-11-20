import ACS12.PowerLogTailBounds
import ACS12.PureAdjacentValueData

/-! Directed moments of the complete right-source tail at the exponent endpoint. -/
namespace ACS12.GammaMeasure

private theorem atanhFive_le_log {x : ℝ} (hx : 0 ≤ x) :
    let z := x / (x + 2)
    2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z ^ 7 / 7 + z ^ 9 / 9) ≤ Real.log (1 + x) := by
  let z := x / (x + 2)
  have h := Real.hasSum_log_one_add hx
  have hL := h.summable.sum_le_tsum (Finset.range 5) (fun j _ => by positivity)
  rw [h.tsum_eq] at hL
  norm_num [Finset.sum_range_succ] at hL
  change 2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z ^ 7 / 7 + z ^ 9 / 9) ≤ _
  convert hL using 1
  unfold z
  ring

private noncomputable def atanhFive (x : ℝ) : ℝ :=
  let z := x / (x + 2)
  2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z ^ 7 / 7 + z ^ 9 / 9)

private theorem log_dyadic_lower {x : ℝ} (k : ℕ) (hx : (2 : ℝ) ^ k ≤ x) :
    (k : ℝ) * (6931471803 / 10000000000) + atanhFive (x / (2 : ℝ) ^ k - 1) ≤ Real.log x := by
  have hk : 0 < (2 : ℝ) ^ k := by positivity
  have hx₀ := hk.trans_le hx
  have hR := sub_nonneg.mpr ((one_le_div hk).mpr hx)
  have h := atanhFive_le_log hR
  change atanhFive (x / 2 ^ k - 1) ≤ Real.log (1 + (x / 2 ^ k - 1)) at h
  rw [show 1 + (x / (2 : ℝ) ^ k - 1) = x / (2 : ℝ) ^ k by ring,
    Real.log_div hx₀.ne' hk.ne',Real.log_pow] at h
  have h₂ := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg k)
  linarith only [h,h₂]

private def rightDyadic (j : Fin 24) : ℕ :=
  ![1,1,2,2,2,2,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4] j

private def rightLogLower (j : Fin 24) : ℕ :=
  ![69312,109859,138627,160941,179173,194589,207942,219720,230256,239787,248488,256492,
    263903,270803,277256,283319,289035,294441,299571,304450,309102,313547,317803,321885] j

private def rightPowerLower (j : Fin 24) : ℕ :=
  ![71793647186,15379394315,5154327775,2207567457,1104142808,614649379,370047988,
    236525768,158489318,110333600,79270438,58481062,44127919,33951049,26567093,21100564,
    16981046,13827264,11378525,9452934,7921250,6690123,5691112,4873353] j

set_option maxHeartbeats 1200000 in
private theorem rightLogLower_le (j : Fin 24) :
    (rightLogLower j : ℝ) / 100000 ≤ Real.log (2 + (j.val : ℝ)) := by
  have h : (2 : ℝ) ^ rightDyadic j ≤ 2 + (j.val : ℝ) := by
    fin_cases j <;> norm_num [rightDyadic]
  refine le_trans ?_ (log_dyadic_lower (rightDyadic j) h)
  fin_cases j <;> norm_num [rightDyadic,rightLogLower,atanhFive]

private theorem right_fifth_lower {x b : ℝ} {k : ℕ} (hx : 0 ≤ x) (hb : 0 < b)
    (h : x ^ 5 ≤ (b ^ k)⁻¹) : x ≤ b ^ (-(k : ℝ) / 5) := by
  apply (Real.rpow_le_rpow_iff hx (Real.rpow_nonneg hb.le _) (z := (5 : ℝ)) (by norm_num)).mp
  rw [← Real.rpow_mul hb.le,show -(k : ℝ) / 5 * 5 = -(k : ℝ) by ring,Real.rpow_neg hb.le,
    Real.rpow_natCast]
  exact (by
    convert h using 1
    exact Real.rpow_natCast x 5)

set_option maxHeartbeats 800000 in
private theorem rightPowerLower_le (j : Fin 24) :
    (rightPowerLower j : ℝ) / 1000000000000 ≤ (2 + (j.val : ℝ)) ^ (-(19 / 5 : ℝ)) := by
  rw [← neg_div]
  apply right_fifth_lower (k := 19) (by positivity) (by positivity)
  fin_cases j <;> norm_num [rightPowerLower]

private noncomputable def rightLogPrefix (k : ℕ) : ℝ :=
  ∑ j : Fin 24, (rightPowerLower j : ℝ) / 1000000000000 * ((rightLogLower j : ℝ) / 100000) ^ k

private theorem rightLogPrefix_tail_le (k : ℕ) :
    rightLogPrefix k + powerLogTail (19 / 5) k 26 ≤ powerLogTail (19 / 5) k 2 := by
  have h := (powerLogTail_summable (q := 19 / 5) (by norm_num) k 2 (by decide)).sum_add_tsum_nat_add 24
  have hTail : (∑' j : ℕ, ((2 : ℝ) + ((j + 24 : ℕ) : ℝ)) ^ (-(19 / 5 : ℝ)) *
      Real.log ((2 : ℝ) + ((j + 24 : ℕ) : ℝ)) ^ k) = powerLogTail (19 / 5) k 26 := by
    unfold powerLogTail
    apply tsum_congr
    intro j
    push_cast
    rw [show (2 : ℝ) + ((j : ℝ) + 24) = 26 + j by ring]
  change (∑ j ∈ Finset.range 24, ((2 : ℝ) + (j : ℝ)) ^ (-(19 / 5 : ℝ)) * Real.log (2 + (j : ℝ)) ^ k) + _ =
    powerLogTail (19 / 5) k 2 at h
  norm_num only [Nat.cast_ofNat] at h
  rw [hTail,← Fin.sum_univ_eq_sum_range] at h
  rw [← h]
  apply add_le_add_left
  unfold rightLogPrefix
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul (rightPowerLower_le j) (pow_le_pow_left₀ (by positivity) (rightLogLower_le j) k)
    (by positivity) (Real.rpow_nonneg (by positivity) _)

private theorem rightLogTail_nonneg (k : ℕ) : 0 ≤ powerLogTail (19 / 5) k 26 := by
  unfold powerLogTail
  exact tsum_nonneg fun j => mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (pow_nonneg (Real.log_nonneg (show (1 : ℝ) ≤ ((26 : ℕ) : ℝ) + (j : ℝ) from
      (by norm_num : (1 : ℝ) ≤ ((26 : ℕ) : ℝ)).trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))) _)

set_option maxHeartbeats 1200000 in
theorem rightLog_endpoint_lower :
    (835 / 10000 : ℝ) < powerLogTail (19 / 5) 1 2 ∧
    (81 / 1000 : ℝ) < powerLogTail (19 / 5) 2 2 ∧
    (94 / 1000 : ℝ) < powerLogTail (19 / 5) 3 2 ∧
    (126 / 1000 : ℝ) < powerLogTail (19 / 5) 4 2 := by
  have hLog : (13 / 4 : ℝ) ≤ Real.log 26 := by
    have h := log_dyadic_lower (x := 26) 4 (by norm_num)
    exact (by norm_num [atanhFive] : (13 / 4 : ℝ) ≤ _).trans h
  have h₁ : (1091627 / 10000000000 : ℝ) ≤ (26 : ℝ) ^ (-(14 / 5 : ℝ)) := by
    rw [← neg_div]
    exact right_fifth_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)
  have h₂ : (41985 / 10000000000 : ℝ) ≤ (26 : ℝ) ^ (-(19 / 5 : ℝ)) := by
    rw [← neg_div]
    exact right_fifth_lower (k := 19) (by norm_num) (by norm_num) (by norm_num)
  have hT := (powerLogTail_trapezoid (q := 19 / 5) (by norm_num) (m := 26) (by decide)).1
  norm_num at hT
  have hA := mul_le_mul h₁ (show (13 / 4 : ℝ) / (14 / 5) + 1 / (14 / 5) ^ 2 ≤
      Real.log 26 / (14 / 5) + 1 / (14 / 5) ^ 2 by linarith only [hLog])
    (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  have hB := mul_le_mul h₂ hLog (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  have hT' : (14745 / 100000000 : ℝ) ≤ powerLogTail (19 / 5) 1 26 := by
    nlinarith only [hA,hB,hT]
  have hF₁ : (83369 / 1000000 : ℝ) ≤ rightLogPrefix 1 := by
    norm_num [rightLogPrefix,Fin.sum_univ_succ,rightPowerLower,rightLogLower]
  have hF₂ : (81 / 1000 : ℝ) < rightLogPrefix 2 := by
    norm_num [rightLogPrefix,Fin.sum_univ_succ,rightPowerLower,rightLogLower]
  have hF₃ : (94 / 1000 : ℝ) < rightLogPrefix 3 := by
    norm_num [rightLogPrefix,Fin.sum_univ_succ,rightPowerLower,rightLogLower]
  have hF₄ : (126 / 1000 : ℝ) < rightLogPrefix 4 := by
    norm_num [rightLogPrefix,Fin.sum_univ_succ,rightPowerLower,rightLogLower]
  exact ⟨by linarith only [hF₁,hT',rightLogPrefix_tail_le 1],
    by linarith only [hF₂,rightLogPrefix_tail_le 2,rightLogTail_nonneg 2],
    by linarith only [hF₃,rightLogPrefix_tail_le 3,rightLogTail_nonneg 3],
    by linarith only [hF₄,rightLogPrefix_tail_le 4,rightLogTail_nonneg 4]⟩

end ACS12.GammaMeasure
