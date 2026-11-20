import ACS12.PureZetaEnvelope

/-! The endpoint moment bounds with complete power tails. -/

namespace ACS12.GammaMeasure

open scoped BigOperators

private def prefixLower (j : Fin 35) : ℕ :=
  ![99999999999, 14358729436, 4613818293, 2061731109, 1103783728, 662485684, 430254565, 296038390, 212873191, 158489318, 121366961, 95124526, 76025381, 61779088, 50926574, 42507350, 35870960, 30565884, 26271804, 22757051, 19851162, 17426752, 15387286, 13658672, 12183384, 10916277, 9821581, 8870691, 8040546, 7312408, 6670942, 6103514, 5599650, 5150613, 4749078] j

private theorem prefix_lt (j : Fin 35) :
    (prefixLower j : ℝ) / 100000000000 < (1 + (j.val : ℝ)) ^ (-(14 : ℝ) / 5) := by
  apply fifth_rpow_lower (k := 14) (by positivity) (by positivity)
  fin_cases j <;> norm_num [prefixLower, Matrix.cons_val_zero, Matrix.cons_val_succ]

theorem pureZ_upperEndpoint_lower : (22446558 / 10000000 : ℝ) < pureZ (9 / 5) := by
  have hTail := powerTail_trapezoid_lower (q := 14 / 5) (m := 36) (by norm_num) (by decide)
  norm_num at hTail
  have hP : (157999421 / 100000000000 : ℝ) < (36 : ℝ) ^ (-(9 : ℝ) / 5) :=
    fifth_rpow_lower (k := 9) (by norm_num) (by norm_num) (by norm_num)
  have hQ : (4388871 / 100000000000 : ℝ) < (36 : ℝ) ^ (-(14 : ℝ) / 5) :=
    fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)
  have hS := (powerTail_summable (q := 14 / 5) (by norm_num) 1).sum_add_tsum_nat_add 35
  simp only [neg_div] at hP hQ
  have hT : (∑' j : ℕ, ((1 : ℝ) + ((j + 35 : ℕ) : ℝ)) ^ (-(14 / 5 : ℝ))) = powerTail (14 / 5) 36 := by
    unfold powerTail
    apply tsum_congr
    intro j
    push_cast
    congr 1
    ring
  norm_num only [Nat.cast_one] at hS
  rw [hT, ← Fin.sum_univ_eq_sum_range] at hS
  have hSum : powerTail (14 / 5) 1 = ∑' j : ℕ, (1 + (j : ℝ)) ^ (-(14 / 5 : ℝ)) := by
    simp only [powerTail, Nat.cast_one]
  rw [← hSum] at hS
  have hC := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (by simpa only [neg_div] using (prefix_lt j).le : (prefixLower j : ℝ) / 100000000000 ≤ (1 + (j.val : ℝ)) ^ (-(14 / 5 : ℝ))))
  have hE : (∑ j : Fin 35, (prefixLower j : ℝ) / 100000000000) = (124613141848 / 100000000000 : ℝ) := by
    norm_num [Fin.sum_univ_succ, prefixLower, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [hE] at hC
  unfold pureZ
  norm_num only [show (9 / 5 : ℝ) + 1 = 14 / 5 by norm_num]
  linarith only [hTail, hP, hQ, hS, hC]

theorem pureZ_upperEndpoint_upper : pureZ (9 / 5) < (22449 / 10000 : ℝ) := by
  have hT := powerTail_B2 (q := 14 / 5) (m := 3) (by norm_num) (by decide)
  have hS₁ := powerTail_shift (q := 14 / 5) (by norm_num) 1
  have hS₂ := powerTail_shift (q := 14 / 5) (by norm_num) 2
  norm_num at hT hS₁ hS₂
  have h0 : (2 : ℝ) ^ (-(14 / 5 : ℝ)) < 14358731 / 100000000 := by
    simpa only [neg_div] using fifth_rpow_upper (k := 14) (b := 2) (x := 14358731 / 100000000)
      (by norm_num) (by norm_num) (by norm_num)
  have h1 : (3 : ℝ) ^ (-(9 / 5 : ℝ)) < 13841456 / 100000000 := by
    simpa only [neg_div] using fifth_rpow_upper (k := 9) (b := 3) (x := 13841456 / 100000000)
      (by norm_num) (by norm_num) (by norm_num)
  have h2 : (3 : ℝ) ^ (-(14 / 5 : ℝ)) < 4613820 / 100000000 := by
    simpa only [neg_div] using fifth_rpow_upper (k := 14) (b := 3) (x := 4613820 / 100000000)
      (by norm_num) (by norm_num) (by norm_num)
  have h3 : (3 : ℝ) ^ (-(19 / 5 : ℝ)) < 1537941 / 100000000 := by
    simpa only [neg_div] using fifth_rpow_upper (k := 19) (b := 3) (x := 1537941 / 100000000)
      (by norm_num) (by norm_num) (by norm_num)
  unfold pureZ
  norm_num only [show (9 / 5 : ℝ) + 1 = 14 / 5 by norm_num]
  linarith only [hT, hS₁, hS₂, h0, h1, h2, h3]


theorem powerTail_prefix_split {q : ℝ} (hq : 1 < q) (n : ℕ) :
    powerTail q 1 =
      (∑ j : Fin n, (1 + (j.val : ℝ)) ^ (-q)) + powerTail q (1 + n) := by
  have h := (powerTail_summable hq 1).sum_add_tsum_nat_add n
  simp only [Nat.cast_one] at h
  change (∑ j ∈ Finset.range n, ((1 : ℝ) + (j : ℝ)) ^ (-q)) +
    (∑' j : ℕ, ((1 : ℝ) + ((j + n : ℕ) : ℝ)) ^ (-q)) =
      (∑' j : ℕ, ((1 : ℝ) + (j : ℝ)) ^ (-q)) at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  have hOne : powerTail q 1 = ∑' j : ℕ, ((1 : ℝ) + (j : ℝ)) ^ (-q) := by simp only [powerTail,Nat.cast_one]
  rw [hOne, ← h]
  congr 1
  unfold powerTail
  apply tsum_congr
  intro j
  push_cast
  congr 1
  ring

private theorem prefix_upper (j : Fin 35) :
    (1 + (j.val : ℝ)) ^ (-(14 / 5 : ℝ)) < ((prefixLower j : ℝ) + 2) / 100000000000 := by
  rw [← neg_div]
  apply fifth_rpow_upper (k := 14) (by positivity) (by positivity)
  fin_cases j <;> norm_num [prefixLower, Matrix.cons_val_zero, Matrix.cons_val_succ]

theorem pureZ_upperEndpoint_tight : pureZ (9 / 5) < (2244656562 / 1000000000 : ℝ) := by
  have hTail := powerTail_B2 (q := 14 / 5) (m := 36) (by norm_num) (by decide)
  have hSplit := powerTail_prefix_split (q := 14 / 5) (by norm_num) 35
  norm_num only [Nat.reduceAdd] at hSplit
  have hS := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (prefix_upper j).le)
  have hSum : (∑ j : Fin 35, ((prefixLower j : ℝ) + 2) / 100000000000) =
      (124613141918 / 100000000000 : ℝ) := by
    norm_num [Fin.sum_univ_succ, prefixLower, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [hSum] at hS
  have hA : (36 : ℝ) ^ (-(9 : ℝ) / 5) < 157999423 / 100000000000 :=
    fifth_rpow_upper (k := 9) (by norm_num) (by norm_num) (by norm_num)
  have hB : (36 : ℝ) ^ (-(14 : ℝ) / 5) < 4388873 / 100000000000 :=
    fifth_rpow_upper (k := 14) (by norm_num) (by norm_num) (by norm_num)
  have hC : (36 : ℝ) ^ (-(19 : ℝ) / 5) < 121914 / 100000000000 :=
    fifth_rpow_upper (k := 19) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hTail
  simp only [neg_div] at hA hB hC
  unfold pureZ
  norm_num only [show (9 / 5 : ℝ) + 1 = 14 / 5 by norm_num]
  linarith only [hTail,hSplit,hS,hA,hB,hC]

private def secondPrefix (j : Fin 25) : ℕ :=
  ![10000000000000,717936471873,153793943162,51543277764,22075674583,11041428094,6146493800,3700479898,2365257695,1584893192,1103336019,792704393,584810634,441279207,339510504,265670948,211005657,169810476,138272659,113785262,94529351,79212516,66901248,56911139,48733540] j

private theorem secondPrefix_lt (j : Fin 25) :
    ((secondPrefix j : ℝ) - 1) / 10000000000000 < (1 + (j.val : ℝ)) ^ (-(19 / 5 : ℝ)) := by
  rw [← neg_div]
  apply fifth_rpow_lower (k := 19) (by positivity)
  · fin_cases j <;> norm_num [secondPrefix]
  · fin_cases j <;> norm_num [secondPrefix]

private theorem secondPrefix_upper (j : Fin 25) :
    (1 + (j.val : ℝ)) ^ (-(19 / 5 : ℝ)) < ((secondPrefix j : ℝ) + 1) / 10000000000000 := by
  rw [← neg_div]
  apply fifth_rpow_upper (k := 19) (by positivity) (by positivity)
  fin_cases j <;> norm_num [secondPrefix]

theorem powerTail_second_endpoint :
    (1097510525353 / 1000000000000 : ℝ) < powerTail (19 / 5) 1 ∧
      powerTail (19 / 5) 1 < (1097510576496 / 1000000000000 : ℝ) := by
  have hT := powerTail_B2 (q := 19 / 5) (m := 26) (by norm_num) (by decide)
  have hL := powerTail_trapezoid_lower (q := 19 / 5) (m := 26) (by norm_num) (by decide)
  have hSplit := powerTail_prefix_split (q := 19 / 5) (by norm_num) 25
  norm_num only [Nat.reduceAdd] at hSplit
  have hLow := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (secondPrefix_lt j).le)
  have hHigh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (secondPrefix_upper j).le)
  have hSumL : (∑ j : Fin 25, ((secondPrefix j : ℝ) - 1) / 10000000000000) =
      (10974694393589 / 10000000000000 : ℝ) := by
    norm_num [Fin.sum_univ_succ, secondPrefix]
  have hSumU : (∑ j : Fin 25, ((secondPrefix j : ℝ) + 1) / 10000000000000) =
      (10974694393639 / 10000000000000 : ℝ) := by
    norm_num [Fin.sum_univ_succ, secondPrefix]
  rw [hSumL] at hLow
  rw [hSumU] at hHigh
  have hA : (1091627895 / 10000000000000 : ℝ) < (26 : ℝ) ^ (-(14 : ℝ) / 5) :=
    fifth_rpow_lower (k := 14) (by norm_num) (by norm_num) (by norm_num)
  have hB : (41985687 / 10000000000000 : ℝ) < (26 : ℝ) ^ (-(19 : ℝ) / 5) :=
    fifth_rpow_lower (k := 19) (by norm_num) (by norm_num) (by norm_num)
  have hC : (26 : ℝ) ^ (-(14 : ℝ) / 5) < 1091627897 / 10000000000000 :=
    fifth_rpow_upper (k := 14) (by norm_num) (by norm_num) (by norm_num)
  have hD : (26 : ℝ) ^ (-(19 : ℝ) / 5) < 41985689 / 10000000000000 :=
    fifth_rpow_upper (k := 19) (by norm_num) (by norm_num) (by norm_num)
  have hE : (26 : ℝ) ^ (-(24 : ℝ) / 5) < 1614835 / 10000000000000 :=
    fifth_rpow_upper (k := 24) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hL hT
  simp only [neg_div] at hA hB hC hD hE
  constructor
  · linarith only [hL,hSplit,hLow,hA,hB]
  · linarith only [hT,hSplit,hHigh,hC,hD,hE]

end ACS12.GammaMeasure
