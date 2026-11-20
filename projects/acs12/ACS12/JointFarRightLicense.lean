import ACS12.ShiftedPowerTail
import ACS12.JointLowerRightSum

/-! Complete right-source third derivative on the middle exponent band. -/
namespace ACS12.GammaMeasure

open Set Finset

theorem farRight_third_lt {p U : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) (hU : U ∈ Icc (1 : ℝ) (7 / 6)) :
    rightSourceSum 3 p U < 1063 / 1000 := by
  let T := p * (p + 1) * (p + 2)
  let q := p + 3
  let x := 1 + U
  let f (j : ℕ) := sourceRightD3 p (1 + (j : ℝ)) U
  have hp₀ := zero_lt_one.trans_le hp
  have hT : 0 < T := by unfold T; positivity
  have hq : 1 < q := by unfold q; linarith only [hp]
  have hx : 2 ≤ x := by unfold x; linarith only [hU.1]
  have hx₁ : 1 ≤ x := one_le_two.trans hx
  have he (j : ℕ) : 1 + (j : ℝ) + U = x + (j : ℝ) := by unfold x; ring
  have hEq (j : ℕ) : f j =
      (T * (-2)) * (x + (j : ℝ)) ^ (-q) +
      (T * q * U) * (x + (j : ℝ)) ^ (-(q + 1)) := by
    unfold f sourceRightD3
    rw [he,show -p - 3 = -q by unfold q; ring,show -p - 4 = -(q + 1) by unfold q; ring]
    unfold T q
    ring
  have hS : Summable f := (((shiftedPowerTail_summable hq hx₁).mul_left (T * (-2))).add
    ((shiftedPowerTail_summable (show 1 < q + 1 by linarith only [hq]) hx₁).mul_left (T * q * U))).congr
      (fun j => (hEq j).symm)
  have hForm (j : ℕ) : f j =
      T * (x + (j : ℝ)) ^ (-q) * (-2 + q * U / (x + (j : ℝ))) := by
    have hj : 0 < x + (j : ℝ) := by positivity
    rw [hEq,show -(q + 1) = -q - 1 by ring,Real.rpow_sub_one hj.ne']
    ring
  have hQu : q * U ≤ 28 / 5 := by
    have h := mul_le_mul (show q ≤ 24 / 5 by unfold q; linarith only [hpP]) hU.2
      (zero_le_one.trans hU.1) (by norm_num : (0 : ℝ) ≤ 24 / 5)
    linarith only [h]
  have hTails : (∑' j : ℕ, f (j + 1)) ≤ 0 := by
    apply tsum_nonpos
    intro j
    rw [hForm]
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    have hj : 3 ≤ x + ((j + 1 : ℕ) : ℝ) := by
      push_cast
      linarith only [hx,Nat.cast_nonneg (α := ℝ) j]
    have hPos : 0 < x + ((j + 1 : ℕ) : ℝ) := by linarith only [hj]
    have hqU : q * U / (x + ((j + 1 : ℕ) : ℝ)) ≤ 2 :=
      (div_le_iff₀ hPos).mpr (by linarith only [hQu,hj])
    linarith only [hqU]
  have hFirst : f 0 ≤ 9576 / 10000 := by
    rw [hForm]
    simp only [Nat.cast_zero,add_zero]
    have hPos : 0 < x := by linarith only [hx]
    have hBracket : -2 + q * U / x ≤ 4 / 5 := by
      have h : q * U / x ≤ 14 / 5 := (div_le_iff₀ hPos).mpr (by linarith only [hQu,hx])
      linarith only [h]
    have hPow : x ^ (-q) ≤ 1 / 16 := by
      calc
        _ ≤ (2 : ℝ) ^ (-q) := Real.rpow_le_rpow_of_nonpos (by norm_num) hx
          (neg_nonpos.mpr (zero_lt_one.trans hq).le)
        _ ≤ (2 : ℝ) ^ (-4 : ℝ) := (Real.rpow_le_rpow_left_iff (by norm_num)).mpr (by unfold q; linarith only [hp])
        _ = _ := by norm_num [Real.rpow_neg,Real.rpow_ofNat]
    have hB : T ≤ 2394 / 125 := by
      have h12 := mul_le_mul hpP (show p + 1 ≤ 14 / 5 by linarith only [hpP]) (by positivity) (by norm_num)
      have h123 := mul_le_mul h12 (show p + 2 ≤ 19 / 5 by linarith only [hpP]) (by positivity) (by norm_num)
      norm_num at h123
      exact h123
    calc
      _ ≤ T * x ^ (-q) * (4 / 5) := mul_le_mul_of_nonneg_left hBracket (by positivity)
      _ ≤ (2394 / 125 : ℝ) * (1 / 16) * (4 / 5) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hB hPow (Real.rpow_nonneg hPos.le _) (by norm_num)) (by norm_num)
      _ = _ := by norm_num
  have h := hS.sum_add_tsum_nat_add 1
  simp only [sum_range_one] at h
  change (∑' j : ℕ, f j) < 1063 / 1000
  rw [← h]
  linarith only [hFirst,hTails]

end ACS12.GammaMeasure
