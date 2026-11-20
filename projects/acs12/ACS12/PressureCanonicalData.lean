import ACS12.PressureCurvature

/-! Independent complete exponential guards for the canonical pressure value. -/
namespace ACS12.Pressure

noncomputable def canonicalV : ℝ := 111 / 80
noncomputable def canonicalE₀ : ℝ := Real.exp (111 / 280)
noncomputable def canonicalA₀ : ℝ :=
  (9 / 5) * Real.exp (37 / 30) + (14 / 5) * Real.exp (999 / 560) -
    Real.exp (111 / 40) - 92 / 5

noncomputable def canonicalP (v : ℝ) : ℝ := Real.exp (-(2 / 7) * (111 / 40 - v))

noncomputable def canonicalB (v : ℝ) : ℝ :=
  canonicalA₀ + (9 / 5) * Real.exp ((4 / 9) * (111 / 40 - 2 * v)) +
    (14 / 5) * Real.exp ((9 / 14) * (111 / 40 - 2 * v)) -
      Real.exp (111 / 40 - 2 * v) + (56 / 5) * canonicalP v

theorem canonicalA₀_gt : (-115917 / 10000 : ℝ) < canonicalA₀ := by
  have h₁ := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 37 / 30) 10
  have h₂ := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 999 / 560) 12
  norm_num [Finset.sum_range_succ,Nat.factorial] at h₁ h₂
  unfold canonicalA₀
  linarith only [h₁,h₂,exp_pressure_cap_lt]

theorem canonicalA₀_gt_coarse : (-58 / 5 : ℝ) < canonicalA₀ := by
  exact (by norm_num : (-58 / 5 : ℝ) < -115917 / 10000).trans canonicalA₀_gt

theorem canonicalE₀_lt : canonicalE₀ < 10000 / 6727 := by
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 111 / 280) (by norm_num : (111 / 280 : ℝ) ≤ 1)
    (n := 10) (by decide)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  unfold canonicalE₀
  linarith only [h]

theorem canonicalE₀_lt_coarse : canonicalE₀ < 149 / 100 :=
  canonicalE₀_lt.trans (by norm_num)

theorem canonicalP_pos (v : ℝ) : 0 < canonicalP v := Real.exp_pos _

theorem canonicalP_zero_le_one : canonicalP 0 ≤ 1 := by
  unfold canonicalP
  exact Real.exp_le_one_iff.mpr (by norm_num)

theorem canonicalP_far_gt : (6727 / 10000 : ℝ) < canonicalP canonicalV := by
  have h : canonicalP canonicalV = canonicalE₀⁻¹ := by
    unfold canonicalP canonicalV canonicalE₀
    rw [show -(2 / 7 : ℝ) * (111 / 40 - 111 / 80) = -(111 / 280) by norm_num,Real.exp_neg]
  rw [h,← one_div]
  apply (lt_div_iff₀ (Real.exp_pos _ : 0 < canonicalE₀)).mpr
  change (6727 / 10000 : ℝ) * canonicalE₀ < 1
  linarith only [mul_lt_mul_of_pos_left canonicalE₀_lt (by norm_num : (0 : ℝ) < 6727 / 10000)]

theorem canonicalB_far_gt : (-229 / 500 : ℝ) < canonicalB canonicalV := by
  unfold canonicalB
  have h : (111 / 40 : ℝ) - 2 * canonicalV = 0 := by norm_num [canonicalV]
  rw [h]
  simp only [mul_zero,Real.exp_zero,mul_one]
  linarith only [canonicalA₀_gt,canonicalP_far_gt]

theorem canonicalB_zero_gt : (147 / 625 : ℝ) < canonicalB 0 := by
  have hE := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 111 / 140) (by norm_num : (111 / 140 : ℝ) ≤ 1)
    (n := 12) (by decide)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hE
  have hP : (100 / 221 : ℝ) < canonicalP 0 := by
    rw [canonicalP,sub_zero,show -(2 / 7 : ℝ) * (111 / 40) = -(111 / 140) by norm_num,
      Real.exp_neg,← one_div]
    apply (lt_div_iff₀ (Real.exp_pos _)).mpr
    linarith only [hE]
  have h : canonicalB 0 = 2 * canonicalA₀ + 92 / 5 + (56 / 5) * canonicalP 0 := by
    unfold canonicalB canonicalA₀
    rw [mul_zero,sub_zero,show (4 / 9 : ℝ) * (111 / 40) = 37 / 30 by norm_num,
      show (9 / 14 : ℝ) * (111 / 40) = 999 / 560 by norm_num]
    ring
  rw [h]
  linarith only [canonicalA₀_gt,hP]

theorem exp_canonicalCap_bounds : (16 : ℝ) < Real.exp (111 / 40) ∧ Real.exp (111 / 40) < 401 / 25 := by
  exact ⟨(Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 16)).mp pressure_log16_lt_cap,
    exp_pressure_cap_lt.trans (by norm_num)⟩

end ACS12.Pressure
