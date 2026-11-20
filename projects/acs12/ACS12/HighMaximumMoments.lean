import ACS12.HighMaximumReference
import ACS12.NativeLiteralRows
import ACS12.JointLogEndpoint

/-! Complete reference moments of the high maximum fee. -/
namespace ACS12.GammaMeasure

open Set Filter MeasureTheory CenteredCircle.AllN
open scoped BigOperators

set_option maxHeartbeats 800000

private theorem borelSquare_geom {x : ℝ} (hx : 0 ≤ x) (hx₁ : x < 1) :
    (∑' j : ℕ, ((j : ℝ) + 1) * x ^ j) = (1 - x)⁻¹ ^ 2 := by
  have h := hasSum_geometric_of_lt_one hx hx₁
  have hS : Summable (fun j : ℕ => ‖x ^ j‖) := by
    simpa only [Real.norm_of_nonneg (pow_nonneg hx _)] using h.summable
  have hP := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hS hS
  have hE (j : ℕ) : (∑ k ∈ Finset.range (j + 1), x ^ k * x ^ (j - k)) = ((j : ℝ) + 1) * x ^ j := by
    calc
      _ = ∑ _k ∈ Finset.range (j + 1), x ^ j := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← pow_add, Nat.add_sub_of_le (by have := Finset.mem_range.mp hk; omega)]
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  simp_rw [hE,h.tsum_eq] at hP
  rw [pow_two]
  exact hP.symm

theorem maximum_boseSquare_moment (r : ℕ) (hr : 2 ≤ r) :
    (∫ s : ℝ in Ioi 0, s ^ r / (Real.exp s - 1) ^ 2) =
      (r.factorial : ℝ) * (powerTail r 1 - powerTail (r + 1) 1) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let x (j : ℕ) := (2 : ℝ) + j
  let f (j : ℕ) (s : ℝ) := ((j : ℝ) + 1) * (s ^ r * Real.exp (-s * x j))
  have hx (j : ℕ) : 0 < x j := by unfold x; positivity
  have hq : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (show 1 < r by omega)
  have hq' : (1 : ℝ) < (r : ℝ) + 1 := by linarith only [hq]
  have hI (j : ℕ) : Integrable (f j) μ :=
    (expMoment_nat_integrable r (hx j)).const_mul ((j : ℝ) + 1)
  have hE (j : ℕ) :
      (∫ s : ℝ, f j s ∂μ) = (r.factorial : ℝ) * (x j ^ (-(r : ℝ)) - x j ^ (-((r : ℝ) + 1))) := by
    change (∫ s : ℝ in Ioi 0, ((j : ℝ) + 1) * (s ^ r * Real.exp (-s * x j))) = _
    rw [integral_const_mul,expMoment_nat_integral r (hx j),Real.rpow_neg (hx j).le,Real.rpow_neg (hx j).le,
      Real.rpow_natCast,show (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) by push_cast; rfl,Real.rpow_natCast,pow_succ]
    unfold x
    field_simp [show (2 : ℝ) + j ≠ 0 by positivity]
    ring
  have hNorm (j : ℕ) : (∫ s : ℝ, ‖f j s‖ ∂μ) = ∫ s : ℝ, f j s ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    unfold f
    exact Real.norm_of_nonneg (by have h : 0 < s := hs; positivity)
  have hSum : Summable (fun j => ∫ s : ℝ, ‖f j s‖ ∂μ) := by
    simp_rw [hNorm,hE]
    exact ((powerTail_summable hq 2).sub (powerTail_summable hq' 2)).mul_left _
  have h := integral_tsum_of_summable_integral_norm hI hSum
  simp_rw [hE] at h
  dsimp only [x] at h
  have hSub := (powerTail_summable hq 2).tsum_sub (powerTail_summable hq' 2)
  norm_num only [Nat.cast_ofNat] at hSub
  rw [tsum_mul_left,hSub] at h
  change (r.factorial : ℝ) * (powerTail r 2 - powerTail ((r : ℝ) + 1) 2) = _ at h
  have h₂ : powerTail r 2 = powerTail r 1 - 1 := by
    simpa only [Nat.reduceAdd,Nat.cast_one,Real.one_rpow] using powerTail_shift hq 1
  have h₂' : powerTail ((r : ℝ) + 1) 2 = powerTail ((r : ℝ) + 1) 1 - 1 := by
    simpa only [Nat.reduceAdd,Nat.cast_one,Real.one_rpow] using powerTail_shift hq' 1
  rw [h₂,h₂',sub_sub_sub_cancel_right] at h
  refine (integral_congr_ae ?_).trans h.symm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs₀ : 0 < s := hs
  let X := Real.exp (-s)
  have hX : 0 < X := Real.exp_pos _
  have hX₁ : X < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs₀)
  have hfE (j : ℕ) : f j s = (s ^ r * X ^ 2) * (((j : ℝ) + 1) * X ^ j) := by
    unfold f x X
    rw [show -s * (2 + (j : ℝ)) = (2 : ℕ) * (-s) + (j : ℝ) * (-s) by norm_num; ring,
      Real.exp_add,Real.exp_nat_mul,Real.exp_nat_mul]
    ring
  simp_rw [hfE]
  rw [tsum_mul_left,borelSquare_geom hX.le hX₁]
  have hY : X * (Real.exp s - 1) = 1 - X := by
    unfold X
    rw [mul_sub,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
  rw [← hY,mul_inv_rev,mul_pow]
  field_simp [hX.ne',(expTail_den_pos hs₀).ne']

private theorem powerTail_two_unit : powerTail 2 1 = Real.pi ^ 2 / 6 := by
  simpa only [pureZ,show (1 : ℝ) + 1 = 2 by norm_num,one_mul] using pureZ_one_eq

private theorem powerTail_five_lower : (103666 / 100000 : ℝ) < powerTail 5 1 := by
  have h := powerTail_prefix_split (q := 5) (by norm_num) 5
  have hT := powerTail_pos (q := 5) (by norm_num) (m := 6) (by decide)
  norm_num [Fin.sum_univ_succ,Real.rpow_neg,Real.rpow_ofNat] at h
  linarith only [h,hT]

theorem maximumFee_first_moment_lt :
    (∫ s : ℝ in Ioi 0, s * Real.exp (-s) * maximumFeeShape s) < 887 / 1000 := by
  have he (s : ℝ) : s * Real.exp (-s) * maximumFeeShape s = s ^ (2 : ℕ) / (Real.exp s - 1) ^ 2 := by
    have h := Real.exp_add (-s) s
    rw [neg_add_cancel,Real.exp_zero] at h
    unfold maximumFeeShape
    calc
      _ = s ^ 2 / (Real.exp s - 1) ^ 2 * (Real.exp (-s) * Real.exp s) := by ring
      _ = _ := by rw [← h,mul_one]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => he s),
    maximum_boseSquare_moment 2 (by decide),show ((2 : ℕ) : ℝ) = 2 by norm_num,powerTail_two_unit]
  norm_num
  have hPi := pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le (by decide : 2 ≠ 0)
  linarith only [hPi,powerTail_three_bounds.1]

theorem maximumFee_second_moment_lt :
    (∫ s : ℝ in Ioi 0, s * Real.exp (-s) * maximumFeeShape s * s ^ 2) < 11 / 10 := by
  have he (s : ℝ) : s * Real.exp (-s) * maximumFeeShape s * s ^ 2 = s ^ (4 : ℕ) / (Real.exp s - 1) ^ 2 := by
    have h := Real.exp_add (-s) s
    rw [neg_add_cancel,Real.exp_zero] at h
    unfold maximumFeeShape
    calc
      _ = s ^ 4 / (Real.exp s - 1) ^ 2 * (Real.exp (-s) * Real.exp s) := by ring
      _ = _ := by rw [← h,mul_one]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s _ => he s),maximum_boseSquare_moment 4 (by decide)]
  norm_num [NativeCells.powerTail_four_eq]
  have hPi := pow_lt_pow_left₀ Real.pi_lt_d6 Real.pi_pos.le (by decide : 4 ≠ 0)
  linarith only [hPi,powerTail_five_lower]

end ACS12.GammaMeasure
