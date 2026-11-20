import ACS12.JointLowerNativeStream

/-! The exact first derivative of the complete moving lower native stream at unit. -/
namespace ACS12.GammaMeasure

open Filter
open scoped Topology

private theorem nativePower_difference_hasSum {p : ℝ} (hp : 0 < p) :
    HasSum (fun j : ℕ => ((1 : ℝ) + (j : ℝ)) ^ (-p) - (1 + ((j + 1 : ℕ) : ℝ)) ^ (-p)) 1 := by
  let b (j : ℕ) := ((1 : ℝ) + (j : ℝ)) ^ (-p)
  have hP (j : ℕ) : 0 ≤ b j - b (j + 1) := by
    unfold b
    exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos (by positivity)
      (add_le_add_right (Nat.cast_le.mpr (Nat.le_succ j)) 1) (neg_nonpos.mpr hp.le))
  apply (hasSum_iff_tendsto_nat_of_nonneg hP 1).mpr
  have hL : Tendsto b atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hp).comp (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have h₀ : b 0 = 1 := by simp [b]
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hL
  simp only [sub_zero] at h
  apply h.congr
  intro j
  rw [Finset.sum_range_sub',h₀]

theorem lowerNativeStream_first_unit {p : ℝ} (hp : 1 ≤ p) :
    lowerNativeStream 1 p 0 =
      2 + (43 / 25) * p + (6 / 25) * p ^ 2 + (2 * p - 3) * pureZ p - (37 / 25) * pureQ p := by
  let b (q : ℝ) (j : ℕ) := ((1 : ℝ) + (j : ℝ)) ^ (-q)
  let d (q : ℝ) (j : ℕ) := ((2 : ℝ) + (j : ℝ)) ^ (-q)
  let T := p * (p + 1)
  let f (j : ℕ) := (2 - 2 * p) * (b p j - b p (j + 1)) +
    (38 / 25) * p ^ 2 * b (p + 1) j + p * ((12 / 25) * p - 3) * d (p + 1) j -
    (19 / 25) * T * b (p + 2) j - (18 / 25) * T * d (p + 2) j
  have hp₀ := zero_lt_one.trans_le hp
  have hq₁ : 1 < p + 1 := by linarith only [hp]
  have hq₂ : 1 < p + 2 := by linarith only [hp]
  have hS (q : ℝ) (hq : 1 < q) : HasSum (b q) (powerTail q 1) := by
    simpa only [b,powerTail,Nat.cast_one] using (powerTail_summable hq 1).hasSum
  have hS' (q : ℝ) (hq : 1 < q) : HasSum (d q) (powerTail q 2) := by
    simpa only [d,Nat.cast_ofNat] using (powerTail_summable hq 2).hasSum
  have hF : HasSum f ((2 - 2 * p) * 1 +
      (38 / 25) * p ^ 2 * powerTail (p + 1) 1 + p * ((12 / 25) * p - 3) * powerTail (p + 1) 2 -
      (19 / 25) * T * powerTail (p + 2) 1 - (18 / 25) * T * powerTail (p + 2) 2) := by
    have h := (((((nativePower_difference_hasSum hp₀).mul_left (2 - 2 * p)).add
      ((hS (p + 1) hq₁).mul_left ((38 / 25) * p ^ 2))).add
      ((hS' (p + 1) hq₁).mul_left (p * ((12 / 25) * p - 3)))).sub
      ((hS (p + 2) hq₂).mul_left ((19 / 25) * T))).sub
      ((hS' (p + 2) hq₂).mul_left ((18 / 25) * T))
    exact h
  have hE (j : ℕ) : lowerNativeSite 1 p (j : ℝ) 0 = f j := by
    let x : ℝ := 1 + j
    let y : ℝ := 2 + j
    have hx : 0 < x := by unfold x; positivity
    have hy : 0 < y := by unfold y; positivity
    have hX (a : ℝ) (ha : 0 < a) : a * a ^ (-p - 2) = a ^ (-p - 1) := by
      rw [mul_comm,← Real.rpow_add_one ha.ne',show -p - 2 + 1 = -p - 1 by ring]
    have hB : 1 + ((j + 1 : ℕ) : ℝ) = y := by unfold y; push_cast; ring
    unfold lowerNativeSite f b d T
    simp only [weightedAffineResponse_first,mul_zero,zero_mul,add_zero,sub_zero,
      show -(p + 1) = -p - 1 by ring,show -p - 1 - 1 = -p - 2 by ring,hB]
    rw [show 1 + (j : ℝ) + 1 = y by unfold y; ring]
    change _ = _
    have hBx : 1 + 2 * (j : ℝ) = 2 * x - 1 := by unfold x; ring
    have hBy : 1 + 2 * (j : ℝ) = 2 * y - 3 := by unfold y; ring
    have hX₀ : x * x ^ (-p - 1) = x ^ (-p) := by
      rw [mul_comm,← Real.rpow_add_one hx.ne',show -p - 1 + 1 = -p by ring]
    have hY₀ : y * y ^ (-p - 1) = y ^ (-p) := by
      rw [mul_comm,← Real.rpow_add_one hy.ne',show -p - 1 + 1 = -p by ring]
    have hX' : (1 + 2 * (j : ℝ)) * x ^ (-p - 2) = 2 * x ^ (-p - 1) - x ^ (-p - 2) := by
      rw [hBx,sub_mul,mul_assoc,hX x hx,one_mul]
    have hY' : (1 + 2 * (j : ℝ)) * y ^ (-p - 2) = 2 * y ^ (-p - 1) - 3 * y ^ (-p - 2) := by
      rw [hBy,sub_mul,mul_assoc,hX y hy]
    have hX₁ : (1 + 2 * (j : ℝ)) * x ^ (-p - 1) = 2 * x ^ (-p) - x ^ (-p - 1) := by
      rw [hBx,sub_mul,mul_assoc,hX₀,one_mul]
    have hY₁ : (1 + 2 * (j : ℝ)) * y ^ (-p - 1) = 2 * y ^ (-p) - 3 * y ^ (-p - 1) := by
      rw [hBy,sub_mul,mul_assoc,hY₀]
    -- Group the moving base factor with its matching power before cancellation.
    calc
      _ = -(63 / 25) * p * x ^ (-p - 1) + ((19 / 25) * p * (p + 1)) *
          ((1 + 2 * (j : ℝ)) * x ^ (-p - 2)) -
          (-2 * x ^ (-p) + p * ((1 + 2 * (j : ℝ)) * x ^ (-p - 1))) +
          (-(12 / 25) * p * y ^ (-p - 1) + ((6 / 25) * p * (p + 1)) *
            ((1 + 2 * (j : ℝ)) * y ^ (-p - 2))) +
          (-2 * y ^ (-p) + p * ((1 + 2 * (j : ℝ)) * y ^ (-p - 1))) := by unfold x y; ring
      _ = _ := by rw [hX',hY',hX₁,hY₁]; unfold x y; ring
  unfold lowerNativeStream
  simp_rw [hE]
  rw [hF.tsum_eq,powerTail_shift hq₁ 1,powerTail_shift hq₂ 1,pureZ,pureQ]
  simp only [T,Nat.cast_one,Real.one_rpow,mul_one]
  ring

end ACS12.GammaMeasure
