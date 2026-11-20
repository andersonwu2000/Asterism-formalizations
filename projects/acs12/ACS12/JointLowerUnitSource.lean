import ACS12.JointFarAdjacentLicense
import ACS12.JointLowerSourceThird

/-! Exact adjacent and fourth-source unit derivatives along the lower diagonal. -/
namespace ACS12.GammaMeasure

private theorem lowerLeftCombined_unit {p : ℝ} (hp : 1 ≤ p) :
    lowerLeftCombined 1 p 0 =
      pureQ p - p * (p + 1) + 2 - 2 * p - (2 : ℝ) ^ (-p) := by
  let T := p * (p + 1)
  let f (j : ℕ) :=
    T * ((2 : ℝ) + (j : ℝ)) ^ (-(p + 2)) - 2 * p * ((2 : ℝ) + (j : ℝ)) ^ (-(p + 1)) +
      3 * p * ((3 : ℝ) + (j : ℝ)) ^ (-(p + 1)) - p * ((1 : ℝ) + (j : ℝ)) ^ (-(p + 1))
  have hq₁ : 1 < p + 1 := by linarith only [hp]
  have hq₂ : 1 < p + 2 := by linarith only [hp]
  have hS (q : ℝ) (m : ℕ) (hq : 1 < q) :
      HasSum (fun j : ℕ => ((m : ℝ) + (j : ℝ)) ^ (-q)) (powerTail q m) :=
    (powerTail_summable hq m).hasSum
  have hF : HasSum f (T * powerTail (p + 2) 2 - 2 * p * powerTail (p + 1) 2 +
      3 * p * powerTail (p + 1) 3 - p * powerTail (p + 1) 1) := by
    have h := ((((hS (p + 2) 2 hq₂).mul_left T).sub ((hS (p + 1) 2 hq₁).mul_left (2 * p))).add
      ((hS (p + 1) 3 hq₁).mul_left (3 * p))).sub ((hS (p + 1) 1 hq₁).mul_left p)
    simpa only [f,Nat.cast_one,Nat.cast_ofNat] using h
  have hS' : lowerLeftPairSum 1 p 0 = ∑' j : ℕ, f j := by
    unfold lowerLeftPairSum
    apply tsum_congr
    intro j
    change p * (p + 1) * (1 - 2 * (0 : ℝ)) * (1 + (j : ℝ) + 1 - 0) ^ (-p - 2) -
      2 * p * (1 + (j : ℝ) + 1 - 0) ^ (-p - 1) + 3 * p * (1 + (j : ℝ) + 2 - 3 * 0) ^ (-p - 1) -
      p * (1 + (j : ℝ)) ^ (-p - 1) = _
    simp only [mul_zero,sub_zero,mul_one,f,T,show -p - 2 = -(p + 2) by ring,show -p - 1 = -(p + 1) by ring]
    rw [show 1 + (j : ℝ) + 1 = 2 + (j : ℝ) by ring,show 1 + (j : ℝ) + 2 = 3 + (j : ℝ) by ring]
  unfold lowerLeftCombined
  change p * (1 - (0 : ℝ)) ^ (-p - 1) - 2 * (p - 1) * (1 - 0) ^ (-p) +
    p * (2 - 3 * 0) ^ (-p - 1) + (p - 1) * (2 - 3 * 0) ^ (-p) + lowerLeftPairSum 1 p 0 = _
  rw [hS',hF.tsum_eq,powerTail_shift hq₁ 2,powerTail_shift hq₁ 1,powerTail_shift hq₂ 1,pureQ]
  simp only [mul_zero,sub_zero,Real.one_rpow,mul_one,Nat.cast_one,Nat.cast_ofNat,T]
  rw [show -(p + 1) = -p - 1 by ring,Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem lowerAdjacent_first_unit {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    lowerDiagonalKnownD1 p 0 + lowerDiagonalRightD1 p 0 = pureQ p - 2 * pureP p - 1 := by
  rw [lowerDiagonalKnownD1,sub_zero,(leftSource_unit_values hp).2.1,lowerDiagonalRightD1,
    lowerDiagonalRatio,lowerDiagonalMass]
  norm_num [lowerKnownFiniteD1,Real.one_rpow]
  rw [rightSourceSum_zero_one hp hp₂,(rightSource_unit_values hp).1,pureP_eq]
  ring

theorem lowerSourcePair_first_unit {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    lowerSourcePair 1 p 0 = 2 * pureQ p - 4 * pureP p - 2 * p - 2 - (2 : ℝ) ^ (-p) := by
  change lowerLeftCombined 1 p 0 + lowerDiagonalRightD1 p 0 -
    (pureZ p - 1) * (2 * (p - 1) * lowerDiagonalMass 0 ^ (-p)) = _
  rw [lowerLeftCombined_unit hp,lowerDiagonalRightD1,lowerDiagonalRatio,lowerDiagonalMass]
  norm_num [Real.one_rpow]
  rw [rightSourceSum_zero_one hp hp₂,(rightSource_unit_values hp).1,pureP_eq]
  ring

end ACS12.GammaMeasure
