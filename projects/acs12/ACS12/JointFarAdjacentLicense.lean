import ACS12.JointFarAdjacentTaylor
import ACS12.JointLowerSourceIdentity

/-! W38 using the exact complete unit moments of both original streams. -/
namespace ACS12.GammaMeasure

open Set Filter
open scoped Topology

theorem leftSource_unit_values {p : ℝ} (hp : 1 ≤ p) :
    lowerKnownSum 0 p 1 = pureZ p - 1 ∧ lowerKnownSum 1 p 1 = p ∧
      lowerKnownSum 2 p 1 = pureQ p - p * (p + 1) := by
  let b (q : ℝ) (j : ℕ) := ((1 : ℝ) + (j : ℝ)) ^ (-q)
  have hp₀ := zero_lt_one.trans_le hp
  have hB (q : ℝ) (hq : 0 < q) : HasSum (fun j : ℕ => b q j - b q (j + 1)) 1 := by
    have hNonneg (j : ℕ) : 0 ≤ b q j - b q (j + 1) := by
      unfold b
      apply sub_nonneg.mpr
      exact Real.rpow_le_rpow_of_nonpos (by positivity)
        (add_le_add_right (Nat.cast_le.mpr (Nat.le_succ j)) 1) (neg_nonpos.mpr hq.le)
    apply (hasSum_iff_tendsto_nat_of_nonneg hNonneg 1).mpr
    have hL : Tendsto (b q) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hq).comp (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
    have h₀ : b q 0 = 1 := by simp [b]
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hL
    simp only [sub_zero] at h
    apply h.congr
    intro j
    rw [Finset.sum_range_sub',h₀]
  have hq₁ : 1 < p + 1 := by linarith only [hp]
  have hq₂ : 1 < p + 2 := by linarith only [hp]
  have h₂ := (powerTail_summable hq₂ 2).hasSum.mul_left (p * (p + 1))
  refine ⟨?_,?_,?_⟩
  · have h₀ := ((powerTail_summable hq₁ 1).hasSum.mul_left p).sub (hB p hp₀)
    rw [lowerKnownSum_zero_eq]
    have he : (fun j : ℕ => purePeanoB p 1 (1 + (j : ℝ))) =
        fun j => p * b (p + 1) j - (b p j - b p (j + 1)) := by
      funext j
      unfold purePeanoB b
      simp only [one_mul,Nat.cast_add,Nat.cast_one]
      rw [add_assoc (1 : ℝ)]
      ring
    rw [he]
    convert h₀.tsum_eq using 1; simp only [b,Nat.cast_one]
  · have h₁ := (hB (p + 1) (zero_lt_one.trans hq₁)).mul_left p
    have he : lowerKnownSum 1 p 1 = ∑' j : ℕ, p * (b (p + 1) j - b (p + 1) (j + 1)) := by
      unfold lowerKnownSum
      apply tsum_congr
      intro j
      change p * (((1 : ℝ) + j) ^ (-p - 1) - ((1 : ℝ) + j + 1) ^ (-p - 1)) = _
      unfold b
      simp only [Nat.cast_add,Nat.cast_one,show -(p + 1) = -p - 1 by ring]
      rw [add_assoc (1 : ℝ)]
    rw [he,h₁.tsum_eq,mul_one]
  · have he : lowerKnownSum 2 p 1 = p * (p + 1) * powerTail (p + 2) 2 := by
      have ht : (∑' j : ℕ, p * (p + 1) * ((2 : ℝ) + j) ^ (-(p + 2))) =
          p * (p + 1) * powerTail (p + 2) 2 := by simpa only [Nat.cast_ofNat] using h₂.tsum_eq
      rw [← ht]
      unfold lowerKnownSum
      apply tsum_congr
      intro j
      change p * (p + 1) * ((1 : ℝ) + j + 1) ^ (-p - 2) = _
      rw [show (1 : ℝ) + j + 1 = 2 + j by ring,show -p - 2 = -(p + 2) by ring]
    rw [he,powerTail_shift hq₂ 1,pureQ]
    norm_num
    ring

theorem rightSource_unit_values {p : ℝ} (hp : 1 ≤ p) :
    rightSourceSum 1 p 1 = pureQ p - p * (p + 1) ∧
    rightSourceSum 2 p 1 = pureQ p - p * (p + 1) - (pureR p - p * (p + 1) * (p + 2)) := by
  have hq₂ : 1 < p + 2 := by linarith only [hp]
  have hq₃ : 1 < p + 3 := by linarith only [hp]
  obtain ⟨hA,hB⟩ := rightSourceSum_unit_first_two hp
  rw [hA,hB,powerTail_shift hq₂ 1,powerTail_shift hq₃ 1,pureQ,pureR]
  norm_num
  constructor <;> ring

theorem jointFarAdjacent_full_upper {p L : ℝ} (hp : 1 ≤ p) (hpP : p ≤ 9 / 5) (hL : 0 < L) :
    adjacentDiagonal p L 0 (7 / 8) (3 / 4) ≤ jointFarAdjacent p := by
  have hp₂ : p ≤ 2 := hpP.trans (by norm_num)
  obtain ⟨hB₀,hB₁,hB₂⟩ := leftSource_unit_values hp
  obtain ⟨hA₁,hA₂⟩ := rightSource_unit_values hp
  have hA := farRight_taylor hp hpP (U := 7 / 6) (by norm_num)
  have hB := farLeft_taylor hp hpP (δ := 1 / 8) (by norm_num)
  rw [rightSourceSum_zero_one hp hp₂,hA₁,hA₂] at hA
  rw [hB₀,hB₁,hB₂] at hB
  have hC := lowerDiagonal_adjacent_source_eq hp hp₂ hL (δ := 1 / 8) (by norm_num) le_rfl
  norm_num [lowerDiagonalMass,lowerDiagonalRatio,lowerDiagonalKnown,lowerDiagonalRight] at hC
  rw [hC]
  have hScale : (3 / 4 : ℝ) ^ (1 - p) = (4 / 3 : ℝ) ^ (p - 1) := by
    rw [show 1 - p = -(p - 1) by ring,Real.rpow_neg (by norm_num),← Real.inv_rpow (by norm_num)]
    norm_num
  have hR : (7 / 8 : ℝ) ^ (-p) = (8 / 7 : ℝ) ^ p := by
    rw [Real.rpow_neg (by norm_num),← Real.inv_rpow (by norm_num)]
    norm_num
  have hFin : lowerKnownFinite p (1 / 8) = (1 / 8 - 3 * p / 4) * (8 / 7 : ℝ) ^ p := by
    unfold lowerKnownFinite
    rw [show (1 - 1 / 8 : ℝ) = 7 / 8 by norm_num,show 1 - p = -p + 1 by ring,
      Real.rpow_add_one (by norm_num),hR]
    ring
  rw [hScale,hFin]
  have h := mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) (p - 1))
  have hEq : jointFarAdjacent p =
      (4 / 3 : ℝ) ^ (p - 1) * (p + 1 - pureZ p + (pureQ p - p * (p + 1)) * (7 / 6 - 1) +
        (pureQ p - p * (p + 1) - (pureR p - p * (p + 1) * (p + 2))) * (7 / 6 - 1) ^ 2 / 2 +
        (1063 / 1000) * (7 / 6 - 1) ^ 3 / 6) +
      ((1 / 8 - 3 * p / 4) * (8 / 7 : ℝ) ^ p +
        (pureZ p - 1 - p * (1 / 8) + (pureQ p - p * (p + 1)) * (1 / 8) ^ 2 / 2 + (1 / 8 : ℝ) ^ 3 / 4)) := by
    -- The two internal moment abbreviations unfold to these same full tails.
    unfold jointFarAdjacent
    change (4 / 3 : ℝ) ^ (p - 1) * (p + 1 - pureZ p + 13 * (pureQ p - p * (p + 1)) / 72 -
      (pureR p - p * (p + 1) * (p + 2)) / 72 + 1063 / 1296000) +
      pureZ p - 1 - p / 8 + (1 / 8 - 3 * p / 4) * (8 / 7 : ℝ) ^ p +
      (pureQ p - p * (p + 1)) / 128 + 1 / 2048 = _
    ring
  rw [hEq]
  linarith only [h,hB]

end ACS12.GammaMeasure
