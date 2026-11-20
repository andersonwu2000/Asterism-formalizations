import ACS12.HighCrossChord
import ACS12.HighCrossAngularPeak
import ACS12.HighCrossPrice

/-! Every original nonincident crossing edge pays the same complete current-product kernel. -/
namespace ACS12.HighCurrent

set_option backward.isDefEq.respectTransparency false

theorem positive_square_rpow {s : ℝ} (hs : 0 < s) (h : ℝ) :
    (s ^ (2 : ℕ)) ^ h = s ^ (2 * h) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hs.le]
  norm_num only [Nat.cast_ofNat]

theorem crossing_pair_kernel {p D u v : ℝ} (hp : 3 ≤ p) (hD : 0 < D)
    (hu : 0 < u) (hv : 0 < v) (hSide : u + v ≤ Real.pi / 2) :
    Real.cos (u + v) / (D * Real.sin (u + v)) ^ (p + 1) ≤
      4 * crossingCoefficient p /
        ((D * Real.sin u) * (D * Real.sin v)) ^ ((p + 1) / 2) := by
  let h := (p + 1) / 2
  let product := (D * Real.sin u) * (D * Real.sin v)
  have hSum : 0 < u + v := add_pos hu hv
  have hSumPi : u + v < Real.pi := by linarith only [hSide,Real.pi_pos]
  have hSinU := Real.sin_pos_of_pos_of_lt_pi hu (by linarith only [hv,hSumPi])
  have hSinV := Real.sin_pos_of_pos_of_lt_pi hv (by linarith only [hu,hSumPi])
  have hSinSum := Real.sin_pos_of_pos_of_lt_pi hSum hSumPi
  have hCos := Real.cos_pos_of_mem_Ioo
    (show (u + v) / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith only [hSum,hSide,Real.pi_pos])
  have hCosSum := Real.cos_nonneg_of_mem_Icc
    (show u + v ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
      constructor <;> linarith only [hSum,hSide,Real.pi_pos])
  have hProd : 0 < product := mul_pos (mul_pos hD hSinU) (mul_pos hD hSinV)
  have hh : 0 ≤ h := by unfold h; linarith only [hp]
  have hTwice : 2 * h = p + 1 := by unfold h; ring
  have hFour : (4 : ℝ) ^ h = (2 : ℝ) ^ (p + 1) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num,
      positive_square_rpow (by norm_num : (0 : ℝ) < 2),hTwice]
  have hFactor :
      (4 * product * Real.cos ((u + v) / 2) ^ (2 : ℕ)) ^ h =
      (2 : ℝ) ^ (p + 1) * product ^ h * Real.cos ((u + v) / 2) ^ (p + 1) := by
    rw [Real.mul_rpow (mul_nonneg (by norm_num) hProd.le) (sq_nonneg _),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hProd.le,
      hFour,positive_square_rpow hCos,hTwice]
  have hPower := Real.rpow_le_rpow (mul_nonneg (mul_nonneg (by norm_num) hProd.le) (sq_nonneg _))
    (crossing_chord_product_square (D := D) u v) hh
  change (4 * product * Real.cos ((u + v) / 2) ^ (2 : ℕ)) ^ h ≤
    ((D * Real.sin (u + v)) ^ (2 : ℕ)) ^ h at hPower
  rw [hFactor,positive_square_rpow (mul_pos hD hSinSum),hTwice] at hPower
  have hDen : 0 < (2 : ℝ) ^ (p + 1) * product ^ h * Real.cos ((u + v) / 2) ^ (p + 1) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hProd _))
      (Real.rpow_pos_of_pos hCos _)
  have hChord := div_le_div_of_nonneg_left hCosSum hDen hPower
  have hTwoInv : (2 : ℝ) ^ (-p - 1) = ((2 : ℝ) ^ (p + 1))⁻¹ := by
    rw [show -p - 1 = -(p + 1) by ring,Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hLeft :
      Real.cos (u + v) /
        ((2 : ℝ) ^ (p + 1) * product ^ h * Real.cos ((u + v) / 2) ^ (p + 1)) =
      ((2 : ℝ) ^ (-p - 1) / product ^ h) *
        (Real.cos (u + v) / Real.cos ((u + v) / 2) ^ (p + 1)) := by
    rw [hTwoInv]
    field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (p + 1)).ne',
      (Real.rpow_pos_of_pos hProd h).ne',(Real.rpow_pos_of_pos hCos (p + 1)).ne']
    <;> ring
  rw [hLeft] at hChord
  have hAngle := mul_le_mul_of_nonneg_left (crossing_angular_peak hp hSum.le hSide)
    (div_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-p - 1)).le
      (Real.rpow_pos_of_pos hProd h).le)
  have hTwo : (2 : ℝ) ^ (-p - 1) = 4 * (2 : ℝ) ^ (-p - 3) := by
    rw [show -p - 1 = (-p - 3) + 2 by ring,Real.rpow_add (by norm_num : (0 : ℝ) < 2),Real.rpow_two]
    ring
  have hRight :
      ((2 : ℝ) ^ (-p - 1) / product ^ h) *
        ((2 / (p - 1)) * (2 * (p - 1) / (p + 1)) ^ ((p + 1) / 2)) =
      4 * crossingCoefficient p / product ^ h := by
    rw [hTwo]
    unfold crossingCoefficient
    ring
  rw [hRight] at hAngle
  exact hChord.trans hAngle

end ACS12.HighCurrent
