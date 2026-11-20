import ACS12.QuarticMinimumCurrent

/-! The radius-dependent crossing tariff is paid by each actual radial atom. -/
namespace ACS12.Configuration

open Finset HighCurrent
set_option backward.isDefEq.respectTransparency false

private theorem quartic_minimum_angle_lower {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 4 ≤ p) (o : Fin n) (r j : Fin n) (hj : j ≠ r)
    (hMin : ∀ j, (F.radialUnitSource hn o).currentMasses r ≤ (F.radialUnitSource hn o).currentMasses j) :
    let G := F.radialUnitSource hn o
    let q := G.currentMasses r
    let x := 1 / (2 * G.radius) ^ 2
    (x * (2 * q) ^ (2 / p)) ^ 2 ≤ 2 * Real.sin (G.shorterHalfAngle r j) ^ 4 := by
  let G := F.radialUnitSource hn o
  let q := G.currentMasses r
  let D := 2 * G.radius
  let x := 1 / D ^ 2
  have hD : 0 < D := mul_pos zero_lt_two G.radius_pos
  have hq : 0 < q := G.mass_pos _
  have hq2 : 0 < 2 * q := mul_pos zero_lt_two hq
  have hp₀ : 0 < p := by linarith only [hp]
  have hChord := F.radialUnitSource_upper_chord hn hp₀ o (G.currentOrder r) (G.currentOrder j)
    (G.currentOrder.injective.ne hj)
  change G.currentMasses j ≤ G.currentChord r j ^ p at hChord
  have hqD := (hMin j).trans hChord
  have hP := Real.rpow_le_rpow hq.le hqD (by positivity : 0 ≤ 4 / p)
  rw [← Real.rpow_mul (G.currentChord_pos hj).le,
    show p * (4 / p) = 4 by field_simp [hp₀.ne'], Real.rpow_ofNat] at hP
  have hPow : x ^ 2 * G.currentChord r j ^ 4 = Real.sin (G.shorterHalfAngle r j) ^ 4 := by
    rw [G.shorterHalfAngle_chord hj]
    change (1 / D ^ 2) ^ 2 * (D * Real.sin (G.shorterHalfAngle r j)) ^ 4 = _
    field_simp [hD.ne']
  have hIn := mul_le_mul_of_nonneg_left hP (sq_nonneg x)
  rw [hPow] at hIn
  have hZsq : (x * (2 * q) ^ (2 / p)) ^ 2 = (2 : ℝ) ^ (4 / p) * (x ^ 2 * q ^ (4 / p)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hq2.le, show (2 / p) * (2 : ℕ) = 4 / p by push_cast; ring,
      Real.mul_rpow (by norm_num) hq.le]
    ring
  have hT : (2 : ℝ) ^ (4 / p) ≤ 2 := by
    have h := (div_le_one hp₀).mpr hp
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h
  change (x * (2 * q) ^ (2 / p)) ^ 2 ≤ _
  rw [hZsq]
  exact mul_le_mul hT hIn (by positivity) (by norm_num)

theorem radialUnitSource_quartic_count_upper {n : ℕ} {p : ℝ} (F : Configuration n p)
    (hn : 2 ≤ n) (hp : 4 ≤ p) (o : Fin n) (hMax : ∀ j, F.mass j ≤ F.mass o) (r : Fin n)
    (hMin : ∀ j, (F.radialUnitSource hn o).currentMasses r ≤ (F.radialUnitSource hn o).currentMasses j)
    (hz : let G := F.radialUnitSource hn o
      (1 / (2 * G.radius) ^ 2) * (2 * G.currentMasses r) ^ (2 / p) ≤ 691 / 2000) :
    let G := F.radialUnitSource hn o
    let q := G.currentMasses r
    let z := (1 / (2 * G.radius) ^ 2) * (2 * q) ^ (2 / p)
    2 * G.commonCurrent ≤ q * (2 * q) ^ (-(1 / p)) * Real.sqrt (1 - z) + (1 / 16 - 5 * z ^ 2 / 64) := by
  let G := F.radialUnitSource hn o
  let q := G.currentMasses r
  let x := 1 / (2 * G.radius) ^ 2
  let z := x * (2 * q) ^ (2 / p)
  let a := (2 * q) ^ (-(1 / p))
  have hx : 0 < x := one_div_pos.mpr (sq_pos_of_pos (mul_pos zero_lt_two G.radius_pos))
  have hq : 0 < q := G.mass_pos _
  have hq2 : 0 < 2 * q := mul_pos zero_lt_two hq
  have ha : 0 < a := Real.rpow_pos_of_pos hq2 _
  have hz₀ : 0 ≤ z := mul_nonneg hx.le (Real.rpow_nonneg hq2.le _)
  have hz' : z ≤ 691 / 2000 := hz
  have hFee (j : Fin n) (hj : j ≠ r) :
      quarticCrossPrice p (G.shorterHalfAngle r j) ≤ 1 / 16 - 5 * z ^ 2 / 64 := by
    by_cases h : G.shorterHalfAngle r j ≤ Real.pi / 4
    · have hP := quarticCrossPrice_le hp (G.shorterHalfAngle_range hj).1 h
      have hE := quartic_minimum_angle_lower F hn hp o r j hj hMin
      change z ^ 2 ≤ 2 * Real.sin (G.shorterHalfAngle r j) ^ 4 at hE
      linarith only [hP, hE]
    · rw [quarticCrossPrice, if_neg (not_lt_of_ge (le_of_not_ge h))]
      have hQ := pow_le_pow_left₀ hz₀ hz' 2
      linarith only [hQ]
  have hUpper := F.radialUnitSource_quartic_current_upper hn hp o hMax r hMin hFee
  change 2 * G.commonCurrent ≤ q * Real.sqrt ((2 * q) ^ (-(2 / p)) - x) + (1 / 16 - 5 * z ^ 2 / 64) at hUpper
  have hLift : (2 * q) ^ (-(2 / p)) = a ^ 2 := by
    dsimp only [a]
    rw [← Real.rpow_mul_natCast hq2.le]
    congr 1
    push_cast
    ring
  have hInv : (2 * q) ^ (-(2 / p)) * (2 * q) ^ (2 / p) = 1 := by
    rw [← Real.rpow_add hq2, neg_add_cancel, Real.rpow_zero]
  have hPay : (2 * q) ^ (-(2 / p)) - x = a ^ 2 * (1 - z) := by
    rw [← hLift]
    dsimp only [z]
    have hxEq := congrArg (x * ·) hInv
    linarith only [hxEq]
  rw [hPay, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le] at hUpper
  change 2 * G.commonCurrent ≤ q * a * Real.sqrt (1 - z) + _
  linarith only [hUpper]

end ACS12.Configuration
