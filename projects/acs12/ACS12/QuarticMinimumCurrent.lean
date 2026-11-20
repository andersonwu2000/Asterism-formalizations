import ACS12.QuarticPhysicalCross
import ACS12.HighIncidentRadius
import ACS12.HighIncidentPrice

/-! The same complete minimum cut pays the incident and both crossing contributions. -/
namespace ACS12.Configuration

open Finset HighCurrent
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {p : ℝ} (F : Configuration n p)

theorem radialUnitSource_quartic_current_upper (hn : 2 ≤ n) (hp : 4 ≤ p)
    (o : Fin n) (hMax : ∀ j, F.mass j ≤ F.mass o) (r : Fin n)
    (hMin : ∀ j, (F.radialUnitSource hn o).currentMasses r ≤ (F.radialUnitSource hn o).currentMasses j)
    {e : ℝ} (hFee : ∀ j ≠ r, quarticCrossPrice p ((F.radialUnitSource hn o).shorterHalfAngle r j) ≤ e) :
    let G := F.radialUnitSource hn o
    let q := G.currentMasses r
    let x := 1 / (2 * G.radius) ^ 2
    2 * G.commonCurrent ≤ q * Real.sqrt ((2 * q) ^ (-(2 / p)) - x) + e := by
  let G := F.radialUnitSource hn o
  let q := G.currentMasses r
  have hp₀ : 0 < p := by linarith only [hp]
  have hRow : 2 * G.coefficient * G.radius ^ 2 = 1 := by
    rw [← G.radial_row (G.currentOrder r)]
    exact F.radialUnitSource_radial hn hp₀ o _
  have hInc := G.minimum_incident_radius_upper hp₀ r hMin hRow
  have hCross := F.radialUnitSource_quartic_crossing hn hp o hMax r
  have hSum : (∑ j ∈ univ.erase r, G.currentMasses j / G.currentChord r j ^ p) = 1 := by
    rw [← hRow, ← G.currentReweighted_radial r]
    exact sum_congr rfl (fun j hj => (G.currentReweighted_row_identity (mem_erase.mp hj).1).symm)
  have hPoint :
      (∑ j ∈ univ.erase r, G.currentMasses j / G.currentChord r j ^ p * quarticCrossPrice p (G.shorterHalfAngle r j)) ≤
        ∑ j ∈ univ.erase r, G.currentMasses j / G.currentChord r j ^ p * e :=
    sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hFee j (mem_erase.mp hj).1)
      (div_nonneg (G.mass_pos _).le (Real.rpow_nonneg (G.currentChord_pos (mem_erase.mp hj).1).le _)))
  rw [← sum_mul, hSum, one_mul] at hPoint
  change 2 * G.commonCurrent ≤ q * Real.sqrt ((2 * q) ^ (-(2 / p)) - 1 / (2 * G.radius) ^ 2) + e
  rw [G.commonCurrent_node_decomposition r]
  linarith only [hInc, hCross, hPoint]

theorem radialUnitSource_quartic_ratio_current_upper (hn : 2 ≤ n) (hp : 4 ≤ p)
    (o : Fin n) (hMax : ∀ j, F.mass j ≤ F.mass o) (r : Fin n)
    (hMin : ∀ j, (F.radialUnitSource hn o).currentMasses r ≤ (F.radialUnitSource hn o).currentMasses j)
    (hqSmall : (F.radialUnitSource hn o).currentMasses r ≤ 1 / 5) :
    2 * (F.radialUnitSource hn o).commonCurrent < 629 / 2000 := by
  let G := F.radialUnitSource hn o
  let q := G.currentMasses r
  let x := 1 / (2 * G.radius) ^ 2
  let A := (2 * q) ^ (-(1 / p))
  have hq : 0 < q := G.mass_pos _
  have hA : 0 < A := Real.rpow_pos_of_pos (mul_pos zero_lt_two hq) _
  have hUpper := F.radialUnitSource_quartic_current_upper hn hp o hMax r hMin (e := 1 / 16)
    (fun j hj => by
      change quarticCrossPrice p (G.shorterHalfAngle r j) ≤ 1 / 16
      have hθ := G.shorterHalfAngle_range hj
      by_cases h : G.shorterHalfAngle r j ≤ Real.pi / 4
      · exact (quarticCrossPrice_le hp hθ.1 h).trans (by nlinarith only [sq_nonneg (Real.sin (G.shorterHalfAngle r j) ^ 2)])
      · simp only [quarticCrossPrice, if_neg (not_lt_of_ge (le_of_not_ge h))]
        norm_num)
  have hA₂ : (2 * q) ^ (-(2 / p)) = A ^ 2 := by
    unfold A
    rw [← Real.rpow_mul_natCast (mul_pos zero_lt_two hq).le]
    congr 1
    norm_num
    ring
  have hAupper : Real.sqrt ((2 * q) ^ (-(2 / p)) - x) ≤ A := by
    rw [hA₂]
    have hx : 0 ≤ x := one_div_nonneg.mpr (sq_nonneg (2 * G.radius))
    exact (Real.sqrt_le_sqrt (sub_le_self (A ^ 2) hx)).trans_eq (Real.sqrt_sq hA.le)
  have hPrice := minimumIncidentPrice_exponent_le_four hp hq (show q ≤ 1 / 2 by linarith only [hqSmall])
  have hPrice' := hPrice.trans (minimumIncidentPrice_mass_mono (p := 4) (Q := 1 / 5)
    (by norm_num) hq hqSmall)
  have hExact := minimumIncidentPrice_four_power (q := 1 / 5) (by norm_num)
  have hPositive := minimumIncidentPrice_pos (p := 4) (q := 1 / 5) (by norm_num)
  have hLt : (minimumIncidentPrice 4 (1 / 5)) ^ 4 < (63 / 500 : ℝ) ^ 4 := by
    rw [hExact]
    norm_num
  have hInc := hPrice'.trans_lt ((pow_lt_pow_iff_left₀ hPositive.le (by norm_num)
    (by decide : (4 : ℕ) ≠ 0)).mp hLt)
  change (q / 2) * A < 63 / 500 at hInc
  change 2 * G.commonCurrent ≤ q * Real.sqrt ((2 * q) ^ (-(2 / p)) - x) + 1 / 16 at hUpper
  linarith only [hInc, hUpper, mul_le_mul_of_nonneg_left hAupper hq.le]

end ACS12.Configuration
