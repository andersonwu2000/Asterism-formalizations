import ACS12.HighMaximumPrice
import ACS12.HighGammaScaling
import ACS12.HighPhysicalPeriod
import ACS12.HighUnitPressure
import ACS12.HighPotentialScaling
import ACS12.HighIncidentEntrance

/-! Correlated original high-band pressure lower bounds in maximum-row units. -/
namespace ACS12.Pressure

open Set MeasureTheory CenteredCircle.AllN
open GammaMeasure

theorem high_pressure_maximum_normalized_gt {n : ℕ} {p : ℝ} (hn : 4 ≤ n)
    (hp : 2 ≤ p) (hP : p ≤ 4) (F : Configuration n p)
    (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi)) (i : Fin n)
    (hMax : ∀ j, C.source.mass j ≤ C.source.mass i) :
    let S := C.source
    let Q := S.mass i
    let D := Q * imagePotential p S.period Q
    (F.chartRadialScale C * (2 * F.coefficient * F.radius ^ 2) + Q * imageSelf p S.period) / D -
      (11 - p) / 10 < pressureAt p S i / D := by
  let S := C.source
  let Q := S.mass i
  let D := Q * imagePotential p S.period Q
  have hp₀ : 0 < p := by linarith only [hp]
  have hD : 0 < D := mul_pos (S.mass_pos i) (imagePotential_pos hp₀ S.period_pos (S.mass_pos i))
  have hPeriod := high_original_normalized_period_gt_two (by omega) F C i
  have hFee := maximumActualFee_lt_line hp hP hPeriod
  rw [← maximumDebit_normalized S.period_pos (S.mass_pos i)] at hFee
  have hPressure := pressure_maximum_gt (by omega) hp₀ F C C.circular_caps i hMax
  have h := (div_lt_div_iff_of_pos_right hD).mpr hPressure
  rw [sub_div] at h
  change _ - (11 - p) / 10 < pressureAt p S i / D
  change maximumDebit p S.period Q / D < (11 - p) / 10 at hFee
  linarith only [h,hFee]

noncomputable def highUnitCoefficient (p : ℝ) : ℝ :=
  let β := (12 - p) / 16
  2 * β * (1 + β * (2 : ℝ) ^ (-(p + 1)))

theorem high_pressure_unit_normalized_gt {n : ℕ} {p : ℝ} (hp : 2 ≤ p) (hP : p ≤ 4)
    (F : Configuration n p) (C : NormalizedCircleChart F.phase F.mass (2 * Real.pi))
    {Q : ℝ} (hQ : 1 ≤ Q) :
    highUnitCoefficient p * (Q * imagePotential p C.source.period Q) < pressureAt p C.source C.source.root := by
  let S := C.source
  let L := S.period
  let b := S.mass S.neighbor
  let β := (12 - p) / 16
  let d := (2 : ℝ) ^ (-(p + 1))
  let k := imagePotential p L
  have hp₀ : 0 < p := by linarith only [hp]
  have hQ₀ := zero_lt_one.trans_le hQ
  have hK₁ : 0 < k 1 := imagePotential_pos hp₀ S.period_pos zero_lt_one
  have hB := F.highIncident_neighbor_mass_gt hp hP C
  change β < b at hB
  have hβ : 0 < β := by unfold β; linarith only [hP]
  have hb : 0 < b := S.mass_pos _
  have hd : 0 < d := Real.rpow_pos_of_pos (by norm_num) _
  have hCoef : 2 * β * (1 + β * d) ≤ 2 * b * (1 + b * d) := by
    have hFac : 1 + β * d ≤ 1 + b * d := by
      linarith only [mul_le_mul_of_nonneg_right hB.le hd.le]
    have h₁ := mul_le_mul hB.le hFac (by positivity : 0 ≤ 1 + β * d) hb.le
    nlinarith only [h₁]
  have hU := (sourceLaplaceMoment_bounds hp S.period_pos zero_lt_one 0).1
  simp only [sourceLaplaceMoment,pow_zero,mul_one,pow_one,Nat.cast_zero,zero_add,one_mul] at hU
  have hU' : 2 * k 1 ≤ imageSlope p L 1 := by
    simpa only [k,imagePotential,imageSlope,mul_one] using hU
  have hPi := high_pressure_unit_gt hp F C
  change b * imageSlope p L 1 * (1 + b * d) < pressureAt p S S.root at hPi
  have hUK := mul_le_mul_of_nonneg_left hU' (show 0 ≤ b * (1 + b * d) by positivity)
  have hK := high_imagePotential_scaled_upper hp S.period_pos zero_lt_one hQ
  change k Q ≤ (1 / Q) ^ 2 * k 1 at hK
  have hK' : Q * k Q ≤ k 1 := by
    have h := mul_le_mul_of_nonneg_left hK hQ₀.le
    have hEq : Q * ((1 / Q) ^ 2 * k 1) = k 1 / Q := by field_simp [hQ₀.ne']
    rw [hEq] at h
    exact h.trans (div_le_self hK₁.le hQ)
  have hPi' : highUnitCoefficient p * k 1 < pressureAt p S S.root := by
    have h := mul_le_mul_of_nonneg_right hCoef hK₁.le
    unfold highUnitCoefficient
    change 2 * β * (1 + β * d) * k 1 < pressureAt p S S.root
    nlinarith only [h,hUK,hPi]
  exact (mul_le_mul_of_nonneg_left hK' (show 0 ≤ highUnitCoefficient p by unfold highUnitCoefficient; positivity)).trans_lt hPi'

end ACS12.Pressure
