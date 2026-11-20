import ACS12.QuarticCountScalar
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The improvement of the actual incident current at the comparison mass. -/
namespace ACS12.HighCurrent

open Set Real

theorem quarticCount_incident_gain {r q z : ℝ} (hr : r ∈ Icc 0 1) (hq : 0 < q)
    (hqCap : q ≤ 3 / 4) (hz : z ∈ Icc 0 (691 / 2000)) :
    (3 / 4) * (2 / 3 : ℝ) ^ (r / 4) * Real.sqrt (1 - z) -
      q * (2 * q) ^ (-(r / 4)) * Real.sqrt (1 - z) ≥
        (3 / 4) * (903 / 1000) * (809 / 1000) * (3 / 4 - q) := by
  let a := r / 4
  let Q : ℝ := 3 / 4
  let u := q / Q
  let B := (2 / 3 : ℝ) ^ a
  let S := Real.sqrt (1 - z)
  have hQ : 0 < Q := by norm_num [Q]
  have hu : 0 < u := div_pos hq hQ
  have hu₁ : u ≤ 1 := (div_le_one hQ).mpr hqCap
  have ha₀ : 0 ≤ a := div_nonneg hr.1 (by norm_num)
  have ha₁ : a ≤ 1 / 4 := div_le_div_of_nonneg_right hr.2 (by norm_num)
  have hqEq : Q * u = q := by unfold u; field_simp [hQ.ne']
  have hBase : 2 * q = (3 / 2 : ℝ) * u := by
    rw [← hqEq]
    unfold Q
    ring
  have hPow : (3 / 2 : ℝ) ^ (-a) = B := by
    unfold B
    rw [Real.rpow_neg_eq_inv_rpow, show (3 / 2 : ℝ)⁻¹ = 2 / 3 by norm_num]
  have huPow : u ^ (1 - a) = u * u ^ (-a) := by
    rw [sub_eq_add_neg, Real.rpow_add hu, Real.rpow_one]
  have hIncident : q * (2 * q) ^ (-a) = Q * B * u ^ (1 - a) := by
    rw [hBase, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) hu.le, hPow, huPow, ← hqEq]
    ring
  have hTangent := rpow_one_add_le_one_add_mul_self (s := u - 1) (p := 1 - a)
    (by linarith only [hu]) (by linarith only [ha₁]) (by linarith only [ha₀])
  rw [show 1 + (u - 1) = u by ring] at hTangent
  have hGain : (3 / 4) * (1 - u) ≤ 1 - u ^ (1 - a) := by
    have h := mul_le_mul_of_nonneg_right (show (3 / 4 : ℝ) ≤ 1 - a by linarith only [ha₁])
      (sub_nonneg.mpr hu₁)
    linarith only [h,hTangent]
  have hB : (903 / 1000 : ℝ) ≤ B :=
    quarticCount_twoThirds_quarter_lower.le.trans
      (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ha₁)
  have hS : (809 / 1000 : ℝ) ≤ S := by
    have hSq : (809 / 1000 : ℝ) ^ 2 ≤ 1 - z := by linarith only [hz.2]
    unfold S
    exact (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 809 / 1000)).symm.le.trans
      (Real.sqrt_le_sqrt hSq)
  have hCoeff : (903 / 1000 : ℝ) * (809 / 1000) ≤ B * S :=
    mul_le_mul hB hS (by norm_num) ((by norm_num : (0 : ℝ) ≤ 903 / 1000).trans hB)
  have hDiff : Q * (1 - u) = Q - q := by rw [mul_sub, mul_one, hqEq]
  change (3 / 4) * (903 / 1000) * (809 / 1000) * (Q - q) ≤ Q * B * S - q * (2 * q) ^ (-a) * S
  rw [hIncident, ← hDiff]
  calc
    _ = ((903 / 1000 : ℝ) * (809 / 1000)) * Q * ((3 / 4) * (1 - u)) := by ring
    _ ≤ B * S * Q * ((3 / 4) * (1 - u)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCoeff hQ.le)
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hu₁))
    _ ≤ B * S * Q * (1 - u ^ (1 - a)) :=
      mul_le_mul_of_nonneg_left hGain (mul_nonneg (mul_nonneg
        ((by norm_num : (0 : ℝ) ≤ 903 / 1000).trans hB) (Real.sqrt_nonneg _)) hQ.le)
    _ = _ := by ring

end ACS12.HighCurrent
