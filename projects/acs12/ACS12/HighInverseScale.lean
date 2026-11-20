import ACS12.HighPotentialScaling
import ACS12.HighLaplaceDerivative
import ACS12.PressureInverseScale

/-! The actual inverse minimum scale on the high-exponent source law. -/
namespace ACS12.Pressure

open Set MeasureTheory Filter CenteredCircle.AllN
open GammaMeasure

theorem imagePotential_deriv_all {p L t : ℝ} (hp : 0 < p) (hL : 0 < L) (ht : 0 < t) :
    HasDerivAt (imagePotential p L) (-imageSlope p L t) t := by
  have h0 : sourceLaplaceMoment p L 0 = imagePotential p L := by
    funext u
    simp only [sourceLaplaceMoment,imagePotential,pow_zero,mul_one]
  have h := sourceLaplaceMoment_deriv hp hL ht 0
  rw [h0] at h
  simpa only [sourceLaplaceMoment,imageSlope,Nat.zero_add,pow_one] using h


theorem high_imagePotential_strictAnti {p L : ℝ} (hp : 2 ≤ p) (hL : 0 < L) :
    StrictAntiOn (imagePotential p L) (Ioi 0) := by
  intro x hx y hy h
  have hx₀ : 0 < x := hx
  have hy₀ : 0 < y := hy
  have hp₀ := (by linarith only [hp] : 0 < p)
  have hK := imagePotential_pos hp₀ hL hx₀
  have hR : (x / y) ^ 2 < 1 := by
    have hxy := div_lt_one hy₀ |>.mpr h
    simpa only [one_pow] using pow_lt_pow_left₀ hxy (div_nonneg hx₀.le hy₀.le) (by decide : (2 : ℕ) ≠ 0)
  exact (high_imagePotential_scaled_upper hp hL hx₀ h.le).trans_lt (mul_lt_of_lt_one_left hK hR)

theorem high_exists_imagePotential_eq {p L c : ℝ} (hp : 2 ≤ p) (hL : 0 < L) (hc : 0 < c) :
    ∃ t > 0, imagePotential p L t = c := by
  let k := imagePotential p L
  let r := (k 1 / c) ^ (1 / 2 : ℝ)
  let x := min 1 r
  let y := max 1 r
  have hp₀ := (by linarith only [hp] : 0 < p)
  have hK := imagePotential_pos hp₀ hL zero_lt_one
  have hD : 0 < k 1 / c := div_pos hK hc
  have hr : 0 < r := Real.rpow_pos_of_pos hD _
  have hx : 0 < x := lt_min zero_lt_one hr
  have hy : 0 < y := zero_lt_one.trans_le (le_max_left _ _)
  have hPow : r ^ (-(2 : ℝ)) * k 1 = c := by
    unfold r
    rw [← Real.rpow_mul hD.le,show (1 / 2 : ℝ) * (-(2 : ℝ)) = -1 by norm_num,Real.rpow_neg_one,inv_div]
    exact div_mul_cancel₀ _ hK.ne'
  have hL₁ : r ^ (-(2 : ℝ)) * k 1 ≤ k x := by
    have hS := high_imagePotential_scaled_upper hp hL hx (min_le_left 1 r)
    norm_num only [Real.rpow_two] at hS ⊢
    change k 1 ≤ (x / 1) ^ 2 * k x at hS
    rw [div_one] at hS
    have hX : x ^ (-(2 : ℝ)) * k 1 ≤ k x := by
      rw [Real.rpow_neg hx.le,← div_eq_inv_mul]
      exact (div_le_iff₀ (Real.rpow_pos_of_pos hx 2)).mpr (by simpa only [mul_comm,Real.rpow_two] using hS)
    exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx (min_le_right 1 r) (by norm_num : -(2 : ℝ) ≤ 0)) hK.le).trans hX
  have hL₂ : k y ≤ r ^ (-(2 : ℝ)) * k 1 := by
    have hS := high_imagePotential_scaled_upper hp hL zero_lt_one (le_max_left 1 r)
    change k y ≤ (1 / y) ^ 2 * k 1 at hS
    rw [← Real.rpow_two (1 / y)] at hS
    rw [one_div,Real.inv_rpow hy.le,← Real.rpow_neg hy.le] at hS
    exact hS.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hr (le_max_right 1 r) (by norm_num : -(2 : ℝ) ≤ 0)) hK.le)
  rw [hPow] at hL₁ hL₂
  have hxy : x ≤ y := (min_le_left 1 r).trans (le_max_left _ _)
  have hCont : ContinuousOn k (Icc x y) := by
    intro t ht
    exact (imagePotential_deriv_all hp₀ hL (hx.trans_le ht.1)).continuousAt.continuousWithinAt
  obtain ⟨t,ht,hEq⟩ := intermediate_value_Icc' hxy hCont ⟨hL₂,hL₁⟩
  exact ⟨t,hx.trans_le ht.1,hEq⟩

end ACS12.Pressure
