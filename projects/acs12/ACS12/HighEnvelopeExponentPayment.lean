import ACS12.HighEnvelopeExponentMotion
import ACS12.HighExponentReserve

/-! The full exponent curvature payment on the admitted containing rectangle. -/
namespace ACS12.Pressure

open Set

theorem highExponentLogSlope_le {c p : ℝ} (hc : 0 ≤ c) (hp : 0 < p) :
    highExponentLogSlope c p ≤ -(2 / 3) := by
  let y := highExponentScale c p
  have hy : 0 ≤ y := by unfold y highExponentScale; positivity
  have hB : 0 < 1 + y / 4 := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hB
  have hEq : 1 - (1 + y / 4)⁻¹ = y / (4 + y) := by
    field_simp [show 1 + y / 4 ≠ 0 by positivity,show 4 + y ≠ 0 by positivity]
    <;> ring
  rw [hEq] at h
  have hLog : Real.log (2 + y / 2) = Real.log 2 + Real.log (1 + y / 4) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hB.ne']
    congr 1
    ring
  have hTerm : 0 ≤ y / (4 + y) := div_nonneg hy (by positivity)
  unfold highExponentLogSlope
  change -Real.log (2 + y / 2) + y / (2 * (4 + y)) ≤ -(2 / 3)
  rw [hLog]
  have hHalf : y / (2 * (4 + y)) = (y / (4 + y)) / 2 := by
    rw [div_div,mul_comm (4 + y) 2]
  rw [hHalf]
  linarith only [h,hTerm,Real.log_two_gt_d9]

theorem highExponentScale_square {c p : ℝ} (hp : 0 < p) :
    highExponentScale c p ^ 2 = c ^ 2 / p := by
  unfold highExponentScale
  rw [mul_pow,← Real.rpow_natCast (p ^ (-(1 / 2 : ℝ))) 2,← Real.rpow_mul hp.le,
    show (-(1 / 2 : ℝ)) * (2 : ℕ) = -1 by norm_num,Real.rpow_neg_one]
  ring

theorem highExponentTail_eq {c p : ℝ} (hc : 0 ≤ c) (hp : 0 < p) :
    highExponentTail c p = (2 + highExponentScale c p / 2) ^ (-p) := by
  have hy : 0 ≤ highExponentScale c p := by unfold highExponentScale; positivity
  unfold highExponentTail highExponentLogTail
  rw [Real.rpow_def_of_pos (by positivity : 0 < 2 + highExponentScale c p / 2)]
  congr 1
  ring

theorem highExponent_second_nonneg {c p : ℝ} (hc : 0 ≤ c) (hCap : c ^ 2 ≤ 33 / 70)
    (hp : 2 ≤ p) (hP : p ≤ 4) :
    0 ≤ highExponentScale c p * (5 - 4 * p) / (16 * p ^ 2) +
      highExponentTail c p * (highExponentLogSlope c p ^ 2 + highExponentLogCurvature c p) := by
  have hp₀ : 0 < p := by linarith only [hp]
  let y := highExponentScale c p
  have hy : 0 ≤ y := by unfold y highExponentScale; positivity
  have hcU : c ≤ (7 / 10 : ℝ) := by nlinarith only [hCap,hc,sq_nonneg (c - 7 / 10)]
  have hySq : y ^ 2 * p = c ^ 2 := by
    rw [highExponentScale_square hp₀]
    exact div_mul_cancel₀ _ hp₀.ne'
  have hyU : y ≤ (1 / 2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hp (sq_nonneg y)
    nlinarith only [h,hySq,hCap,hy]
  have hBase : 0 < 2 + y / 2 := by positivity
  have hBaseU : 2 + y / 2 ≤ (9 / 4 : ℝ) := by linarith only [hyU]
  have hE : (4 / 9 : ℝ) ^ p ≤ highExponentTail c p := by
    rw [highExponentTail_eq hc hp₀]
    change (4 / 9 : ℝ) ^ p ≤ (2 + y / 2) ^ (-p)
    have h := Real.rpow_le_rpow_of_nonpos hBase hBaseU (neg_nonpos.mpr hp₀.le)
    have hEq : (9 / 4 : ℝ) ^ (-p) = (4 / 9 : ℝ) ^ p := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 9 / 4),
        show (9 / 4 : ℝ) = (4 / 9 : ℝ)⁻¹ by norm_num,Real.inv_rpow (by norm_num),inv_inv]
    rwa [hEq] at h
  have hS := highExponentLogSlope_le hc hp₀
  have hS₂ : (4 / 9 : ℝ) ≤ highExponentLogSlope c p ^ 2 := by
    nlinarith only [hS,sq_nonneg (highExponentLogSlope c p + 2 / 3)]
  have hG : 0 ≤ highExponentLogCurvature c p := by
    unfold highExponentLogCurvature
    exact div_nonneg (mul_nonneg hy (by positivity)) (by positivity)
  have hE₀ : 0 ≤ highExponentTail c p := (Real.exp_pos _).le
  have hPositive : (4 / 9 : ℝ) * (4 / 9 : ℝ) ^ p ≤
      highExponentTail c p * (highExponentLogSlope c p ^ 2 + highExponentLogCurvature c p) := by
    have h := mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 4 / 9)
    have h' := mul_le_mul_of_nonneg_left (show (4 / 9 : ℝ) ≤ highExponentLogSlope c p ^ 2 + highExponentLogCurvature c p by linarith only [hS₂,hG]) hE₀
    nlinarith only [h,h']
  have hRatio : highExponentScale c p / p ^ 2 = c / p ^ (5 / 2 : ℝ) := by
    unfold highExponentScale
    rw [show (5 / 2 : ℝ) = (1 / 2) + 2 by norm_num,Real.rpow_add hp₀,Real.rpow_two,Real.rpow_neg hp₀.le]
    ring
  have hL : highExponentScale c p * (5 - 4 * p) / (16 * p ^ 2) =
      -c * (4 * p - 5) / (16 * p ^ (5 / 2 : ℝ)) := by
    have h := congrArg (fun z : ℝ => z * (5 - 4 * p) / 16) hRatio
    convert h using 1 <;> ring
  have hDen : 0 < 16 * p ^ (5 / 2 : ℝ) := by positivity
  have hCoef := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcU (show 0 ≤ 4 * p - 5 by linarith only [hp])) hDen.le
  have hPay := highExponentReserve_payment hp hP
  rw [hL,neg_mul,neg_div]
  linarith only [hPositive,hCoef,hPay]

theorem highExponent_combined_convex {c : ℝ} (hc : 0 ≤ c) (hCap : c ^ 2 ≤ 33 / 70) :
    ConvexOn ℝ (Icc 2 4) (fun p => highExponentLinear c p + highExponentTail c p) := by
  let D (p : ℝ) := highExponentScale c p * (1 / 2 - 5 / (24 * p)) +
    highExponentTail c p * highExponentLogSlope c p
  have hD (p : ℝ) (hp : 0 < p) :
      HasDerivAt (fun q => highExponentLinear c q + highExponentTail c q) (D p) p :=
    (highExponentLinear_deriv hp).add (highExponentTail_deriv hc hp)
  have hD₂ (p : ℝ) (hp : 0 < p) :
      HasDerivAt D (highExponentScale c p * (5 - 4 * p) / (16 * p ^ 2) +
        highExponentTail c p * (highExponentLogSlope c p ^ 2 + highExponentLogCurvature c p)) p :=
    (highExponentLinear_second hp).add (highExponentTail_second hc hp)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) (f' := D)
    (f'' := fun p => highExponentScale c p * (5 - 4 * p) / (16 * p ^ 2) +
      highExponentTail c p * (highExponentLogSlope c p ^ 2 + highExponentLogCurvature c p))
  · intro p hp
    exact (hD p (by linarith only [hp.1])).continuousAt.continuousWithinAt
  · intro p hp
    have hp₂ : 2 ≤ p := (interior_subset hp).1
    exact (hD p (by linarith only [hp₂])).hasDerivWithinAt
  · intro p hp
    have hp₂ : 2 ≤ p := (interior_subset hp).1
    exact (hD₂ p (by linarith only [hp₂])).hasDerivWithinAt
  · intro p hp
    have hp' : p ∈ Icc 2 4 := interior_subset hp
    exact highExponent_second_nonneg hc hCap hp'.1 hp'.2

end ACS12.Pressure
